// Copyright 2019 Intel Corporation. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::os::unix::io::AsRawFd;
use std::sync::atomic::AtomicBool;
use std::sync::{Arc, Barrier, LazyLock, Mutex, RwLock};
use std::{io, result};

use event_monitor::event;
use log::{debug, error, info, warn};
use seccompiler::SeccompAction;
use serde::{Deserialize, Serialize};
use serde_with::{Bytes, serde_as};
use vhost::vhost_user::message::{
    VhostUserMMap, VhostUserMMapFlags, VhostUserProtocolFeatures, VhostUserVirtioFeatures,
};
use vhost::vhost_user::{
    FrontendReqHandler, HandlerResult, VhostUserFrontend, VhostUserFrontendReqHandler,
};
use vm_device::UserspaceMapping;
use vm_memory::{Address, ByteValued};
use vm_migration::protocol::MemoryRangeTable;
use vm_migration::{Migratable, MigratableError, Pausable, Snapshot, Snapshottable, Transportable};
use vmm_sys_util::eventfd::EventFd;

use super::vu_common_ctrl::VhostUserHandle;
use super::{DEFAULT_VIRTIO_FEATURES, Error, Result};
use crate::device::ActivationContext;
use crate::seccomp_filters::Thread;
use crate::vhost_user::{VhostUserCommon, VhostUserState};
use crate::{
    ActivateError, ActivateResult, GuestRegion, VIRTIO_F_ACCESS_PLATFORM, VirtioCommon,
    VirtioDevice, VirtioDeviceType, VirtioSharedMemoryList,
};

const NUM_QUEUE_OFFSET: u16 = 1;
const DEFAULT_QUEUE_NUMBER: u16 = 2;
const VIRTIO_FS_SHMCAP_ID_CACHE: u8 = 0;

pub type State = VhostUserState<VirtioFsConfig>;

#[derive(Clone, Copy)]
struct DaxWindowEntry {
    gpa: u64,
    len: u64,
    hva: u64,
}

static DAX_WINDOWS: LazyLock<RwLock<Vec<DaxWindowEntry>>> = LazyLock::new(|| RwLock::new(Vec::new()));

fn register_dax_window(gpa: u64, len: u64, hva: u64) {
    let mut windows = DAX_WINDOWS.write().unwrap();
    if let Some(entry) = windows.iter_mut().find(|w| w.hva == hva) {
        entry.gpa = gpa;
        entry.len = len;
    } else {
        windows.push(DaxWindowEntry { gpa, len, hva });
    }
}

fn unregister_dax_window(hva: u64) {
    DAX_WINDOWS.write().unwrap().retain(|w| w.hva != hva);
}

/// Attempt to recover from a synchronous `KVM_EXIT_MEMORY_FAULT` inside an active virtio-fs DAX
/// shared-memory window (for example, if a guest thread races with an external host truncation
/// before `virtiofsd`'s `inotify` zero-remap finishes) by atomically replacing the faulting page
/// range with anonymous zero-filled pages.
pub fn try_zero_fill_dax_fault(gpa: u64, size: u64) -> bool {
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) }.max(4096) as u64;
    let page_mask = !(page_size - 1);
    let fault_len = size.max(page_size);

    let target = {
        let windows = DAX_WINDOWS.read().unwrap();
        windows.iter().copied().find(|w| {
            gpa >= w.gpa
                && gpa
                    .checked_sub(w.gpa)
                    .is_some_and(|off| off < w.len)
        })
    };
    let Some(win) = target else {
        return false;
    };

    let aligned_gpa = (gpa & page_mask).max(win.gpa);
    let win_end = win.gpa.saturating_add(win.len);
    let fault_end = gpa
        .saturating_add(fault_len)
        .saturating_add(page_size - 1)
        & page_mask;
    let map_end = fault_end.min(win_end);
    if map_end <= aligned_gpa {
        return false;
    }
    let map_len = (map_end - aligned_gpa) as usize;
    let map_hva = win.hva + (aligned_gpa - win.gpa);

    // SAFETY: `[map_hva, map_hva + map_len)` lies strictly within the reserved DAX `MmapRegion`
    // and is page-aligned.
    let ret = unsafe {
        libc::mmap(
            map_hva as *mut libc::c_void,
            map_len,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_ANONYMOUS | libc::MAP_PRIVATE | libc::MAP_FIXED,
            -1,
            0,
        )
    };
    if ret == libc::MAP_FAILED {
        error!(
            "Failed to zero-map faulting virtio-fs DAX range gpa={aligned_gpa:#x} len={map_len:#x}: {}",
            io::Error::last_os_error()
        );
        return false;
    }
    warn!(
        "Recovered synchronous KVM memory fault in virtio-fs DAX window at gpa={gpa:#x} (zero-mapped {map_len} bytes)"
    );
    true
}

/// Translate `[gpa, gpa + len)` within an active virtio-fs DAX window to a host pointer if covered.
pub fn translate_dax_gpa(gpa: u64, len: usize) -> Option<*mut u8> {
    let windows = DAX_WINDOWS.read().unwrap();
    for w in windows.iter() {
        if gpa >= w.gpa {
            let off = gpa - w.gpa;
            if off.checked_add(len as u64).is_some_and(|end| end <= w.len) {
                return Some((w.hva + off) as *mut u8);
            }
        }
    }
    None
}

struct BackendReqHandler {
    cache_size: u64,
    mmap_cache_addr: u64,
}

impl BackendReqHandler {
    #[inline]
    fn is_req_valid(&self, offset: u64, len: u64) -> bool {
        match offset.checked_add(len) {
            Some(end) => offset < self.cache_size && end <= self.cache_size,
            None => false,
        }
    }
}

impl VhostUserFrontendReqHandler for BackendReqHandler {
    fn handle_config_change(&self) -> HandlerResult<u64> {
        debug!("virtio-fs handle_config_change");
        Ok(0)
    }

    fn shmem_map(&self, req: &VhostUserMMap, fd: &dyn AsRawFd) -> HandlerResult<u64> {
        if req.shmid != VIRTIO_FS_SHMCAP_ID_CACHE || req.len == 0 {
            return Err(io::Error::from_raw_os_error(libc::EINVAL));
        }
        if !self.is_req_valid(req.shm_offset, req.len) {
            return Err(io::Error::from_raw_os_error(libc::EINVAL));
        }
        let flags = VhostUserMMapFlags::from_bits(req.flags)
            .ok_or_else(|| io::Error::from_raw_os_error(libc::EINVAL))?;
        let prot = libc::PROT_READ
            | if flags.contains(VhostUserMMapFlags::WRITABLE) {
                libc::PROT_WRITE
            } else {
                0
            };

        let addr = self.mmap_cache_addr + req.shm_offset;
        // SAFETY: `[addr, addr + req.len)` was validated to lie within `self.mmap_cache_addr..+cache_size`
        // and `fd` is a valid file descriptor received via `SCM_RIGHTS`.
        let ret = unsafe {
            libc::mmap(
                addr as *mut libc::c_void,
                req.len as usize,
                prot,
                libc::MAP_SHARED | libc::MAP_FIXED,
                fd.as_raw_fd(),
                req.fd_offset as libc::off_t,
            )
        };
        if ret == libc::MAP_FAILED {
            return Err(io::Error::last_os_error());
        }
        Ok(0)
    }

    fn shmem_unmap(&self, req: &VhostUserMMap) -> HandlerResult<u64> {
        if req.shmid != VIRTIO_FS_SHMCAP_ID_CACHE {
            return Err(io::Error::from_raw_os_error(libc::EINVAL));
        }
        if req.len == 0 {
            return Ok(0);
        }
        let (offset, len) = if req.len == u64::MAX {
            (0, self.cache_size)
        } else {
            (req.shm_offset, req.len)
        };
        if !self.is_req_valid(offset, len) {
            return Err(io::Error::from_raw_os_error(libc::EINVAL));
        }

        let addr = self.mmap_cache_addr + offset;
        // SAFETY: `[addr, addr + len)` lies strictly within the reserved DAX `MmapRegion`.
        let ret = unsafe {
            libc::mmap(
                addr as *mut libc::c_void,
                len as usize,
                libc::PROT_NONE,
                libc::MAP_ANONYMOUS | libc::MAP_PRIVATE | libc::MAP_FIXED,
                -1,
                0,
            )
        };
        if ret == libc::MAP_FAILED {
            return Err(io::Error::last_os_error());
        }
        Ok(0)
    }
}

pub const VIRTIO_FS_TAG_LEN: usize = 36;
#[serde_as]
#[derive(Copy, Clone, Serialize, Deserialize)]
#[repr(C, packed)]
pub struct VirtioFsConfig {
    #[serde_as(as = "Bytes")]
    pub tag: [u8; VIRTIO_FS_TAG_LEN],
    pub num_request_queues: u32,
}

impl Default for VirtioFsConfig {
    fn default() -> Self {
        VirtioFsConfig {
            tag: [0; VIRTIO_FS_TAG_LEN],
            num_request_queues: 0,
        }
    }
}

// SAFETY: only a series of integers
unsafe impl ByteValued for VirtioFsConfig {}

pub struct Fs {
    vu_common: VhostUserCommon,
    id: String,
    config: VirtioFsConfig,
    // Hold ownership of the DAX shared memory window mapping allocated for the device.
    cache: Option<VirtioSharedMemoryList>,
    seccomp_action: SeccompAction,
    exit_evt: EventFd,
}

impl Fs {
    /// Create a new virtio-fs device.
    #[expect(clippy::too_many_arguments)]
    pub fn new(
        id: String,
        path: &str,
        tag: &str,
        req_num_queues: u16,
        queue_size: u16,
        cache: Option<VirtioSharedMemoryList>,
        seccomp_action: SeccompAction,
        exit_evt: EventFd,
        access_platform_enabled: bool,
        state: Option<State>,
    ) -> Result<Fs> {
        let num_queues = req_num_queues
            .checked_add(NUM_QUEUE_OFFSET)
            .ok_or(Error::BadQueueNum)?;

        let mut vu =
            VhostUserHandle::connect_vhost_user(false, path, num_queues, false, &exit_evt, |_| {
                Ok(())
            })?;

        let (
            avail_features,
            acked_features,
            acked_protocol_features,
            vu_num_queues,
            config,
            paused,
            vring_bases,
        ) = if let Some(state) = state {
            info!("Restoring vhost-user-fs {id}");

            vu.set_protocol_features_vhost_user(
                state.acked_features,
                state.acked_protocol_features,
            )?;

            vu.restore_state(&state)?;

            (
                state.avail_features,
                state.acked_features,
                state.acked_protocol_features,
                state.vu_num_queues,
                state.config,
                true,
                state.vring_bases,
            )
        } else {
            let avail_features = DEFAULT_VIRTIO_FEATURES;

            let mut avail_protocol_features = VhostUserProtocolFeatures::MQ
                | VhostUserProtocolFeatures::CONFIGURE_MEM_SLOTS
                | VhostUserProtocolFeatures::REPLY_ACK
                | VhostUserProtocolFeatures::INFLIGHT_SHMFD
                | VhostUserProtocolFeatures::LOG_SHMFD
                | VhostUserProtocolFeatures::DEVICE_STATE;
            if cache.is_some() {
                avail_protocol_features |= VhostUserProtocolFeatures::BACKEND_REQ
                    | VhostUserProtocolFeatures::BACKEND_SEND_FD
                    | VhostUserProtocolFeatures::SHMEM;
            }

            let (acked_features, acked_protocol_features) =
                vu.negotiate_features_vhost_user(avail_features, avail_protocol_features)?;

            if let Some(ref shm) = cache {
                let required = (VhostUserProtocolFeatures::BACKEND_REQ
                    | VhostUserProtocolFeatures::BACKEND_SEND_FD
                    | VhostUserProtocolFeatures::SHMEM)
                    .bits();
                if acked_protocol_features & required != required {
                    error!(
                        "vhost-user-fs DAX enabled (cache_size={} MiB), but backend did not negotiate SHMEM+BACKEND_REQ+BACKEND_SEND_FD (acked={acked_protocol_features:#x})",
                        shm.mapping.size() >> 20
                    );
                    return Err(Error::UnsupportedProtocolFeatures(required));
                }
                if let Ok(shmem_cfg) = vu.socket_handle().get_shmem_config()
                    && shmem_cfg.nregions >= 1
                    && shmem_cfg.memory_sizes[0] != shm.mapping.size() as u64
                {
                    warn!(
                        "vhost-user-fs backend reported SHMEM size {} bytes vs VMM cache_size {} bytes",
                        shmem_cfg.memory_sizes[0],
                        shm.mapping.size()
                    );
                }
            }

            let backend_num_queues =
                if acked_protocol_features & VhostUserProtocolFeatures::MQ.bits() != 0 {
                    vu.socket_handle()
                        .get_queue_num()
                        .map_err(Error::VhostUserGetQueueMaxNum)?
                } else {
                    DEFAULT_QUEUE_NUMBER as u64
                };

            if num_queues as u64 > backend_num_queues {
                error!(
                    "vhost-user-fs requested too many queues ({num_queues}) since the backend only supports {backend_num_queues}\n"
                );
                return Err(Error::BadQueueNum);
            }

            let mut config = VirtioFsConfig::default();
            let tag_bytes_slice = tag.as_bytes();
            let len = tag_bytes_slice.len().min(config.tag.len());
            config.tag[..len].copy_from_slice(&tag_bytes_slice[..len]);
            config.num_request_queues = req_num_queues as u32;

            let mut avail_features = acked_features;
            if access_platform_enabled {
                avail_features |= 1u64 << VIRTIO_F_ACCESS_PLATFORM;
            }

            (
                avail_features,
                acked_features & VhostUserVirtioFeatures::PROTOCOL_FEATURES.bits(),
                acked_protocol_features,
                num_queues,
                config,
                false,
                None,
            )
        };

        if let Some(ref shm) = cache {
            register_dax_window(
                shm.addr.raw_value(),
                shm.mapping.size() as u64,
                shm.mapping.as_ptr() as u64,
            );
        }

        Ok(Fs {
            vu_common: VhostUserCommon {
                virtio_common: VirtioCommon {
                    device_type: VirtioDeviceType::Fs as u32,
                    avail_features,
                    acked_features,
                    queue_sizes: vec![queue_size; num_queues as usize],
                    paused_sync: Some(Arc::new(Barrier::new(2))),
                    min_queues: 1,
                    paused: Arc::new(AtomicBool::new(paused)),
                    ..Default::default()
                },
                vu: Some(Arc::new(Mutex::new(vu))),
                acked_protocol_features,
                socket_path: path.to_string(),
                vu_num_queues,
                vring_bases,
                ..Default::default()
            },
            id,
            config,
            cache,
            seccomp_action,
            exit_evt,
        })
    }

    fn state(&self) -> result::Result<State, MigratableError> {
        self.vu_common.state(self.config)
    }
}

impl Drop for Fs {
    fn drop(&mut self) {
        if let Some(ref shm) = self.cache {
            unregister_dax_window(shm.mapping.as_ptr() as u64);
        }
        self.vu_common.shutdown();
    }
}

impl VirtioDevice for Fs {
    fn device_type(&self) -> u32 {
        self.vu_common.virtio_common.device_type
    }

    fn queue_max_sizes(&self) -> &[u16] {
        &self.vu_common.virtio_common.queue_sizes
    }

    fn features(&self) -> u64 {
        self.vu_common.virtio_common.avail_features
    }

    fn ack_features(&mut self, value: u64) {
        self.vu_common.virtio_common.ack_features(value);
    }

    fn read_config(&self, offset: u64, data: &mut [u8]) {
        self.read_config_from_slice(self.config.as_slice(), offset, data);
    }

    fn activate(&mut self, context: ActivationContext) -> ActivateResult {
        let ActivationContext {
            mem,
            interrupt_cb,
            queues,
            device_status,
        } = context;
        self.vu_common
            .virtio_common
            .activate(&queues, Arc::clone(&interrupt_cb))?;

        let shmem_bits =
            (VhostUserProtocolFeatures::BACKEND_REQ | VhostUserProtocolFeatures::SHMEM).bits();
        let backend_req_handler = if let Some(ref shm) = self.cache
            && (self.vu_common.acked_protocol_features & shmem_bits) == shmem_bits
        {
            let vu_frontend_req_handler = Arc::new(BackendReqHandler {
                cache_size: shm.mapping.size() as u64,
                mmap_cache_addr: shm.mapping.as_ptr() as u64,
            });
            let mut req_handler =
                FrontendReqHandler::new(vu_frontend_req_handler).map_err(|e| {
                    ActivateError::VhostUserSetup(Error::FrontendReqHandlerCreation(e))
                })?;
            if self.vu_common.acked_protocol_features & VhostUserProtocolFeatures::REPLY_ACK.bits()
                != 0
            {
                req_handler.set_reply_ack_flag(true);
            }
            Some(req_handler)
        } else {
            None
        };

        let (kill_evt, pause_evt) = self.vu_common.virtio_common.dup_eventfds()?;

        let mut handler = self.vu_common.activate(
            mem,
            &queues,
            Arc::clone(&interrupt_cb),
            self.vu_common.virtio_common.acked_features,
            backend_req_handler,
            kill_evt,
            pause_evt,
        )?;

        let paused = Arc::clone(&self.vu_common.virtio_common.paused);
        let paused_sync = self.vu_common.virtio_common.paused_sync.clone();

        self.vu_common.spawn_worker(
            &self.id,
            &self.seccomp_action,
            Thread::VirtioVhostFs,
            &self.exit_evt,
            Arc::clone(&device_status),
            Arc::clone(&interrupt_cb),
            move || handler.run(&paused, paused_sync.as_ref().unwrap()),
        )?;

        event!("virtio-device", "activated", "id", &self.id);
        Ok(())
    }

    fn reset(&mut self) {
        self.vu_common.reset(&self.id);
    }

    fn shutdown(&mut self) {
        self.vu_common.shutdown();
    }

    fn get_shm_regions(&self) -> Option<VirtioSharedMemoryList> {
        self.cache.clone()
    }

    fn set_shm_regions(
        &mut self,
        shm_regions: VirtioSharedMemoryList,
    ) -> result::Result<(), crate::Error> {
        if let Some(cache) = self.cache.as_mut() {
            register_dax_window(
                shm_regions.addr.raw_value(),
                shm_regions.mapping.size() as u64,
                shm_regions.mapping.as_ptr() as u64,
            );
            *cache = shm_regions;
            Ok(())
        } else {
            Err(crate::Error::SetShmRegionsNotSupported)
        }
    }

    fn add_memory_region(&mut self, region: &Arc<GuestRegion>) -> result::Result<(), crate::Error> {
        self.vu_common.add_memory_region(region)
    }

    fn userspace_mappings(&self) -> Vec<UserspaceMapping> {
        let mut mappings = Vec::new();
        if let Some(shm) = self.cache.as_ref() {
            mappings.push(UserspaceMapping {
                mem_slot: shm.mem_slot,
                addr: shm.addr,
                mapping: Arc::clone(&shm.mapping),
                mergeable: false,
            });
        }

        mappings
    }
}

impl Pausable for Fs {
    fn pause(&mut self) -> result::Result<(), MigratableError> {
        self.vu_common.pause()?;
        self.vu_common.virtio_common.pause()
    }

    fn resume(&mut self) -> result::Result<(), MigratableError> {
        self.vu_common.virtio_common.resume()?;
        self.vu_common.resume()
    }
}

impl Snapshottable for Fs {
    fn id(&self) -> String {
        self.id.clone()
    }

    fn snapshot(&mut self) -> result::Result<Snapshot, MigratableError> {
        self.vu_common.snapshot(&self.state()?)
    }
}
impl Transportable for Fs {}

impl Migratable for Fs {
    fn start_dirty_log(&mut self) -> result::Result<(), MigratableError> {
        self.vu_common.start_dirty_log()
    }

    fn stop_dirty_log(&mut self) -> result::Result<(), MigratableError> {
        self.vu_common.stop_dirty_log()
    }

    fn dirty_log(&mut self) -> result::Result<MemoryRangeTable, MigratableError> {
        self.vu_common.dirty_log()
    }

    fn notify_started_migration(&mut self) -> result::Result<(), MigratableError> {
        self.vu_common.notify_started_migration()
    }

    fn notify_failed_migration(&mut self) -> result::Result<(), MigratableError> {
        self.vu_common.notify_failed_migration()
    }

    fn notify_completed_migration(&mut self) -> result::Result<(), MigratableError> {
        self.vu_common.notify_completed_migration()
    }
}
