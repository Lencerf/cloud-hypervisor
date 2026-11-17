// Copyright 2019 Intel Corporation. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::result;
use std::sync::atomic::{AtomicU16, Ordering};
use std::sync::{Arc, Mutex};

use log::{error, info};
use net_util::{CtrlQueue, MacAddr, VirtioNetConfig};
use seccompiler::SeccompAction;
use vhost::vhost_user::message::{VhostUserConfigFlags, VhostUserProtocolFeatures};
use vhost::vhost_user::{FrontendReqHandler, VhostUserFrontend, VhostUserFrontendReqHandler};
use virtio_bindings::virtio_net::{
    VIRTIO_NET_F_CSUM, VIRTIO_NET_F_CTRL_VQ, VIRTIO_NET_F_GUEST_ANNOUNCE, VIRTIO_NET_F_GUEST_CSUM,
    VIRTIO_NET_F_GUEST_ECN, VIRTIO_NET_F_GUEST_TSO4, VIRTIO_NET_F_GUEST_TSO6,
    VIRTIO_NET_F_GUEST_UFO, VIRTIO_NET_F_HOST_ECN, VIRTIO_NET_F_HOST_TSO4, VIRTIO_NET_F_HOST_TSO6,
    VIRTIO_NET_F_HOST_UFO, VIRTIO_NET_F_MAC, VIRTIO_NET_F_MQ, VIRTIO_NET_F_MRG_RXBUF,
    VIRTIO_NET_F_MTU, VIRTIO_NET_F_STATUS, VIRTIO_NET_S_ANNOUNCE, VIRTIO_NET_S_LINK_UP,
};
use virtio_bindings::virtio_ring::VIRTIO_RING_F_EVENT_IDX;
use virtio_queue::QueueT;
use vm_memory::ByteValued;
use vm_migration::protocol::MemoryRangeTable;
use vm_migration::{Migratable, MigratableError, Pausable, Snapshot, Snapshottable, Transportable};
use vmm_sys_util::eventfd::EventFd;
use vmm_sys_util::timerfd::TimerFd;

use crate::device::ActivationContext;
use crate::net::{AnnounceOps, AnnouncementState, Announcer, VirtioNetGuestAnnounceOps};
use crate::seccomp_filters::Thread;
use crate::vhost_user::vu_common_ctrl::{VhostUserConfig, VhostUserHandle};
use crate::vhost_user::{
    DEFAULT_VIRTIO_FEATURES, Error, PostcopyHandler, Result, VhostUserCommon, VhostUserState,
};
use crate::{
    ActivateError, ActivateResult, GuestRegion, NetCtrlEpollHandler, VIRTIO_F_ACCESS_PLATFORM,
    VirtioCommon, VirtioDevice, VirtioDeviceType,
};

const DEFAULT_QUEUE_NUMBER: u16 = 2;

pub type State = VhostUserState<VirtioNetConfig>;

struct BackendReqHandler {}
impl VhostUserFrontendReqHandler for BackendReqHandler {}

pub struct Net {
    vu_common: VhostUserCommon,
    id: String,
    config: VirtioNetConfig,
    curr_queue_pairs: Arc<AtomicU16>,
    enabled_queues: Arc<AtomicU16>,
    seccomp_action: SeccompAction,
    exit_evt: EventFd,
    announce: AnnouncementState,
}

impl Net {
    /// Derive the guest-visible feature set from the backend-negotiated
    /// features plus frontend only bits.
    fn guest_avail_features(backend_acked_features: u64, advertise_mtu: bool) -> u64 {
        let mut guest_avail_features = backend_acked_features | (1 << VIRTIO_NET_F_MAC);

        // Guest announce is implemented by the frontend through config
        // changes and the locally handled control queue.
        if guest_avail_features & (1 << VIRTIO_NET_F_CTRL_VQ) != 0 {
            guest_avail_features |= 1 << VIRTIO_NET_F_STATUS;
            guest_avail_features |= 1 << VIRTIO_NET_F_GUEST_ANNOUNCE;
        }

        if advertise_mtu {
            guest_avail_features |= 1 << VIRTIO_NET_F_MTU;
        }

        guest_avail_features
    }

    /// Create a new vhost-user-net device
    #[expect(clippy::too_many_arguments)]
    pub fn new(
        id: String,
        mac_addr: &mut Option<MacAddr>,
        mtu: Option<u16>,
        vu_cfg: VhostUserConfig,
        server: bool,
        seccomp_action: SeccompAction,
        exit_evt: EventFd,
        access_platform_enabled: bool,
        state: Option<State>,
        postcopy_handler: Option<Arc<dyn PostcopyHandler>>,
        offload_tso: bool,
        offload_ufo: bool,
        offload_csum: bool,
    ) -> Result<Net> {
        let mut num_queues = vu_cfg.num_queues;

        let mut vu = VhostUserHandle::connect_vhost_user(
            server,
            &vu_cfg.socket,
            num_queues,
            false,
            &exit_evt,
            |_| Ok(()),
        )?;

        let (
            avail_features,
            acked_features,
            acked_protocol_features,
            vu_num_queues,
            config,
            paused,
            vring_bases,
            announce_pending,
            curr_queue_pairs,
        ) = if let Some(state) = state {
            info!("Restoring vhost-user-net {id}");

            vu.set_protocol_features_vhost_user(
                state.acked_protocol_features,
                postcopy_handler.is_some(),
            )?;

            vu.restore_state(&state)?;

            // If the control queue feature has been negotiated, let's
            // increase the number of queues.
            if state.acked_features & (1 << VIRTIO_NET_F_CTRL_VQ) != 0 {
                num_queues = num_queues.checked_add(1).ok_or(Error::BadQueueNum)?;
            }

            // Always set the announcement pending if the device was restored and
            // VIRTIO_NET_F_GUEST_ANNOUNCE was negotiated, to make sure the device announces itself.
            let announce_pending =
                (state.acked_features & (1u64 << VIRTIO_NET_F_GUEST_ANNOUNCE)) != 0;

            // Older snapshots without curr_queue_pairs keep every configured pair enabled.
            let default_pairs = (state.vu_num_queues / 2).max(1);
            let curr_queue_pairs = state.curr_queue_pairs.unwrap_or(default_pairs);

            (
                state.avail_features,
                state.acked_features,
                state.acked_protocol_features,
                state.vu_num_queues,
                state.config,
                true,
                state.vring_bases,
                announce_pending,
                curr_queue_pairs,
            )
        } else {
            // Filling device and vring features VMM supports.
            let mut backend_avail_features = (1 << VIRTIO_NET_F_MRG_RXBUF)
                | (1 << VIRTIO_NET_F_CTRL_VQ)
                | (1 << VIRTIO_NET_F_GUEST_ANNOUNCE)
                | (1 << VIRTIO_NET_F_MAC)
                | (1 << VIRTIO_NET_F_MTU)
                | (1 << VIRTIO_NET_F_MQ)
                | DEFAULT_VIRTIO_FEATURES;

            // Configure TSO/UFO features when hardware checksum offload is enabled.
            if offload_csum {
                backend_avail_features |= (1 << VIRTIO_NET_F_CSUM) | (1 << VIRTIO_NET_F_GUEST_CSUM);

                if offload_tso {
                    backend_avail_features |= (1 << VIRTIO_NET_F_HOST_ECN)
                        | (1 << VIRTIO_NET_F_HOST_TSO4)
                        | (1 << VIRTIO_NET_F_HOST_TSO6)
                        | (1 << VIRTIO_NET_F_GUEST_ECN)
                        | (1 << VIRTIO_NET_F_GUEST_TSO4)
                        | (1 << VIRTIO_NET_F_GUEST_TSO6);
                }

                if offload_ufo {
                    backend_avail_features |=
                        (1 << VIRTIO_NET_F_HOST_UFO) | (1 << VIRTIO_NET_F_GUEST_UFO);
                }
            }

            let avail_protocol_features = VhostUserProtocolFeatures::MQ
                | VhostUserProtocolFeatures::CONFIGURE_MEM_SLOTS
                | VhostUserProtocolFeatures::REPLY_ACK
                | VhostUserProtocolFeatures::INFLIGHT_SHMFD
                | VhostUserProtocolFeatures::LOG_SHMFD
                | VhostUserProtocolFeatures::DEVICE_STATE
                | VhostUserProtocolFeatures::CONFIG;

            let (backend_acked_features, acked_protocol_features) = vu
                .negotiate_features_vhost_user(
                    backend_avail_features,
                    avail_protocol_features,
                    postcopy_handler.is_some(),
                )?;

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
                    "vhost-user-net requested too many queues ({num_queues}) since the backend only supports {backend_num_queues}\n"
                );
                return Err(Error::BadQueueNum);
            }

            let backend_config =
                if acked_protocol_features & VhostUserProtocolFeatures::CONFIG.bits() != 0 {
                    let config_len = size_of::<VirtioNetConfig>();
                    let config_space: Vec<u8> = vec![0u8; config_len];

                    let (_, config_space) = vu
                        .socket_handle()
                        .get_config(
                            0,
                            config_len as u32,
                            VhostUserConfigFlags::WRITABLE,
                            config_space.as_slice(),
                        )
                        .map_err(Error::VhostUserGetConfig)?;
                    VirtioNetConfig::from_slice(config_space.as_slice()).copied()
                } else {
                    None
                };

            let backend_provides_mac = backend_acked_features & (1 << VIRTIO_NET_F_MAC) != 0
                && backend_config.is_some()
                && mac_addr.is_none();

            let guest_mac = if backend_provides_mac {
                None
            } else {
                Some(*mac_addr.get_or_insert_with(MacAddr::local_random))
            };

            let backend_provides_mtu = backend_acked_features & (1 << VIRTIO_NET_F_MTU) != 0
                && backend_config.is_some()
                && mtu.is_none();

            let mut config = backend_config.unwrap_or_default();
            config.populate(guest_mac, num_queues, mtu);

            // If the control queue feature has been negotiated, let's increase
            // the number of queues.
            let vu_num_queues = num_queues;
            if backend_acked_features & (1 << VIRTIO_NET_F_CTRL_VQ) != 0 {
                num_queues = num_queues.checked_add(1).ok_or(Error::BadQueueNum)?;
            }

            // Build the feature set that gets exposed to the guest. Some frontend available
            // features are dependent on the features the backend supports.
            let mut guest_avail_features = Self::guest_avail_features(
                backend_acked_features,
                backend_provides_mtu || mtu.is_some(),
            );
            if access_platform_enabled {
                guest_avail_features |= 1u64 << VIRTIO_F_ACCESS_PLATFORM;
            }

            (
                guest_avail_features,
                0,
                acked_protocol_features,
                vu_num_queues,
                config,
                false,
                None,
                false,
                1,
            )
        };

        if let Some(postcopy_handler) = postcopy_handler {
            vu.start_postcopy(id.clone(), postcopy_handler)?;
        }

        let enabled_queues = Arc::new(AtomicU16::new(curr_queue_pairs.saturating_mul(2)));
        let curr_queue_pairs = Arc::new(AtomicU16::new(curr_queue_pairs));

        let virtio_common = VirtioCommon {
            device_type: VirtioDeviceType::Net as u32,
            queue_sizes: vec![vu_cfg.queue_size; num_queues as usize],
            avail_features,
            acked_features,
            min_queues: DEFAULT_QUEUE_NUMBER,
            ..VirtioCommon::new(paused).map_err(Error::CreateEventFd)?
        };

        Ok(Net {
            id,
            vu_common: VhostUserCommon {
                vu: Some(Arc::new(Mutex::new(vu))),
                acked_protocol_features,
                socket_path: vu_cfg.socket,
                vu_num_queues,
                server,
                vring_bases,
                enabled_queues: Some(Arc::clone(&enabled_queues)),
                ..VhostUserCommon::new(virtio_common)
            },
            config,
            curr_queue_pairs,
            enabled_queues,
            seccomp_action,
            exit_evt,
            announce: AnnouncementState::new(announce_pending).map_err(Error::CreateEventFd)?,
        })
    }

    fn state(&self) -> result::Result<State, MigratableError> {
        let mut state = self.vu_common.state(self.config)?;
        state.curr_queue_pairs = Some(self.curr_queue_pairs.load(Ordering::Acquire));
        Ok(state)
    }

    /// Compute `(curr_queue_pairs, ctrl_max_virtqueue_pairs)` for activation
    /// from the activated data queues and negotiated features.
    fn active_mq_params(&self, data_queues_len: usize) -> (u16, u16) {
        let active_pairs = (data_queues_len / 2) as u16;
        let mq_acked = self
            .vu_common
            .virtio_common
            .feature_acked(VIRTIO_NET_F_MQ.into());
        let max_pairs = if mq_acked {
            active_pairs.min(self.config.max_virtqueue_pairs)
        } else {
            1
        };
        let curr_queue_pairs = self
            .curr_queue_pairs
            .load(Ordering::Acquire)
            .min(max_pairs)
            .max(1);
        let ctrl_max_virtqueue_pairs = if mq_acked { max_pairs } else { 0 };
        (curr_queue_pairs, ctrl_max_virtqueue_pairs)
    }

    /// Compute the guest-visible virtio-net status field.
    fn guest_visible_status(&self) -> u16 {
        let mut status = 0;

        if self
            .vu_common
            .virtio_common
            .feature_acked(VIRTIO_NET_F_STATUS.into())
        {
            status |= VIRTIO_NET_S_LINK_UP as u16;

            if self
                .vu_common
                .virtio_common
                .feature_acked(VIRTIO_NET_F_GUEST_ANNOUNCE.into())
                && self.announce.pending.load(Ordering::Acquire)
            {
                status |= VIRTIO_NET_S_ANNOUNCE as u16;
            }
        }

        status
    }
}

impl Drop for Net {
    fn drop(&mut self) {
        self.vu_common.shutdown();
    }
}

impl VirtioDevice for Net {
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
        let mut config = self.config;
        config.status = self.guest_visible_status();
        self.read_config_from_slice(config.as_slice(), offset, data);
    }

    fn activate(&mut self, context: ActivationContext) -> ActivateResult {
        let ActivationContext {
            mem,
            interrupt_cb,
            mut queues,
            device_status,
        } = context;
        self.vu_common
            .virtio_common
            .activate(&queues, Arc::clone(&interrupt_cb))?;

        let num_queues = u16::try_from(queues.len()).map_err(|_| ActivateError::BadActivate)?;
        let event_idx = self
            .vu_common
            .virtio_common
            .feature_acked(VIRTIO_RING_F_EVENT_IDX.into());
        let has_ctrl_queue = self
            .vu_common
            .virtio_common
            .feature_acked(VIRTIO_NET_F_CTRL_VQ.into())
            && !num_queues.is_multiple_of(2);

        let ctrl_queue_info = if has_ctrl_queue {
            let ctrl_queue_index = num_queues - 1;
            Some((ctrl_queue_index, queues.remove(ctrl_queue_index as usize)))
        } else {
            None
        };

        if !queues.len().is_multiple_of(2) {
            return Err(ActivateError::BadActivate);
        }

        let (curr_queue_pairs, ctrl_max_virtqueue_pairs) = self.active_mq_params(queues.len());
        self.curr_queue_pairs
            .store(curr_queue_pairs, Ordering::Release);
        self.enabled_queues
            .store(curr_queue_pairs.saturating_mul(2), Ordering::Release);

        let backend_req_handler: Option<FrontendReqHandler<BackendReqHandler>> = None;

        // Configure the vhost-user backend before starting the worker threads so
        // only the active queue pairs are enabled and ready for control commands.
        let (kill_evt, pause_evt) = self.vu_common.virtio_common.dup_eventfds()?;

        let mut handler = self.vu_common.activate(
            mem.clone(),
            &queues,
            Arc::clone(&interrupt_cb),
            self.vu_common.virtio_common.acked_features,
            backend_req_handler,
            kill_evt,
            pause_evt,
        )?;

        if let Some((ctrl_queue_index, (_, mut ctrl_queue, ctrl_queue_evt))) = ctrl_queue_info {
            ctrl_queue.set_event_idx(event_idx);

            let (ctrl_kill_evt, ctrl_pause_evt) = self.vu_common.virtio_common.dup_eventfds()?;

            let announce_ops = VirtioNetGuestAnnounceOps::new(
                Arc::clone(&interrupt_cb),
                self.vu_common
                    .virtio_common
                    .feature_acked(VIRTIO_NET_F_GUEST_ANNOUNCE.into()),
                &self.announce,
            );

            let announcer = Announcer::new(
                &self.announce,
                vec![Box::new(announce_ops) as Box<dyn AnnounceOps>].into_boxed_slice(),
            );

            let vu = Arc::clone(
                self.vu_common
                    .vu
                    .as_ref()
                    .ok_or(ActivateError::BadActivate)?,
            );
            let dev_id = self.id.clone();
            let ctrl_q = CtrlQueue::new(
                Vec::new(),
                Arc::clone(&self.announce.pending),
                ctrl_max_virtqueue_pairs,
                Arc::clone(&self.curr_queue_pairs),
                self.vu_common.virtio_common.acked_features,
            )
            .with_mq_callback(move |queue_pairs| {
                vu.lock()
                    .unwrap()
                    .update_enabled_queues(queue_pairs.saturating_mul(2))
                    .inspect_err(|e| {
                        error!(
                            "Failed updating enabled vhost-user queues for {dev_id} to {queue_pairs} pairs: {e:?}"
                        );
                    })
                    .is_ok()
            });

            let mut ctrl_handler = NetCtrlEpollHandler {
                mem,
                kill_evt: ctrl_kill_evt,
                pause_evt: ctrl_pause_evt,
                ctrl_q,
                queue: ctrl_queue,
                queue_evt: ctrl_queue_evt,
                access_platform: None,
                interrupt_cb: Arc::clone(&interrupt_cb),
                queue_index: ctrl_queue_index,
                announce_evt: self
                    .announce
                    .evt
                    .try_clone()
                    .map_err(ActivateError::CloneEventFd)?,
                announce_retry_timer: TimerFd::new().map_err(ActivateError::CreateTimerFd)?,
                announcer,
            };

            self.vu_common.spawn_worker(
                &format!("{}_ctrl", self.id),
                &self.seccomp_action,
                Thread::VirtioVhostNetCtl,
                &self.exit_evt,
                Arc::clone(&device_status),
                Arc::clone(&interrupt_cb),
                move |pause_common| ctrl_handler.run_ctrl(pause_common),
            )?;
        }

        self.vu_common.spawn_worker(
            &self.id,
            &self.seccomp_action,
            Thread::VirtioVhostNet,
            &self.exit_evt,
            Arc::clone(&device_status),
            Arc::clone(&interrupt_cb),
            move |pause_common| handler.run(pause_common),
        )?;

        self.announce.notify(
            self.vu_common
                .virtio_common
                .feature_acked(VIRTIO_NET_F_GUEST_ANNOUNCE.into()),
        );

        Ok(())
    }

    fn reset(&mut self) {
        self.vu_common.reset(&self.id);
        self.announce.reset();
        self.curr_queue_pairs.store(1, Ordering::Release);
        self.enabled_queues.store(2, Ordering::Release);
    }

    fn shutdown(&mut self) {
        self.vu_common.shutdown();
    }

    fn add_memory_region(&mut self, region: &Arc<GuestRegion>) -> result::Result<(), crate::Error> {
        self.vu_common.add_memory_region(region)
    }
}

impl Pausable for Net {
    fn pause(&mut self) -> result::Result<(), MigratableError> {
        self.announce.invalidate();
        self.vu_common.pause()?;
        self.vu_common.virtio_common.pause()
    }

    fn resume(&mut self) -> result::Result<(), MigratableError> {
        self.vu_common.virtio_common.resume()?;
        self.vu_common.resume()?;
        self.announce.notify(
            self.vu_common
                .virtio_common
                .feature_acked(VIRTIO_NET_F_GUEST_ANNOUNCE.into()),
        );
        Ok(())
    }
}

impl Snapshottable for Net {
    fn id(&self) -> String {
        self.id.clone()
    }

    fn snapshot(&mut self) -> result::Result<Snapshot, MigratableError> {
        self.vu_common.snapshot(&self.state()?)
    }
}
impl Transportable for Net {}

impl Migratable for Net {
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
        self.announce.invalidate();
        self.vu_common.notify_started_migration()
    }

    fn notify_failed_migration(&mut self) -> result::Result<(), MigratableError> {
        self.vu_common.notify_failed_migration()
    }

    fn notify_completed_migration(&mut self) -> result::Result<(), MigratableError> {
        self.vu_common.notify_completed_migration()
    }
}

#[cfg(test)]
mod tests {
    use std::mem::{offset_of, size_of};

    use seccompiler::SeccompAction;
    use serde::Serialize;
    use virtio_bindings::virtio_net::{VIRTIO_NET_F_STATUS, VIRTIO_NET_S_LINK_UP};
    use vmm_sys_util::eventfd::EventFd;

    use super::*;
    use crate::VirtioInterrupt;

    fn test_net(
        acked_features: u64,
        interrupt_cb: Option<Arc<dyn VirtioInterrupt>>,
    ) -> Result<Net> {
        let virtio_common = VirtioCommon {
            acked_features,
            interrupt_cb,
            ..VirtioCommon::new(false).unwrap()
        };
        let enabled_queues = Arc::new(AtomicU16::new(2));

        Ok(Net {
            vu_common: VhostUserCommon {
                enabled_queues: Some(Arc::clone(&enabled_queues)),
                ..VhostUserCommon::new(virtio_common)
            },
            id: "test-vu-net".to_string(),
            config: VirtioNetConfig::default(),
            curr_queue_pairs: Arc::new(AtomicU16::new(1)),
            enabled_queues,
            seccomp_action: SeccompAction::Allow,
            exit_evt: EventFd::new(libc::EFD_NONBLOCK).unwrap(),
            announce: AnnouncementState::new(false).map_err(Error::CreateEventFd)?,
        })
    }

    const STATUS_OFFSET: usize = offset_of!(VirtioNetConfig, status);
    fn read_status(device: &Net) -> u16 {
        let mut data = vec![0; size_of::<VirtioNetConfig>()];
        device.read_config(0, &mut data);

        u16::from_le_bytes(
            data[STATUS_OFFSET..STATUS_OFFSET + size_of::<u16>()]
                .try_into()
                .unwrap(),
        )
    }

    #[test]
    fn test_status_feature_reports_link_up() {
        // The current implementation should always report "link up" if
        // VIRTIO_NET_F_STATUS has been negotiated.
        let net = test_net(1 << VIRTIO_NET_F_STATUS, None).unwrap();

        assert_eq!(read_status(&net), VIRTIO_NET_S_LINK_UP as u16);
    }

    #[test]
    fn test_restore_state_without_curr_queue_pairs_keeps_all_pairs() {
        #[derive(Serialize)]
        struct LegacyVhostUserNetState {
            avail_features: u64,
            acked_features: u64,
            config: VirtioNetConfig,
            acked_protocol_features: u64,
            vu_num_queues: u16,
        }

        let snapshot = Snapshot::new_from_state(&LegacyVhostUserNetState {
            avail_features: 0,
            acked_features: 0,
            config: VirtioNetConfig::default(),
            acked_protocol_features: 0,
            vu_num_queues: 8,
        })
        .unwrap();
        let state: State = snapshot.to_state().unwrap();
        assert_eq!(state.curr_queue_pairs, None);
    }

    #[test]
    fn test_mq_vq_pairs_set_sends_set_vring_enable_and_tracks_state() {
        use std::fs::File;
        use std::io::{self, Read, Write};
        use std::os::unix::io::FromRawFd;
        use std::os::unix::net::{UnixListener, UnixStream};
        use std::sync::atomic::AtomicU8;
        use std::sync::mpsc;
        use std::thread;
        use std::time::Duration;

        use vhost::vhost_user::message::{
            FrontendReq, VhostUserHeaderFlag, VhostUserVirtioFeatures,
        };
        use virtio_bindings::virtio_net::{
            VIRTIO_NET_CTRL_MQ, VIRTIO_NET_CTRL_MQ_VQ_PAIRS_SET, VIRTIO_NET_ERR, VIRTIO_NET_OK,
        };
        use virtio_bindings::virtio_ring::{VRING_DESC_F_NEXT, VRING_DESC_F_WRITE};
        use vm_memory::{Bytes, FileOffset, GuestAddress, GuestMemoryAtomic};
        use vm_virtio::queue::testing::VirtQueue as GuestQ;
        use vmm_sys_util::sock_ctrl_msg::ScmSocket;
        use vmm_sys_util::tempdir::TempDir;

        use crate::{VIRTIO_F_VERSION_1, VirtioInterruptType};

        #[repr(C, packed)]
        #[derive(Clone, Copy, Default)]
        struct ControlHeader {
            class: u8,
            cmd: u8,
        }
        // SAFETY: ControlHeader is plain old data with no padding.
        unsafe impl ByteValued for ControlHeader {}

        struct CtrlNotifyInterrupt {
            ctrl_queue_index: u16,
            tx: Mutex<mpsc::Sender<()>>,
        }

        impl VirtioInterrupt for CtrlNotifyInterrupt {
            fn trigger(&self, int_type: VirtioInterruptType) -> io::Result<()> {
                if matches!(int_type, VirtioInterruptType::Queue(idx) if idx == self.ctrl_queue_index)
                {
                    let _ = self.tx.lock().unwrap().send(());
                }
                Ok(())
            }

            fn set_notifier(
                &self,
                _int_type: u32,
                _notifier: Option<EventFd>,
                _vm: &dyn hypervisor::Vm,
            ) -> io::Result<()> {
                Ok(())
            }
        }

        fn recv_msg(stream: &mut UnixStream) -> Option<(u32, u32, Vec<u8>)> {
            let mut hdr = [0u8; 12];
            let mut fds = [0; 8];
            let mut iovs = [libc::iovec {
                iov_base: hdr.as_mut_ptr().cast(),
                iov_len: hdr.len(),
            }];
            // SAFETY: hdr is owned and valid for 12 bytes; any received fds are closed below.
            let (bytes, fd_count) = unsafe { stream.recv_with_fds(&mut iovs, &mut fds).ok()? };
            for &fd in &fds[..fd_count] {
                // SAFETY: fd was just received from the kernel via SCM_RIGHTS.
                unsafe {
                    drop(File::from_raw_fd(fd));
                }
            }
            if bytes == 0 {
                return None;
            }
            assert_eq!(bytes, 12);
            let req = u32::from_ne_bytes(hdr[0..4].try_into().unwrap());
            let flags = u32::from_ne_bytes(hdr[4..8].try_into().unwrap());
            let size = u32::from_ne_bytes(hdr[8..12].try_into().unwrap()) as usize;
            let mut payload = vec![0u8; size];
            if size > 0 {
                stream.read_exact(&mut payload).unwrap();
            }
            Some((req, flags, payload))
        }

        fn send_u64_reply(stream: &mut UnixStream, req: u32, val: u64) {
            let mut reply = Vec::with_capacity(20);
            reply.extend_from_slice(&req.to_ne_bytes());
            reply.extend_from_slice(&(VhostUserHeaderFlag::REPLY.bits() | 1).to_ne_bytes());
            reply.extend_from_slice(&8u32.to_ne_bytes());
            reply.extend_from_slice(&val.to_ne_bytes());
            stream.write_all(&reply).unwrap();
        }

        let temp_dir = TempDir::new_with_prefix("/tmp/vhost-user-net-mq-").unwrap();
        let socket_path = temp_dir.as_path().join("backend.sock");
        let listener = UnixListener::bind(&socket_path).unwrap();

        let (vring_enable_tx, vring_enable_rx) = mpsc::channel::<(u32, bool)>();
        let backend_features = (1u64 << VIRTIO_F_VERSION_1)
            | (1u64 << VIRTIO_NET_F_MQ)
            | (1u64 << VIRTIO_NET_F_CTRL_VQ)
            | VhostUserVirtioFeatures::PROTOCOL_FEATURES.bits();
        let proto_features =
            (VhostUserProtocolFeatures::MQ | VhostUserProtocolFeatures::REPLY_ACK).bits();

        let backend = thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            while let Some((req, flags, payload)) = recv_msg(&mut stream) {
                let need_reply = flags & VhostUserHeaderFlag::NEED_REPLY.bits() != 0;
                if req == u32::from(FrontendReq::GET_FEATURES) {
                    send_u64_reply(&mut stream, req, backend_features);
                } else if req == u32::from(FrontendReq::GET_PROTOCOL_FEATURES) {
                    send_u64_reply(&mut stream, req, proto_features);
                } else if req == u32::from(FrontendReq::GET_QUEUE_NUM) {
                    send_u64_reply(&mut stream, req, 4);
                } else if req == u32::from(FrontendReq::GET_VRING_BASE) {
                    let index = u32::from_ne_bytes(payload[0..4].try_into().unwrap());
                    let mut reply = Vec::with_capacity(20);
                    reply.extend_from_slice(&req.to_ne_bytes());
                    reply.extend_from_slice(&(VhostUserHeaderFlag::REPLY.bits() | 1).to_ne_bytes());
                    reply.extend_from_slice(&8u32.to_ne_bytes());
                    reply.extend_from_slice(&index.to_ne_bytes());
                    reply.extend_from_slice(&0u32.to_ne_bytes());
                    stream.write_all(&reply).unwrap();
                } else if req == u32::from(FrontendReq::SET_VRING_ENABLE) {
                    let index = u32::from_ne_bytes(payload[0..4].try_into().unwrap());
                    let num = u32::from_ne_bytes(payload[4..8].try_into().unwrap());
                    let _ = vring_enable_tx.send((index, num != 0));
                    if need_reply {
                        send_u64_reply(&mut stream, req, 0);
                    }
                } else if need_reply {
                    send_u64_reply(&mut stream, req, 0);
                }
            }
        });

        let mut mac = None;
        let mut net = Net::new(
            "test-vu-net-mq".to_string(),
            &mut mac,
            None,
            VhostUserConfig {
                socket: socket_path.to_str().unwrap().to_string(),
                num_queues: 4,
                queue_size: 16,
            },
            false,
            SeccompAction::Allow,
            EventFd::new(libc::EFD_NONBLOCK).unwrap(),
            false,
            None,
            None,
            false,
            false,
            false,
        )
        .unwrap();

        let guest_features = (1u64 << VIRTIO_F_VERSION_1)
            | (1u64 << VIRTIO_NET_F_MQ)
            | (1u64 << VIRTIO_NET_F_CTRL_VQ);
        net.ack_features(guest_features);

        const MEM_SIZE: usize = 0x40_0000;
        let mem_file = File::options()
            .read(true)
            .write(true)
            .create_new(true)
            .open(temp_dir.as_path().join("guest_mem"))
            .unwrap();
        mem_file.set_len(MEM_SIZE as u64).unwrap();
        let mem = crate::GuestMemory::from_ranges_with_files(&[(
            GuestAddress(0),
            MEM_SIZE,
            Some(FileOffset::new(mem_file, 0)),
        )])
        .unwrap();

        let mut queues = Vec::new();
        for i in 0..4u16 {
            let gq = GuestQ::new(GuestAddress(0x10_0000 + u64::from(i) * 0x1_0000), &mem, 16);
            queues.push((
                i,
                gq.create_queue(),
                EventFd::new(libc::EFD_NONBLOCK).unwrap(),
            ));
        }

        let ctrl_gq = GuestQ::new(GuestAddress(0x20_0000), &mem, 16);
        let ctrl_evt = EventFd::new(libc::EFD_NONBLOCK).unwrap();
        let ctrl_evt_kick = ctrl_evt.try_clone().unwrap();
        queues.push((4, ctrl_gq.create_queue(), ctrl_evt));

        let (ctrl_done_tx, ctrl_done_rx) = mpsc::channel();
        let interrupt_cb: Arc<dyn VirtioInterrupt> = Arc::new(CtrlNotifyInterrupt {
            ctrl_queue_index: 4,
            tx: Mutex::new(ctrl_done_tx),
        });

        net.activate(ActivationContext {
            mem: GuestMemoryAtomic::new(mem.clone()),
            interrupt_cb,
            queues,
            device_status: Arc::new(AtomicU8::new(0)),
        })
        .unwrap();

        let recv_four = |rx: &mpsc::Receiver<(u32, bool)>| -> Vec<(u32, bool)> {
            (0..4)
                .map(|_| rx.recv_timeout(Duration::from_secs(5)).unwrap())
                .collect()
        };

        // 1. Initial activation enables only queue pair 0 (vrings 0, 1) and disables pair 1 (vrings 2, 3).
        assert_eq!(
            recv_four(&vring_enable_rx),
            vec![(0, true), (1, true), (2, false), (3, false)]
        );
        assert_eq!(net.state().unwrap().curr_queue_pairs, Some(1));

        let mut avail_idx = 0u16;
        let send_mq_cmd = |pairs: u16, avail_idx: &mut u16| -> u8 {
            const HDR_ADDR: u64 = 0x25_0000;
            const DATA_ADDR: u64 = 0x25_1000;
            const STATUS_ADDR: u64 = 0x25_2000;

            ctrl_gq.dtable[0].set(
                HDR_ADDR,
                size_of::<ControlHeader>() as u32,
                VRING_DESC_F_NEXT.try_into().unwrap(),
                1,
            );
            ctrl_gq.dtable[1].set(
                DATA_ADDR,
                size_of::<u16>() as u32,
                VRING_DESC_F_NEXT.try_into().unwrap(),
                2,
            );
            ctrl_gq.dtable[2].set(STATUS_ADDR, 1, VRING_DESC_F_WRITE.try_into().unwrap(), 0);

            mem.write_obj(
                ControlHeader {
                    class: VIRTIO_NET_CTRL_MQ as u8,
                    cmd: VIRTIO_NET_CTRL_MQ_VQ_PAIRS_SET as u8,
                },
                GuestAddress(HDR_ADDR),
            )
            .unwrap();
            mem.write_obj(pairs, GuestAddress(DATA_ADDR)).unwrap();
            mem.write_obj(0xff_u8, GuestAddress(STATUS_ADDR)).unwrap();

            let ring_slot = usize::from(*avail_idx % 16);
            ctrl_gq.avail.ring[ring_slot].set(0);
            *avail_idx = avail_idx.wrapping_add(1);
            ctrl_gq.avail.idx.set(*avail_idx);

            ctrl_evt_kick.write(1).unwrap();
            while ctrl_gq.used.idx.get() != *avail_idx {
                ctrl_done_rx.recv_timeout(Duration::from_secs(5)).unwrap();
            }

            mem.read_obj::<u8>(GuestAddress(STATUS_ADDR)).unwrap()
        };

        // 2. Request 2 queue pairs -> enables all 4 vrings before returning VIRTIO_NET_OK.
        assert_eq!(send_mq_cmd(2, &mut avail_idx), VIRTIO_NET_OK as u8);
        assert_eq!(
            recv_four(&vring_enable_rx),
            vec![(0, true), (1, true), (2, true), (3, true)]
        );
        assert_eq!(net.state().unwrap().curr_queue_pairs, Some(2));

        // 3. Request 1 queue pair -> disables vrings 2 and 3 before returning VIRTIO_NET_OK.
        assert_eq!(send_mq_cmd(1, &mut avail_idx), VIRTIO_NET_OK as u8);
        assert_eq!(
            recv_four(&vring_enable_rx),
            vec![(0, true), (1, true), (2, false), (3, false)]
        );
        assert_eq!(net.state().unwrap().curr_queue_pairs, Some(1));

        // 4. Out-of-range request (3 > max_virtqueue_pairs=2) is rejected without touching vrings.
        assert_eq!(send_mq_cmd(3, &mut avail_idx), VIRTIO_NET_ERR as u8);
        vring_enable_rx.try_recv().unwrap_err();
        assert_eq!(net.state().unwrap().curr_queue_pairs, Some(1));

        // 5. Pause disables all vrings; resume re-enables only the active pair (vrings 0, 1).
        net.pause().unwrap();
        assert_eq!(
            recv_four(&vring_enable_rx),
            vec![(0, false), (1, false), (2, false), (3, false)]
        );
        net.resume().unwrap();
        assert_eq!(
            recv_four(&vring_enable_rx),
            vec![(0, true), (1, true), (2, false), (3, false)]
        );

        // 6. Reset disables all vrings and resets curr_queue_pairs back to 1.
        assert_eq!(send_mq_cmd(2, &mut avail_idx), VIRTIO_NET_OK as u8);
        assert_eq!(
            recv_four(&vring_enable_rx),
            vec![(0, true), (1, true), (2, true), (3, true)]
        );
        net.reset();
        assert_eq!(
            recv_four(&vring_enable_rx),
            vec![(0, false), (1, false), (2, false), (3, false)]
        );
        assert_eq!(net.state().unwrap().curr_queue_pairs, Some(1));

        drop(net);
        backend.join().unwrap();
    }
}
