use probe_rs_rtt::{DownChannel, UpChannel};

use super::Adapter;
use crate::error::IoError;

#[cfg_attr(docsrs, doc(cfg(feature = "rtt-probe-rs")))]
pub struct RttProbeRsAdapter {
    down_channel: DownChannel,
    up_channel: UpChannel,
}

impl Adapter for RttProbeRsAdapter {
    fn read(&mut self) -> Result<Option<u8>, IoError> {
        let mut buf = [0; 1];

        match self.up_channel.read(&mut buf) {
            Ok(0) => Ok(None),
            Ok(1) => Ok(Some(buf[0])),
            _ => Err(IoError::IoError),
        }
    }

    fn write(&mut self, byte: u8) -> Result<(), IoError> {
        match self.down_channel.write(&[byte]) {
            Ok(1) => Ok(()),
            _ => Err(IoError::IoError),
        }
    }
}

impl RttProbeRsAdapter {
    /// Creates a new RTT adapter.
    pub fn new(down_channel: DownChannel, up_channel: UpChannel) -> Self {
        Self {
            down_channel,
            up_channel,
        }
    }

    /// Releases the RTT channels.
    pub fn release(self) -> (DownChannel, UpChannel) {
        (self.down_channel, self.up_channel)
    }
}
