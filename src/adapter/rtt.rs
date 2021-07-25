use rtt_target::{DownChannel, UpChannel};

use super::Adapter;
use crate::error::IoError;

pub struct RttAdapter {
    down_channel: DownChannel,
    up_channel: UpChannel,
}

impl Adapter for RttAdapter {
    fn read(&mut self) -> Result<Option<u8>, IoError> {
        let mut buf = [0; 1];

        match self.down_channel.read(&mut buf) {
            0 => Ok(None),
            1 => Ok(Some(buf[0])),
            _ => Err(IoError::IoError),
        }
    }

    fn write(&mut self, byte: u8) -> Result<(), IoError> {
        match self.up_channel.write(&[byte]) {
            1 => Ok(()),
            _ => Err(IoError::IoError),
        }
    }
}

impl RttAdapter {
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
