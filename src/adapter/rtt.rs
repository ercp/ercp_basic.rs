use rtt_target::{DownChannel, UpChannel};

use super::Adapter;

/// An adapter for [`rtt_target`].
///
/// This adapter can be used to instantiate an ERCP Basic driver over RTT
/// channels on the device side.
///
/// *This adapter is currently experimental.*
#[cfg_attr(docsrs, doc(cfg(feature = "rtt")))]
pub struct RttAdapter {
    down_channel: DownChannel,
    up_channel: UpChannel,
}

impl Adapter for RttAdapter {
    type Error = ();

    fn read(&mut self) -> Result<Option<u8>, Self::Error> {
        let mut buf = [0; 1];

        match self.down_channel.read(&mut buf) {
            0 => Ok(None),
            1 => Ok(Some(buf[0])),
            _ => Err(()),
        }
    }

    fn write(&mut self, byte: u8) -> Result<(), Self::Error> {
        match self.up_channel.write(&[byte]) {
            1 => Ok(()),
            _ => Err(()),
        }
    }
}

impl RttAdapter {
    /// Instantiates an RTT adapter.
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
