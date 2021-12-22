use probe_rs_rtt::{DownChannel, UpChannel};

use super::Adapter;

/// An adapter for [`probe_rs_rtt`].
///
/// This adapter can be used to instantiate an ERCP Basic driver over RTT
/// channels on the host side.
///
/// *This adapter is currently experimental.*
#[cfg_attr(docsrs, doc(cfg(feature = "rtt-probe-rs")))]
pub struct RttProbeRsAdapter {
    down_channel: DownChannel,
    up_channel: UpChannel,
}

impl Adapter for RttProbeRsAdapter {
    type Error = ();

    fn read(&mut self) -> Result<Option<u8>, Self::Error> {
        let mut buf = [0; 1];

        match self.up_channel.read(&mut buf) {
            Ok(0) => Ok(None),
            Ok(1) => Ok(Some(buf[0])),
            _ => Err(()),
        }
    }

    fn write(&mut self, byte: u8) -> Result<(), Self::Error> {
        match self.down_channel.write(&[byte]) {
            Ok(1) => Ok(()),
            _ => Err(()),
        }
    }
}

impl RttProbeRsAdapter {
    /// Instantiates a new RTT adapter.
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
