// TODO: Module doc.
//! ERCP connection adapter.

#[cfg(feature = "rtt")]
mod rtt;
#[cfg(feature = "serial")]
mod serial;
#[cfg(feature = "serial-host")]
mod serial_host;

#[cfg(feature = "rtt")]
pub use rtt::RttAdapter;
#[cfg(feature = "serial")]
pub use serial::SerialAdapter;
#[cfg(feature = "serial-host")]
pub use serial_host::SerialPortAdapter;

use crate::error::IoError;

/// An ERCP connection adapter.
pub trait Adapter {
    fn read(&mut self) -> Result<Option<u8>, IoError>;
    fn write(&mut self, byte: u8) -> Result<(), IoError>;
}
