// TODO: Module doc.
//! ERCP connection adapter.

#[cfg(feature = "embedded")]
mod embedded;

#[cfg(feature = "host")]
mod host;

#[cfg(feature = "embedded")]
pub use embedded::SerialAdapter;

#[cfg(feature = "host")]
pub use host::SerialPortAdapter;

use crate::error::IoError;

/// An ERCP connection adapter.
pub trait Adapter {
    fn read(&mut self) -> Result<Option<u8>, IoError>;
    fn write(&mut self, byte: u8) -> Result<(), IoError>;
}
