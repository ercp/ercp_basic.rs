//! ERCP Basic connection adapters.

#[cfg(feature = "rtt")]
mod rtt;
#[cfg(feature = "rtt-probe-rs")]
mod rtt_probe_rs;
#[cfg(feature = "serial")]
mod serial;
#[cfg(feature = "serial-host")]
mod serial_host;

#[cfg(feature = "rtt")]
pub use rtt::RttAdapter;
#[cfg(feature = "rtt-probe-rs")]
pub use rtt_probe_rs::RttProbeRsAdapter;
#[cfg(feature = "serial")]
pub use serial::SerialAdapter;
#[cfg(feature = "serial-host")]
pub use serial_host::SerialPortAdapter;

use crate::error::IoError;

/// An ERCP connection adapter.
///
/// An adapter is the piece of software that makes the link between the ERCP
/// Basic driver and the actual communication medium.
///
/// You can find several built-in adapters in the [`adapter`](`crate::adapter`)
/// module, and you can write your own by implementing the [`Adapter`] trait.
pub trait Adapter {
    // IDEA: Replace IoError with an implementation-defined type.

    /// Reads a byte from the connection.
    ///
    /// This function tries to read a byte from the connection. If a byte is
    /// available, it returns `Ok(Some(value))`. If nothing is available, it
    /// does not block and `Ok(None)` is returned. There is however no guarantee
    /// on the time the actual implementation takes to return a `Ok(None)`.
    ///
    /// # Errors
    ///
    /// Any call to this function may generate an I/O error.
    fn read(&mut self) -> Result<Option<u8>, IoError>;

    /// Writes a byte to the connection.
    ///
    /// This function writes a byte to the connection. It may block, and there
    /// is no guarantee that when it returns the byte has been actually written
    /// on the medium.
    ///
    /// # Errors
    ///
    /// Any call to this function may generate an I/O error.
    fn write(&mut self, byte: u8) -> Result<(), IoError>;
}
