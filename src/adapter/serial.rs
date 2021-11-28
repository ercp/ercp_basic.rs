use embedded_hal::serial::{Read, Write};
use nb::block;

use super::Adapter;
use crate::error::IoError;

/// An adapter for [`embedded_hal::serial`].
///
/// This adapter can be used on any platform implementing
/// [`embedded_hal::serial`]. It is typically used to instantiate an ERCP Basic
/// driver over a USART link on embedded devices.
///
///
/// # Example
///
/// ```
/// # pub mod hal {
/// #   pub mod serial {
/// #       use embedded_hal::serial::{Read, Write};
/// #
/// #       pub struct Serial;
/// #
/// #       impl Serial { pub fn new() -> Self { Self } }
/// #
/// #       impl Read<u8> for Serial {
/// #           type Error = ();
/// #           fn read(&mut self) -> nb::Result<u8, ()> { Ok(0) }
/// #       }
/// #
/// #       impl Write<u8> for Serial {
/// #           type Error = ();
/// #           fn write(&mut self, _: u8) -> nb::Result<(), ()> { Ok(()) }
/// #           fn flush(&mut self) -> nb::Result<(), ()> { Ok(()) }
/// #       }
/// #   }
/// # }
/// #
/// use hal::serial::Serial; // Typical embedded_hal::serial implementation.
/// use ercp_basic::{adapter::SerialAdapter, DefaultRouter, ErcpBasic};
///
/// let serial = Serial::new(/* parameters omitted */);
/// let adapter = SerialAdapter::new(serial);
/// let ercp: ErcpBasic<_, _, 255> = ErcpBasic::new(adapter, DefaultRouter);
/// ```
#[cfg_attr(docsrs, doc(cfg(feature = "serial")))]
pub struct SerialAdapter<S: Read<u8> + Write<u8>> {
    serial: S,
}

impl<S: Read<u8> + Write<u8>> Adapter for SerialAdapter<S> {
    fn read(&mut self) -> Result<Option<u8>, IoError> {
        // TODO: Handle errors.
        let result = self.serial.read().ok();
        Ok(result)
    }

    fn write(&mut self, byte: u8) -> Result<(), IoError> {
        block!(self.serial.write(byte)).map_err(|_| IoError::IoError)
    }
}

impl<S: Read<u8> + Write<u8>> SerialAdapter<S> {
    /// Instantiates a serial adapter.
    pub fn new(serial: S) -> Self {
        Self { serial }
    }

    /// Releases the serial port.
    pub fn release(self) -> S {
        self.serial
    }
}
