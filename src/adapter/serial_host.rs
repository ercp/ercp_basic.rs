use serialport::SerialPort;

use crate::adapter::Adapter;

/// An adapter for [`serialport`].
///
/// This adapter can be used on platform with an OS supported by [`serialport`].
/// It is typically used to instantiate an ERCP Basic driver over a serial port
/// on the host side.
///
/// # Example
///
/// ```no_run
/// use std::time::Duration;
/// use ercp_basic::{adapter::SerialPortAdapter, DefaultRouter, ErcpBasic};
///
/// let port = serialport::new("/dev/ttyUSB0", 115_200)
///     .timeout(Duration::from_millis(10))
///     .open()
///     .unwrap();
///
/// let adapter = SerialPortAdapter::new(port);
/// let ercp: ErcpBasic<_, _, 255> = ErcpBasic::new(adapter, DefaultRouter);
/// ```
#[cfg_attr(docsrs, doc(cfg(feature = "serial-host")))]
pub struct SerialPortAdapter {
    port: Box<dyn SerialPort>,
}

impl Adapter for SerialPortAdapter {
    type Error = ();

    fn read(&mut self) -> Result<Option<u8>, Self::Error> {
        let mut buf = [0; 1];

        match self.port.read(&mut buf) {
            Ok(0) => Ok(None),
            Ok(_) => Ok(Some(buf[0])),
            // TODO: Only for timeout.
            Err(_) => Ok(None),
        }
    }

    fn write(&mut self, byte: u8) -> Result<(), Self::Error> {
        match self.port.write(&[byte]) {
            Ok(1) => Ok(()),
            _ => Err(()),
        }
    }
}

impl SerialPortAdapter {
    /// Instantiates a new [`SerialPort`] adapter.
    pub fn new(port: Box<dyn SerialPort>) -> Self {
        Self { port }
    }

    /// Releases the serial port.
    pub fn release(self) -> Box<dyn SerialPort> {
        self.port
    }
}
