// TODO: Module doc.

use serialport::SerialPort;

use crate::adapter::Adapter;
use crate::error::IoError;

pub struct SerialPortAdapter {
    port: Box<dyn SerialPort>,
}

impl Adapter for SerialPortAdapter {
    fn read(&mut self) -> Result<Option<u8>, IoError> {
        let mut buf = [0; 1];

        match self.port.read(&mut buf) {
            Ok(0) => Ok(None),
            Ok(_) => Ok(Some(buf[0])),
            // TODO: Only for timeout.
            Err(_) => Ok(None),
        }
    }

    fn write(&mut self, byte: u8) -> Result<(), IoError> {
        match self.port.write(&[byte]) {
            Ok(1) => Ok(()),
            _ => Err(IoError::IoError),
        }
    }
}

impl SerialPortAdapter {
    /// Creates a new SerialPort adapter.
    pub fn new(port: Box<dyn SerialPort>) -> Self {
        Self { port }
    }

    /// Releases the serial port.
    pub fn release(self) -> Box<dyn SerialPort> {
        self.port
    }
}
