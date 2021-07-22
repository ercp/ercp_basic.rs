// TODO: Module doc.

use embedded_hal::serial::{Read, Write};
use nb::block;

use super::Adapter;
use crate::error::IoError;

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
    pub fn new(serial: S) -> Self {
        Self { serial }
    }

    pub fn release(self) -> S {
        self.serial
    }
}
