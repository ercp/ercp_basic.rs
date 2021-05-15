// TODO: Module doc.
//! ERCP connection adapter.

use crate::error::IoError;

/// An ERCP connection adapter.
pub trait Adapter {
    fn read(&mut self) -> Result<Option<u8>, IoError>;
    fn write(&mut self, byte: u8) -> Result<(), IoError>;
}
