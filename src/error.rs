// TODO: Documentation

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Error {
    InvalidCRC,
    TooLong,
    IoError(IoError),

    // TODO: Remove
    OtherError,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum IoError {
    IoError,
}

impl From<IoError> for Error {
    fn from(io_error: IoError) -> Self {
        Error::IoError(io_error)
    }
}
