// TODO: Documentation
// TODO: Use the global Error type only for fatal errors that the direct user
// would propagate.
// TODO: Use function-specific errors for errors to be handled by the direct
// user.

#[cfg(any(feature = "std", test))]
use std::string::FromUtf8Error;

#[derive(Clone, Debug, PartialEq)]
pub enum Error {
    IoError(IoError),
    FrameError(FrameError),
    CommandError(CommandError),
    BufferError(BufferError),

    #[cfg(any(feature = "std", test))]
    FromUtf8Error(FromUtf8Error),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum IoError {
    IoError,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum FrameError {
    TooLong,
    InvalidCrc,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum CommandError {
    UnhandledCommand,
    UnexpectedReply,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BufferError {
    TooShort,
}

impl From<IoError> for Error {
    fn from(io_error: IoError) -> Self {
        Error::IoError(io_error)
    }
}

impl From<FrameError> for Error {
    fn from(frame_error: FrameError) -> Self {
        Error::FrameError(frame_error)
    }
}

impl From<CommandError> for Error {
    fn from(command_error: CommandError) -> Self {
        Error::CommandError(command_error)
    }
}

impl From<BufferError> for Error {
    fn from(buffer_error: BufferError) -> Self {
        Error::BufferError(buffer_error)
    }
}

#[cfg(any(feature = "std", test))]
impl From<FromUtf8Error> for Error {
    fn from(utf8_error: FromUtf8Error) -> Self {
        Error::FromUtf8Error(utf8_error)
    }
}
