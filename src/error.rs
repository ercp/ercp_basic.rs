// TODO: Documentation

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Error {
    IoError(IoError),
    FrameError(FrameError),
    CommandError(CommandError),
    BufferError(BufferError),
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
