//! ERCP Basic errors.

use crate::command::NewCommandError;
#[cfg(any(feature = "std", test))]
use std::string::FromUtf8Error;

// TODO: Replace with an adapter-specific error.
/// An error that can happen on connection I/O.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum IoError {
    /// An error has occured while writing or reading data.
    IoError,
}

/// An error that can happen on frames.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum FrameError {
    /// The value is too long.
    TooLong,
    /// The received CRC does not match the computed one.
    InvalidCrc,
}

/// A system-level error that can happen while sending / receiving a command.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum CommandError {
    /// An error has occured while writing or reading data.
    IoError(IoError),
    /// A frame has been received, but it is erroneous.
    ReceivedFrameError(FrameError),
}

/// A typical command result.
pub type CommandResult<T, E> = Result<Result<T, E>, CommandError>;

/// The minimal protocol-level error that can happen on commands.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum GenericCommandError {
    /// The received reply is unexpected.
    UnexpectedReply,
}

/// A generic error that can happen on commands with a return buffer.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum CommandWithBufferError {
    /// The received reply is unexpected.
    UnexpectedReply,
    /// The buffer is too short to hold the received content.
    BufferTooShort,
}

/// A generic error that can happen on commands returning a [`String`].
#[cfg(any(feature = "std", test))]
#[derive(Clone, Debug, PartialEq)]
pub enum CommandReturningStringError {
    /// The received reply is unexpected.
    UnexpectedReply,
    /// The received string is not valid UTF-8.
    FromUtf8Error(FromUtf8Error),
}

/// An error that can happen on ping commands.
pub type PingError = GenericCommandError;
/// An error that can happen on protocol commands.
pub type ProtocolError = GenericCommandError;
/// An error that can happen on max_length commands.
pub type MaxLengthError = GenericCommandError;
/// An error that can happen on version commands.
pub type VersionError = CommandWithBufferError;
/// An error that can happen on description commands.
pub type DescriptionError = CommandWithBufferError;

#[cfg(any(feature = "std", test))]
/// An erro that can happen on version_as_string commands.
pub type VersionAsStringError = CommandReturningStringError;
#[cfg(any(feature = "std", test))]
/// An erro that can happen on description_as_string commands.
pub type DescriptionAsStringError = CommandReturningStringError;

/// An error that can happen on reset commands.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ResetError {
    /// The received reply is unexpected.
    UnexpectedReply,
    /// The Reset command is unhandled on the peer device.
    UnhandledCommand,
}

/// An error that can happen on log commands or notifications.
#[derive(Clone, Debug, PartialEq)]
pub enum LogError {
    /// The received reply is unexpected.
    UnexpectedReply,
    /// The log message is too long to fin in a frame.
    TooLong,
}

impl From<NewCommandError> for FrameError {
    fn from(error: NewCommandError) -> Self {
        match error {
            NewCommandError::TooLong => FrameError::TooLong,
        }
    }
}

impl From<IoError> for CommandError {
    fn from(error: IoError) -> Self {
        Self::IoError(error)
    }
}

impl From<FrameError> for CommandError {
    fn from(error: FrameError) -> Self {
        Self::ReceivedFrameError(error)
    }
}

#[cfg(any(feature = "std", test))]
impl From<FromUtf8Error> for CommandReturningStringError {
    fn from(error: FromUtf8Error) -> Self {
        Self::FromUtf8Error(error)
    }
}
