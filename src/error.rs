// Copyright 2021-2022 Jean-Philippe Cugnet
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! ERCP Basic errors.

use crate::command::NewCommandError;
#[cfg(any(feature = "std", test))]
use std::string::FromUtf8Error;

/// An error that can happen when receiving data.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ReceiveError {
    /// An unexpected value has been received during at the init stage.
    UnexpectedValue,
    /// The length is too long.
    TooLong,
    /// The EOT field does not contain EOT.
    NotEot,
    /// Data has been received while a previous command is being processed.
    Overflow,
}

/// An error that can happen on frames.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum FrameError {
    /// The value is too long.
    TooLong,
    /// The received CRC does not match the computed one.
    InvalidCrc,
}

/// An error that can happen on received frames.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ReceivedFrameError {
    /// An unexpected value has been received during at the init stage.
    UnexpectedValue,
    /// The length is too long.
    TooLong,
    /// The EOT field does not contain EOT.
    NotEot,
    /// The received CRC does not match the computed one.
    InvalidCrc,
    /// Data has been received while a previous command is being processed.
    Overflow,
}

/// A system-level error that can happen while sending / receiving a command.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum CommandError<IoError> {
    /// An error has occured while writing or reading data.
    IoError(IoError),
    /// A frame has been received, but it is erroneous.
    ReceivedFrameError(ReceivedFrameError),
    /// The peer has reported an error with the frame it has received.
    SentFrameError(FrameError),
}

/// A typical command result.
pub type CommandResult<T, E, IoError> =
    Result<Result<T, E>, CommandError<IoError>>;

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

impl From<FrameError> for ReceivedFrameError {
    fn from(error: FrameError) -> Self {
        match error {
            FrameError::TooLong => ReceivedFrameError::TooLong,
            FrameError::InvalidCrc => ReceivedFrameError::InvalidCrc,
        }
    }
}

impl From<ReceiveError> for ReceivedFrameError {
    fn from(error: ReceiveError) -> Self {
        match error {
            ReceiveError::UnexpectedValue => {
                ReceivedFrameError::UnexpectedValue
            }
            ReceiveError::TooLong => ReceivedFrameError::TooLong,
            ReceiveError::NotEot => ReceivedFrameError::NotEot,
            ReceiveError::Overflow => ReceivedFrameError::Overflow,
        }
    }
}

#[cfg(any(feature = "std", test))]
impl From<FromUtf8Error> for CommandReturningStringError {
    fn from(error: FromUtf8Error) -> Self {
        Self::FromUtf8Error(error)
    }
}
