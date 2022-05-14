// Copyright 2021 Jean-Philippe Cugnet
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

// TODO: Avoid as u8 since it can be dangerous
//! ERCP Basic command type and values.

use crate::crc::crc;

/// A command.
///
/// Commands are a core concept of ERCP Basic: this is what a device sends,
/// receives and processes. Some commands come built-in, but you can complement
/// them by your own values, provided that they are not in the `0x00..0x1F`
/// range, nor `0xFF`, which are reserved by the specification.
///
/// # Built-in commands
///
/// The ERCP Basic specification comes with [built-in
/// commands](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#built-in-commands).
/// The codes for these commands are defined as constants in the
/// [`command`](`self`) module.
///
/// Macros like [`ack!`] or [`nack!`] are provided to build the corresponding
/// [`Command`] values.
///
/// # Defining application-specific commands
///
/// *TODO: Value, wrapper and handler.*
#[derive(Debug, PartialEq)]
pub struct Command<'a> {
    code: u8,
    value: &'a [u8],
}

/// An error that can happen when building a command.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NewCommandError {
    /// The value of the command is too long.
    TooLong,
}

/// Tests connectivity ([reference](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ping)).
pub const PING: u8 = 0x00;
/// Acknowledgement ([reference](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ack)).
pub const ACK: u8 = 0x01;
/// Negative acknowledgement ([reference](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#nackreason)).
pub const NACK: u8 = 0x02;
/// Resets the device ([reference](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#reset)).
pub const RESET: u8 = 0x03;
/// Gets the protocol version ([reference](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#protocol)).
pub const PROTOCOL: u8 = 0x04;
/// Replies to `PROTOCOL` ([reference](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#protocol_replymajor-minor-patch)).
pub const PROTOCOL_REPLY: u8 = 0x05;
/// Gets the version of a software component ([reference](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#versioncomponent)).
pub const VERSION: u8 = 0x06;
/// Replies to `VERSION` ([reference](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#version_replyversion)).
pub const VERSION_REPLY: u8 = 0x07;
/// Gets the maximum acceptable *Length* ([reference](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#max_length)).
pub const MAX_LENGTH: u8 = 0x08;
/// Replies to `MAX_LENGTH` ([reference](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#max_length_replymax_length)).
pub const MAX_LENGTH_REPLY: u8 = 0x09;
/// Gets the device description ([reference](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#description)).
pub const DESCRIPTION: u8 = 0x10;
/// Replies to `DESCRIPTION` ([reference](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#description_replydescription)).
pub const DESCRIPTION_REPLY: u8 = 0x11;
/// Logs a message ([reference](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#logmessage)).
pub const LOG: u8 = 0xFF;

/// Reasons for the [`Nack(reason)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#nackreason) command.
///
/// Constants in this modules are the values required by the specification. You
/// can complement them by your own values, provided that they are not in the
/// `0x00..0x0F` range, which is reserved by the specification.
pub mod nack_reason {
    /// No specified reason.
    pub const NO_REASON: u8 = 0x00;
    /// The length is above `MAX_LEN`.
    pub const TOO_LONG: u8 = 0x01;
    /// The received CRC is invalid.
    pub const INVALID_CRC: u8 = 0x02;
    /// The command is unknown.
    pub const UNKNOWN_COMMAND: u8 = 0x03;
    /// Arguments provided to the command are invalid.
    pub const INVALID_ARGUMENTS: u8 = 0x04;
}

/// Compoments to be used for the [`Version(component)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#versioncomponent) command.
///
/// Constants in this modules are the values required by the specification. You
/// can complement them by your own values, provided that they are not in the
/// `0x00..0x0F` range, which is reserved by the specification.
pub mod component {
    /// The firmware itself.
    pub const FIRMWARE: u8 = 0x00;
    /// The ERCP Basic library.
    pub const ERCP_LIBRARY: u8 = 0x01;
}

impl<'a> Command<'a> {
    /// Builds a command.
    ///
    /// As the length is encoded on 8 bits in ERCP Basic frames, the length of
    /// `value` cannot be greater than 255. Trying to build a command with a
    /// value longer than that results in a [`NewCommandError`].
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::command::{nack_reason, Command, NACK};
    ///
    /// let result = Command::new(NACK, &[nack_reason::NO_REASON]);
    /// assert!(result.is_ok());
    /// ```
    pub fn new(code: u8, value: &'a [u8]) -> Result<Self, NewCommandError> {
        if value.len() <= u8::MAX.into() {
            Ok(Self { code, value })
        } else {
            Err(NewCommandError::TooLong)
        }
    }

    /// Returns a [`Ping()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ping) command.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::command::{Command, PING};
    ///
    /// assert_eq!(
    ///     Command::ping(),
    ///     Command::new(PING, &[]).unwrap()
    /// );
    /// ```
    pub fn ping() -> Self {
        Self {
            code: PING,
            value: &[],
        }
    }

    /// Returns an [`Ack()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ack) command.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::command::{Command, ACK};
    ///
    /// assert_eq!(
    ///     Command::ack(),
    ///     Command::new(ACK, &[]).unwrap()
    /// );
    /// ```
    pub fn ack() -> Self {
        Self {
            code: ACK,
            value: &[],
        }
    }

    /// Returns a [`Reset()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#reset) command.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::command::{Command, RESET};
    ///
    /// assert_eq!(
    ///     Command::reset(),
    ///     Command::new(RESET, &[]).unwrap()
    /// );
    /// ```
    pub fn reset() -> Self {
        Self {
            code: RESET,
            value: &[],
        }
    }

    /// Returns a [`Protocol()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#protocol) command.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::command::{Command, PROTOCOL};
    ///
    /// assert_eq!(
    ///     Command::protocol(),
    ///     Command::new(PROTOCOL, &[]).unwrap()
    /// );
    /// ```
    pub fn protocol() -> Self {
        Self {
            code: PROTOCOL,
            value: &[],
        }
    }

    /// Returns a [`Version_Reply(version)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#version_replyversion) command.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::command::{Command, VERSION_REPLY};
    ///
    /// assert_eq!(
    ///     Command::version_reply("0.1.0"),
    ///     Command::new(VERSION_REPLY, "0.1.0".as_bytes())
    /// );
    /// ```
    pub fn version_reply(version: &'a str) -> Result<Self, NewCommandError> {
        Self::new(VERSION_REPLY, version.as_bytes())
    }

    /// Returns a [`Max_Length()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#max_length) command.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::command::{Command, MAX_LENGTH};
    ///
    /// assert_eq!(
    ///     Command::max_length(),
    ///     Command::new(MAX_LENGTH, &[]).unwrap()
    /// );
    /// ```
    pub fn max_length() -> Self {
        Self {
            code: MAX_LENGTH,
            value: &[],
        }
    }

    /// Returns a [`Description()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#description) command.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::command::{Command, DESCRIPTION};
    ///
    /// assert_eq!(
    ///     Command::description(),
    ///     Command::new(DESCRIPTION, &[]).unwrap()
    /// );
    /// ```
    pub fn description() -> Self {
        Self {
            code: DESCRIPTION,
            value: &[],
        }
    }

    /// Returns a [`Description_Reply(description)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#description_replydescription) command.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::command::{Command, DESCRIPTION_REPLY};
    ///
    /// assert_eq!(
    ///     Command::description_reply("Example description"),
    ///     Command::new(DESCRIPTION_REPLY, "Example description".as_bytes())
    /// );
    /// ```
    pub fn description_reply(
        description: &'a str,
    ) -> Result<Self, NewCommandError> {
        Self::new(DESCRIPTION_REPLY, description.as_bytes())
    }

    /// Returns a [`Log(message)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#logmessage) command.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::command::{Command, LOG};
    ///
    /// assert_eq!(
    ///     Command::log("Some message"),
    ///     Command::new(LOG, "Some message".as_bytes())
    /// );
    /// ```
    pub fn log(message: &'a str) -> Result<Self, NewCommandError> {
        Self::new(LOG, message.as_bytes())
    }

    /// Returns the code of the command.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::command::{Command, DESCRIPTION_REPLY};
    ///
    /// let reply = Command::description_reply("Description").unwrap();
    /// assert_eq!(reply.code(), DESCRIPTION_REPLY);
    /// ```
    pub fn code(&self) -> u8 {
        self.code
    }

    /// Returns the length of the value.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::command::Command;
    ///
    /// let reply = Command::description_reply("Description").unwrap();
    /// assert_eq!(reply.length(), 11);
    /// ```
    pub fn length(&self) -> u8 {
        self.value.len() as u8
    }

    /// Returns the value of the command.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::command::Command;
    ///
    /// let reply = Command::description_reply("Description").unwrap();
    /// assert_eq!(reply.value(), "Description".as_bytes());
    /// ```
    pub fn value(&self) -> &[u8] {
        self.value
    }

    /// Returns the CRC of the command.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::command::Command;
    ///
    /// let reply = Command::description_reply("Description").unwrap();
    /// assert_eq!(reply.crc(), 0xE2);
    /// ```
    pub fn crc(&self) -> u8 {
        crc(self.code, self.value)
    }

    #[cfg(test)]
    pub(crate) fn as_frame(&self) -> Vec<u8> {
        let mut frame = vec![b'E', b'R', b'C', b'P', b'B'];
        frame.push(self.code());
        frame.push(self.length());
        frame.extend(self.value());
        frame.push(self.crc());
        frame.push(crate::EOT);

        frame
    }
}

/// Builds a [`Ping()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ping) command.
///
/// # Example
///
/// ```
/// use ercp_basic::{
///     command::{Command, PING},
///     ping,
/// };
///
/// let ping = ping!();
/// assert_eq!(ping, Command::new(PING, &[]).unwrap());
/// ```
#[macro_export]
macro_rules! ping {
    () => {
        $crate::command::Command::ping()
    };
}

/// Builds an [`Ack()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ack) command.
///
/// # Example
///
/// ```
/// use ercp_basic::{
///     ack,
///     command::{Command, ACK},
/// };
///
/// let ack = ack!();
/// assert_eq!(ack, Command::new(ACK, &[]).unwrap());
/// ```
#[macro_export]
macro_rules! ack {
    () => {
        $crate::command::Command::ack()
    };
}

/// Builds a [`Nack(reason)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#nackreason) command.
///
/// # Example
///
/// ```
/// use ercp_basic::{
///     command::{nack_reason, Command, NACK},
///     nack,
/// };
///
/// let nack = nack!(nack_reason::NO_REASON);
/// assert_eq!(nack, Command::new(NACK, &[nack_reason::NO_REASON]).unwrap());
/// ```
#[macro_export]
macro_rules! nack {
    ($reason:expr) => {
        $crate::command::Command::new($crate::command::NACK, &[$reason])
            .unwrap()
    };
}

/// Builds a [`Reset()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#reset) command.
///
/// # Example
///
/// ```
/// use ercp_basic::{
///     command::{Command, RESET},
///     reset,
/// };
///
/// let reset = reset!();
/// assert_eq!(reset, Command::new(RESET, &[]).unwrap());
/// ```
#[macro_export]
macro_rules! reset {
    () => {
        $crate::command::Command::reset()
    };
}

/// Builds a [`Protocol()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#protocol) command.
///
/// # Example
///
/// ```
/// use ercp_basic::{
///     command::{Command, PROTOCOL},
///     protocol,
/// };
///
/// let protocol = protocol!();
/// assert_eq!(protocol, Command::new(PROTOCOL, &[]).unwrap());
/// ```
#[macro_export]
macro_rules! protocol {
    () => {
        $crate::command::Command::protocol()
    };
}

/// Builds a [`Protocol_Reply(major, minor, patch)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#protocol_replymajor-minor-patch) command.
///
/// # Example
///
/// ```
/// use ercp_basic::{
///     command::{Command, PROTOCOL_REPLY},
///     protocol_reply,
///     version::Version,
/// };
///
/// let protocol_reply = protocol_reply!(Version { major: 0, minor: 1, patch: 0 });
/// assert_eq!(protocol_reply, Command::new(PROTOCOL_REPLY, &[0, 1, 0]).unwrap());
/// ```
#[macro_export]
macro_rules! protocol_reply {
    ($version:expr) => {
        $crate::command::Command::new(
            $crate::command::PROTOCOL_REPLY,
            &[$version.major, $version.minor, $version.patch],
        )
        .unwrap()
    };
}

/// Builds a [`Version(component)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#versioncomponent) command.
///
/// # Example
///
/// ```
/// use ercp_basic::{
///     command::{component, Command, VERSION},
///     version,
/// };
///
/// let version = version!(component::FIRMWARE);
/// assert_eq!(version, Command::new(VERSION, &[component::FIRMWARE]).unwrap());
/// ```
#[macro_export]
macro_rules! version {
    ($component:expr) => {
        $crate::command::Command::new($crate::command::VERSION, &[$component])
            .unwrap()
    };
}

/// Builds a [`Version_Reply(version)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#version_replyversion) command.
///
/// # Example
///
/// ```
/// use ercp_basic::{
///     command::{component, Command, VERSION_REPLY},
///     version_reply,
/// };
///
/// let version_reply = version_reply!("0.1.0");
/// assert_eq!(version_reply, Command::new(VERSION_REPLY, "0.1.0".as_bytes()).unwrap());
/// ```
#[macro_export]
macro_rules! version_reply {
    ($version:expr) => {
        $crate::command::Command::version_reply($version).unwrap()
    };
}

/// Builds a [`Max_Length()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#max_length) command.
///
/// # Example
///
/// ```
/// use ercp_basic::{
///     command::{component, Command, MAX_LENGTH},
///     max_length,
/// };
///
/// let max_length = max_length!();
/// assert_eq!(max_length, Command::new(MAX_LENGTH, &[]).unwrap());
/// ```
#[macro_export]
macro_rules! max_length {
    () => {
        $crate::command::Command::max_length()
    };
}

/// Builds a [`Max_Length_Reply(max_length)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#max_length_replymax_length) command.
///
/// # Example
///
/// ```
/// use ercp_basic::{
///     command::{component, Command, MAX_LENGTH_REPLY},
///     max_length_reply,
/// };
///
/// let max_length_reply = max_length_reply!(50);
/// assert_eq!(max_length_reply, Command::new(MAX_LENGTH_REPLY, &[50]).unwrap());
/// ```
#[macro_export]
macro_rules! max_length_reply {
    ($max_length:expr) => {
        $crate::command::Command::new(
            $crate::command::MAX_LENGTH_REPLY,
            &[$max_length],
        )
        .unwrap()
    };
}

/// Builds a [`Description()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#description) command.
///
/// # Example
///
/// ```
/// use ercp_basic::{
///     command::{component, Command, DESCRIPTION},
///     description,
/// };
///
/// let description = description!();
/// assert_eq!(description, Command::new(DESCRIPTION, &[]).unwrap());
#[macro_export]
macro_rules! description {
    () => {
        $crate::command::Command::description()
    };
}

/// Builds a [`Description_Reply(description)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#description_replydescription) command.
///
/// # Example
///
/// ```
/// use ercp_basic::{
///     command::{component, Command, DESCRIPTION_REPLY},
///     description_reply,
/// };
///
/// let description_reply = description_reply!("Example description");
/// assert_eq!(
///     description_reply,
///     Command::new(DESCRIPTION_REPLY, "Example description".as_bytes()).unwrap()
/// );
/// ```
#[macro_export]
macro_rules! description_reply {
    ($description:expr) => {
        $crate::command::Command::description_reply($description).unwrap()
    };
}

#[cfg(test)]
mod test {
    use super::*;
    use proptest::collection::vec;
    use proptest::num::u8;
    use proptest::prelude::*;

    ///////////////////////////// Constructors /////////////////////////////

    proptest! {
        #[test]
        fn new_returns_a_command(
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize)
        ) {
            let expected = Command {
                code,
                value: &value,
            };

            assert_eq!(Command::new(code, &value), Ok(expected));
        }
    }

    proptest! {
        #[test]
        fn new_returns_an_error_if_value_is_too_long(
            code in u8::ANY,
            value in vec(u8::ANY, (u8::MAX as usize + 1)..1000)
        ) {
            assert_eq!(Command::new(code, &value), Err(NewCommandError::TooLong))
        }
    }

    /////////////////////////////// Getters ////////////////////////////////

    proptest! {
        #[test]
        fn code_returns_the_code(code in u8::ANY) {
            let command = Command {
                code,
                value: &[],
            };

            assert_eq!(command.code(), command.code);
        }
    }

    proptest! {
        #[test]
        fn value_returns_the_value(
            value in vec(u8::ANY, 0..=u8::MAX as usize),
        ) {
            let command = Command {
                code: 0x00,
                value: &value,
            };

            assert_eq!(command.value(), command.value);
        }
    }

    proptest! {
        #[test]
        fn length_returns_the_value_length(
            value in vec(u8::ANY, 0..=u8::MAX as usize),
        ) {
            let command = Command {
                code: 0x00,
                value: &value,
            };

            assert_eq!(command.length() as usize, command.value.len());
        }
    }

    proptest! {
        #[test]
        fn crc_returns_the_crc(
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize),
        ) {
            let command = Command {
                code,
                value: &value,
            };

            assert_eq!(command.crc(), crc(code, &value));
        }
    }
}
