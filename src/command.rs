// TODO: Avoid as u8 since it can be dangerous
//! ERCP Basic command type and values.

use crate::crc::crc;
use crate::error::FrameError;

/// A command.
///
/// Commands are a core concept of ERCP Basic: this is what a device sends,
/// receives and processes. Some commands come built-in, but you can complement
/// them by your own values, provided that they are not in the `0x00..0x1F`
/// range, which is reserved by the specification.
#[derive(Debug, PartialEq)]
pub struct Command<'a> {
    command: u8,
    value: &'a [u8],
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

/// Reasons for the [`Nack(reason)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#nackreason)
/// command.
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
    /// value longer than that results in a [`FrameError`].
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::command::{nack_reason, Command, NACK};
    ///
    /// let result = Command::new(NACK, &[nack_reason::NO_REASON]);
    /// assert!(result.is_ok());
    /// ```
    pub fn new(command: u8, value: &'a [u8]) -> Result<Self, FrameError> {
        if value.len() <= u8::MAX.into() {
            Ok(Self { command, value })
        } else {
            Err(FrameError::TooLong)
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
            command: PING,
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
            command: ACK,
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
            command: RESET,
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
            command: PROTOCOL,
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
    pub fn version_reply(version: &'a str) -> Result<Self, FrameError> {
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
            command: MAX_LENGTH,
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
            command: DESCRIPTION,
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
    pub fn description_reply(description: &'a str) -> Result<Self, FrameError> {
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
    pub fn log(message: &'a str) -> Result<Self, FrameError> {
        Self::new(LOG, message.as_bytes())
    }

    /// Returns the opcode of the command.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::command::{Command, DESCRIPTION_REPLY};
    ///
    /// let reply = Command::description_reply("Description").unwrap();
    /// assert_eq!(reply.command(), DESCRIPTION_REPLY);
    /// ```
    pub fn command(&self) -> u8 {
        self.command
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
        crc(self.command, self.value)
    }

    #[cfg(test)]
    pub(crate) fn as_frame(&self) -> Vec<u8> {
        let mut frame = vec![b'E', b'R', b'C', b'P', b'B'];
        frame.push(self.command());
        frame.push(self.length());
        frame.extend(self.value());
        frame.push(self.crc());
        frame.push(crate::EOT);

        frame
    }
}

#[macro_export]
macro_rules! ping {
    () => {
        $crate::command::Command::ping()
    };
}

#[macro_export]
macro_rules! ack {
    () => {
        $crate::command::Command::ack()
    };
}

#[macro_export]
macro_rules! nack {
    ($reason:expr) => {
        $crate::command::Command::new($crate::command::NACK, &[$reason])
            .unwrap()
    };
}

#[macro_export]
macro_rules! reset {
    () => {
        $crate::command::Command::reset()
    };
}

#[macro_export]
macro_rules! protocol {
    () => {
        $crate::command::Command::protocol()
    };
}

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

#[macro_export]
macro_rules! version {
    ($component:expr) => {
        $crate::command::Command::new($crate::command::VERSION, &[$component])
            .unwrap()
    };
}

#[macro_export]
macro_rules! version_reply {
    ($version:expr) => {
        $crate::command::Command::version_reply($version).unwrap()
    };
}

#[macro_export]
macro_rules! max_length {
    () => {
        $crate::command::Command::max_length()
    };
}

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

#[macro_export]
macro_rules! description {
    () => {
        $crate::command::Command::description()
    };
}

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
    use proptest::prelude::*;

    ///////////////////////////// Constructors /////////////////////////////

    proptest! {
        #[test]
        fn new_returns_a_command(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize)
        ) {
            let expected = Command {
                command,
                value: &value,
            };

            assert_eq!(Command::new(command, &value), Ok(expected));
        }
    }

    proptest! {
        #[test]
        fn new_returns_an_error_if_value_is_too_long(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, (u8::MAX as usize + 1)..1000)
        ) {
            assert_eq!(Command::new(command, &value), Err(FrameError::TooLong))
        }
    }

    /////////////////////////////// Getters ////////////////////////////////

    proptest! {
        #[test]
        fn command_returns_the_command(command in 0..=u8::MAX) {
            let command = Command {
                command,
                value: &[],
            };

            assert_eq!(command.command(), command.command);
        }
    }

    proptest! {
        #[test]
        fn value_returns_the_value(
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            let command = Command {
                command: 0x00,
                value: &value,
            };

            assert_eq!(command.value(), command.value);
        }
    }

    proptest! {
        #[test]
        fn length_returns_the_value_length(
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            let command = Command {
                command: 0x00,
                value: &value,
            };

            assert_eq!(command.length() as usize, command.value.len());
        }
    }

    proptest! {
        #[test]
        fn crc_returns_the_crc(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            let cmd = Command {
                command,
                value: &value,
            };

            assert_eq!(cmd.crc(), crc(command, &value));
        }
    }
}
