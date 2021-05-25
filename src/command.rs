// TODO: Better documentation.
// TODO: Avoid as u8 since it can be dangerous
//! ERCP command type and values.

use crate::crc::crc;
use crate::error::FrameError;

#[derive(Debug, PartialEq)]
pub struct Command<'a> {
    command: u8,
    value: &'a [u8],
}

pub const PING: u8 = 0x00;
pub const ACK: u8 = 0x01;
pub const NACK: u8 = 0x02;
pub const RESET: u8 = 0x03;
pub const PROTOCOL: u8 = 0x04;
pub const PROTOCOL_REPLY: u8 = 0x05;
pub const VERSION: u8 = 0x06;
pub const VERSION_REPLY: u8 = 0x07;
pub const MAX_LENGTH: u8 = 0x08;
pub const MAX_LENGTH_REPLY: u8 = 0x09;
pub const DESCRIPTION: u8 = 0x10;
pub const DESCRIPTION_REPLY: u8 = 0x11;
pub const LOG: u8 = 0xFF;

pub mod nack_reason {
    pub const NO_REASON: u8 = 0x00;
    pub const TOO_LONG: u8 = 0x01;
    pub const INVALID_CRC: u8 = 0x02;
    pub const UNKNOWN_COMMAND: u8 = 0x03;
    pub const INVALID_ARGUMENTS: u8 = 0x04;
}

pub mod component {
    pub const FIRMWARE: u8 = 0x00;
    pub const ERCP_LIBRARY: u8 = 0x01;
}

impl<'a> Command<'a> {
    pub fn new(command: u8, value: &'a [u8]) -> Result<Self, FrameError> {
        if value.len() <= u8::MAX.into() {
            Ok(Self { command, value })
        } else {
            Err(FrameError::TooLong)
        }
    }

    pub fn ping() -> Self {
        Self {
            command: PING,
            value: &[],
        }
    }

    pub fn ack() -> Self {
        Self {
            command: ACK,
            value: &[],
        }
    }

    pub fn reset() -> Self {
        Self {
            command: RESET,
            value: &[],
        }
    }

    pub fn protocol() -> Self {
        Self {
            command: PROTOCOL,
            value: &[],
        }
    }

    pub fn version_reply(version: &'a str) -> Result<Self, FrameError> {
        Self::new(VERSION_REPLY, version.as_bytes())
    }

    pub fn max_length() -> Self {
        Self {
            command: MAX_LENGTH,
            value: &[],
        }
    }

    pub fn description() -> Self {
        Self {
            command: DESCRIPTION,
            value: &[],
        }
    }

    pub fn description_reply(description: &'a str) -> Result<Self, FrameError> {
        Self::new(DESCRIPTION_REPLY, description.as_bytes())
    }

    pub fn log(message: &'a str) -> Result<Self, FrameError> {
        Self::new(LOG, message.as_bytes())
    }

    pub fn command(&self) -> u8 {
        self.command
    }

    pub fn length(&self) -> u8 {
        self.value.len() as u8
    }

    pub fn value(&self) -> &[u8] {
        self.value
    }

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

    #[test]
    fn ping_returns_an_ping() {
        assert_eq!(
            Command::ping(),
            Command {
                command: PING,
                value: &[],
            }
        );
    }

    #[test]
    fn ack_returns_an_ack() {
        assert_eq!(
            Command::ack(),
            Command {
                command: ACK,
                value: &[],
            }
        );
    }

    #[test]
    fn reset_returns_a_reset() {
        assert_eq!(
            Command::reset(),
            Command {
                command: RESET,
                value: &[],
            }
        );
    }

    #[test]
    fn protocol_returns_a_protocol() {
        assert_eq!(
            Command::protocol(),
            Command {
                command: PROTOCOL,
                value: &[],
            }
        );
    }

    proptest! {
        #[test]
        fn version_reply_returns_a_version_reply(
            version in ".{0,100}",
        ) {
            assert_eq!(
                Command::version_reply(&version),
                Ok(Command {
                    command: VERSION_REPLY,
                    value: version.as_bytes(),
                })
            );
        }
    }

    #[test]
    fn max_length_returns_a_max_length() {
        assert_eq!(
            Command::max_length(),
            Command {
                command: MAX_LENGTH,
                value: &[],
            }
        );
    }

    #[test]
    fn description_returns_a_description() {
        assert_eq!(
            Command::description(),
            Command {
                command: DESCRIPTION,
                value: &[],
            }
        );
    }

    proptest! {
        #[test]
        fn description_reply_returns_a_description_reply(
            description in ".{0,100}",
        ) {
            assert_eq!(
                Command::description_reply(&description),
                Ok(Command {
                    command: DESCRIPTION_REPLY,
                    value: description.as_bytes(),
                })
            );
        }
    }

    proptest! {
        #[test]
        fn log_returns_a_log(
            message in ".{0,100}",
        ) {
            assert_eq!(
                Command::log(&message),
                Ok(Command {
                    command: LOG,
                    value: message.as_bytes(),
                })
            );
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
