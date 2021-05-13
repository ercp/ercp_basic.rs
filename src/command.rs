// TODO: Better documentation.
// TODO: Avoid as u8 since it can be dangerous
//! ERCP command type and values.

use crate::crc::crc;
use crate::error::Error;

#[derive(Debug, PartialEq)]
pub struct Command<'a> {
    command: u8,
    value: &'a [u8],
}

pub const PING: u8 = 0x00;
pub const ACK: u8 = 0x01;
pub const NACK: u8 = 0x02;

pub mod nack_reason {
    pub const NO_REASON: u8 = 0x00;
    pub const TOO_LONG: u8 = 0x01;
    pub const INVALID_CRC: u8 = 0x02;
    pub const UNKNOWN_COMMAND: u8 = 0x03;
    pub const INVALID_ARGUMENTS: u8 = 0x04;
}

impl<'a> Command<'a> {
    pub fn new(command: u8, value: &'a [u8]) -> Result<Self, Error> {
        if value.len() <= u8::MAX.into() {
            Ok(Self { command, value })
        } else {
            Err(Error::TooLong)
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
            assert_eq!(Command::new(command, &value), Err(Error::TooLong))
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
