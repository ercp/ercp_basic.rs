// TODO: Better documentation.
//! ERCP Basic framing tools.

use core::convert::TryInto;

use crate::crc::crc;
use crate::error::Error;

#[derive(Debug, PartialEq)]
pub struct Frame<'a> {
    command: u8,
    length: u8,
    value: &'a [u8],
    crc: u8,
}

impl<'a> Frame<'a> {
    pub fn new(command: u8, value: &'a [u8]) -> Result<Self, Error> {
        let length = value.len().try_into().or(Err(Error::TooLong))?;
        let crc = crc(command, value);

        Ok(Self {
            command,
            length,
            value,
            crc,
        })
    }

    pub fn command(&self) -> u8 {
        self.command
    }

    pub fn length(&self) -> u8 {
        self.length
    }

    pub fn value(&self) -> &[u8] {
        self.value
    }

    pub fn crc(&self) -> u8 {
        self.crc
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use proptest::collection::vec;
    use proptest::prelude::*;

    ///////////////////////////// Constructor //////////////////////////////

    proptest! {
        #[test]
        fn new_returns_a_frame_with_its_length_and_crc(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize)
        ) {
            let expected = Frame {
                command,
                length: value.len() as u8,
                value: &value,
                crc: crc(command, &value),
            };

            assert_eq!(Frame::new(command, &value), Ok(expected));
        }
    }

    proptest! {
        #[test]
        fn new_returns_an_error_if_value_is_too_long(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, (u8::MAX as usize + 1)..1000)
        ) {
            assert_eq!(Frame::new(command, &value), Err(Error::TooLong))
        }
    }

    /////////////////////////////// Getters ////////////////////////////////

    proptest! {
        #[test]
        fn command_returns_the_command(command in 0..=u8::MAX) {
            let frame = Frame {
                command,
                length: 0x00,
                value: &[],
                crc: 0x00,
            };

            assert_eq!(frame.command(), frame.command);
        }
    }

    proptest! {
        #[test]
        fn command_returns_the_length(length in 0..=u8::MAX) {
            let frame = Frame {
                command: 0x00,
                length,
                value: &[],
                crc: 0x00,
            };

            assert_eq!(frame.length(), frame.length);
        }
    }

    proptest! {
        #[test]
        fn value_returns_the_value(
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            let frame = Frame {
                command: 0x00,
                length: 0x00,
                value: &value,
                crc: 0x00,
            };

            assert_eq!(frame.crc(), frame.crc);
        }
    }

    proptest! {
        #[test]
        fn crc_returns_the_crc(crc in 0..=u8::MAX) {
            let frame = Frame {
                command: 0x00,
                length: 0x00,
                value: &[],
                crc,
            };

            assert_eq!(frame.crc(), frame.crc);
        }
    }
}
