// TODO: Better documentation.
// TODO: Avoid as u8 since it can be dangerous (annote when justified)
//! ERCP Basic framing tools.

use heapless::Vec;

use crate::command::Command;
use crate::error::FrameError;

#[derive(Clone, Debug, Default, PartialEq)]
pub(crate) struct FrameBuffer<const MAX_LEN: usize> {
    code: u8,
    length: u8,
    value: Vec<u8, MAX_LEN>,
    crc: u8,
}

/// An error that can happen when setting the length.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SetLengthError {
    /// The length is bigger than `MAX_LEN`.
    TooLong,
}

/// An error that can happen when pushing a value byte.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum PushValueError {
    /// The value overflows its declared `length`.
    Overflow,
}

impl<const MAX_LEN: usize> FrameBuffer<MAX_LEN> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn reset(&mut self) {
        // TODO: Use zeroize to avoid optimisations.
        *self = Self::default();
    }

    pub fn code(&self) -> u8 {
        self.code
    }

    #[cfg(test)]
    pub fn length(&self) -> u8 {
        self.length
    }

    pub fn value(&self) -> &[u8] {
        self.value.as_slice()
    }

    pub fn crc(&self) -> u8 {
        self.crc
    }

    pub fn set_code(&mut self, code: u8) {
        self.code = code;
    }

    // FIXME: Currently, if we change the length /after/ pushing the value, we
    // can have a length that is inferior to the value size.
    // FIXME: Another issue can come if the buffer is re-used but not zeroed.
    pub fn set_length(&mut self, length: u8) -> Result<(), SetLengthError> {
        if length as usize <= MAX_LEN {
            self.length = length;
            Ok(())
        } else {
            Err(SetLengthError::TooLong)
        }
    }

    pub fn push_value(&mut self, byte: u8) -> Result<(), PushValueError> {
        if self.value.len() < self.length.into() {
            // NOTE: value.len() < length <= MAX_LEN == value.capacity().
            self.value.push(byte).ok();
            Ok(())
        } else {
            Err(PushValueError::Overflow)
        }
    }

    pub fn set_crc(&mut self, crc: u8) {
        self.crc = crc;
    }

    pub fn value_is_complete(&self) -> bool {
        // NOTE: Type inference does not work due to an issue in serde-yaml:
        // https://github.com/dtolnay/serde-yaml/issues/140
        self.value.len() == self.length as usize
    }

    pub fn check_frame(&self) -> Result<Command, FrameError> {
        let command = Command::new(self.code(), self.value())?;

        if self.crc() == command.crc() {
            Ok(command)
        } else {
            Err(FrameError::InvalidCrc)
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::crc::crc;
    use proptest::collection::vec;
    use proptest::prelude::*;

    /////////////////////////////// Strategy ///////////////////////////////

    fn frame_buffer() -> impl Strategy<Value = FrameBuffer<255>> {
        (0..=u8::MAX, vec(0..=u8::MAX, 0..=u8::MAX as usize)).prop_map(
            |(code, value)| FrameBuffer {
                code,
                length: value.len() as u8,
                value: Vec::from_slice(&value).unwrap(),
                crc: crc(code, &value),
            },
        )
    }

    ///////////////////////////// Constructor //////////////////////////////

    #[test]
    fn new_returns_an_empty_frame_buffer() {
        let frame_buffer = FrameBuffer::<255>::new();
        let expected = FrameBuffer {
            code: 0x00,
            length: 0x00,
            value: Vec::new(),
            crc: 0x00,
        };

        assert_eq!(frame_buffer, expected);
    }

    //////////////////////////////// Reset /////////////////////////////////

    #[test]
    fn reset_resets_to_an_empty_frame_buffer() {
        let mut frame_buffer = FrameBuffer::<255> {
            code: 0xAA,
            length: 0x55,
            value: Vec::from_slice(&[0xAA; 0x55]).unwrap(),
            crc: 0xAA,
        };

        let expected = FrameBuffer::<255> {
            code: 0x00,
            length: 0x00,
            value: Vec::new(),
            crc: 0x00,
        };

        frame_buffer.reset();
        assert_eq!(frame_buffer, expected);
    }

    /////////////////////////////// Getters ////////////////////////////////

    proptest! {
        #[test]
        fn code_returns_the_code(frame_buffer in frame_buffer()) {
            assert_eq!(frame_buffer.code(), frame_buffer.code);
        }
    }

    proptest! {
        #[test]
        fn length_returns_the_length(frame_buffer in frame_buffer()) {
            assert_eq!(frame_buffer.length(), frame_buffer.length);
        }
    }

    proptest! {
        #[test]
        fn value_returns_the_value_as_a_slice(frame_buffer in frame_buffer()) {
            assert_eq!(
                frame_buffer.value(),
                frame_buffer.value.as_slice()
            );
        }
    }

    proptest! {
        #[test]
        fn crc_returns_the_crc(frame_buffer in frame_buffer()) {
            assert_eq!(frame_buffer.crc(), frame_buffer.crc);
        }
    }

    /////////////////////////////// Setters ////////////////////////////////

    proptest! {
        #[test]
        fn set_code_sets_the_code(code in 0..=u8::MAX) {
            let mut frame_buffer = FrameBuffer::<255>::new();

            frame_buffer.set_code(code);
            assert_eq!(frame_buffer.code, code);
        }
    }

    proptest! {
        #[test]
        fn set_length_sets_the_length_when_length_is_valid(length in 0..=95u8) {
            let mut frame_buffer = FrameBuffer::<95>::new();

            assert!(frame_buffer.set_length(length).is_ok());
            assert_eq!(frame_buffer.length, length);
        }
    }

    proptest! {
        #[test]
        fn set_length_returns_an_error_when_length_is_too_long(
            length in 96..=u8::MAX
        ) {
            let mut frame_buffer = FrameBuffer::<95>::new();

            assert_eq!(
                frame_buffer.set_length(length),
                Err(SetLengthError::TooLong)
            );
        }
    }

    proptest! {
        #[test]
        fn push_value_pushes_value_in_the_buffer_when_there_is_space(
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize)
        ) {
            let mut frame_buffer = FrameBuffer::<255>::new();
            frame_buffer.set_length(value.len() as u8).unwrap();

            for (i, byte) in value.into_iter().enumerate() {
                assert!(frame_buffer.push_value(byte).is_ok());
                assert_eq!(frame_buffer.value[i], byte);
            }
        }
    }

    proptest! {
        #[test]
        fn push_value_returns_an_error_when_buffer_is_full(
            value in 0..=u8::MAX
        ) {
            let mut frame_buffer = FrameBuffer::<1>::new();
            frame_buffer.set_length(1).unwrap();

            assert!(frame_buffer.push_value(value).is_ok());
            assert_eq!(
                frame_buffer.push_value(value),
                Err(PushValueError::Overflow)
            );
        }
    }

    proptest! {
        #[test]
        fn push_value_returns_an_error_if_value_value_is_complete(
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize - 1),
            next in 0..=u8::MAX
        ) {
            let mut frame_buffer = FrameBuffer::<255>::new();
            frame_buffer.set_length(value.len() as u8).unwrap();

            for byte in value {
                assert!(frame_buffer.push_value(byte).is_ok());
            }

            assert_eq!(
                frame_buffer.push_value(next),
                Err(PushValueError::Overflow)
            );
        }
    }

    proptest! {
        #[test]
        fn set_crc_sets_the_crc(crc in 0..=u8::MAX) {
            let mut frame_buffer = FrameBuffer::<255>::new();
            frame_buffer.set_crc(crc);

            assert_eq!(frame_buffer.crc, crc);
        }
    }

    ///////////////////////////// Frame check //////////////////////////////

    proptest! {
        #[test]
        fn value_is_complete_returns_true_if_all_bytes_have_been_received(
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize)
        ) {
            let mut frame_buffer = FrameBuffer::<255>::new();
            frame_buffer.set_length(value.len() as u8).unwrap();

            for byte in value {
                frame_buffer.push_value(byte).unwrap();
            }

            assert!(frame_buffer.value_is_complete());
        }
    }

    proptest! {
        #[test]
        fn value_is_complete_returns_false_if_not_all_bytes_have_been_received(
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize - 1)
        ) {
            let mut frame_buffer = FrameBuffer::<255>::new();
            frame_buffer.set_length(value.len() as u8 + 1).unwrap();

            for byte in value {
                frame_buffer.push_value(byte).unwrap();
                assert!(!frame_buffer.value_is_complete());
            }
        }
    }

    proptest! {
        #[test]
        fn check_frame_returs_a_command_if_crc_is_valid(
            frame_buffer in frame_buffer()
        ) {
            let command =
                Command::new(frame_buffer.code(), frame_buffer.value())
                    .unwrap();

            assert_eq!(frame_buffer.check_frame(), Ok(command));
        }
    }

    proptest! {
        #[test]
        fn check_frame_returns_an_error_if_crc_is_invalid(
            mut frame_buffer in frame_buffer(),
            bad_crc in 0..=u8::MAX
        ) {
            prop_assume!(
                bad_crc != crc(frame_buffer.code(), frame_buffer.value())
            );

            frame_buffer.set_crc(bad_crc);

            let result = frame_buffer.check_frame();
            assert_eq!(result, Err(FrameError::InvalidCrc));
        }
    }
}
