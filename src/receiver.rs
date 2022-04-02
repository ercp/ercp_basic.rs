// Copyright 2022 Jean-Philippe Cugnet
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

//! ERCP Basic receiver.
//!
//! *This is an internal module.*
//!
//! The receiver is the object that handles incoming data and parses it.

pub mod frame_buffer;

use crate::{error::ReceiveError, EOT};
use frame_buffer::{FrameBuffer, SetLengthError};

/// An ERCP Basic receiver.
#[derive(Debug)]
pub(crate) struct Receiver<const MAX_LEN: usize> {
    state: State,
    rx_frame: FrameBuffer<MAX_LEN>,
}

// TODO: Make these internal state machine enums private.

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum State {
    Ready,
    Init(InitState),
    Receiving(Field),
    Complete,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum InitState {
    R,
    C,
    P,
    B,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Field {
    Code,
    Length,
    Value,
    CRC,
    EOT,
}

impl InitState {
    // TODO: Make this private.
    pub const fn next_state(&self) -> State {
        match self {
            InitState::R => State::Init(InitState::C),
            InitState::C => State::Init(InitState::P),
            InitState::P => State::Init(InitState::B),
            InitState::B => State::Receiving(Field::Code),
        }
    }

    const fn value(&self) -> u8 {
        match self {
            InitState::R => b'R',
            InitState::C => b'C',
            InitState::P => b'P',
            InitState::B => b'B',
        }
    }
}

impl<const MAX_LEN: usize> Receiver<MAX_LEN> {
    /// Creates a new receiver.
    pub fn new() -> Self {
        Self {
            state: State::Ready,
            rx_frame: FrameBuffer::new(),
        }
    }

    // TODO: Remove when the interface is clearly defined.
    #[cfg(test)]
    pub fn state(&self) -> State {
        self.state
    }

    // TODO: Remove when the interface is clearly defined.
    #[cfg(test)]
    pub fn set_state(&mut self, state: State) {
        self.state = state
    }

    // TODO: Remove when the interface is clearly defined.
    pub fn rx_frame(&self) -> &FrameBuffer<MAX_LEN> {
        &self.rx_frame
    }

    // TODO: Remove when the interface is clearly defined.
    #[cfg(test)]
    pub fn rx_frame_mut(&mut self) -> &mut FrameBuffer<MAX_LEN> {
        &mut self.rx_frame
    }

    /// Receives a byte.
    pub fn receive(&mut self, byte: u8) -> Result<(), ReceiveError> {
        match self.state {
            State::Ready => {
                if byte == b'E' {
                    self.state = State::Init(InitState::R);
                    Ok(())
                } else {
                    // Ignore unexpected data.
                    Err(ReceiveError::UnexpectedValue)
                }
            }

            State::Init(init_state) => {
                if byte == init_state.value() as u8 {
                    self.state = init_state.next_state();
                    Ok(())
                } else {
                    // Unexpected value => reset.
                    self.state = State::Ready;
                    Err(ReceiveError::UnexpectedValue)
                }
            }

            State::Receiving(field) => match field {
                Field::Code => {
                    self.rx_frame.set_code(byte);
                    self.state = State::Receiving(Field::Length);
                    Ok(())
                }

                Field::Length => match self.rx_frame.set_length(byte) {
                    Ok(()) => {
                        if byte == 0 {
                            // No value field if the length is zero.
                            self.state = State::Receiving(Field::CRC);
                        } else {
                            self.state = State::Receiving(Field::Value);
                        }

                        Ok(())
                    }

                    Err(SetLengthError::TooLong) => {
                        self.reset_state();
                        Err(ReceiveError::TooLong)
                    }
                },

                Field::Value => {
                    // NOTE: The error never occurs since we wait for the CRC
                    // when the value is complete.
                    self.rx_frame.push_value(byte).ok();

                    if self.rx_frame.value_is_complete() {
                        self.state = State::Receiving(Field::CRC);
                    }

                    Ok(())
                }

                Field::CRC => {
                    self.rx_frame.set_crc(byte);
                    self.state = State::Receiving(Field::EOT);
                    Ok(())
                }

                Field::EOT => {
                    if byte == EOT {
                        self.state = State::Complete;
                        Ok(())
                    } else {
                        // Unexpected value => reset.
                        self.reset_state();
                        Err(ReceiveError::NotEot)
                    }
                }
            },

            State::Complete => {
                // Ignore unexpected data.
                Err(ReceiveError::Overflow)
            }
        }
    }

    /// Returns wether a complete frame has been received.
    ///
    /// If it returns `true`, you should then call `process`.
    pub fn complete_frame_received(&self) -> bool {
        self.state == State::Complete
    }

    /// Resets the receive state machine and clears the frame buffer.
    pub fn reset_state(&mut self) {
        self.state = State::Ready;
        self.rx_frame.reset();
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::crc::crc;

    use proptest::collection::vec;
    use proptest::prelude::*;

    /////////////////////////////// Strategy ///////////////////////////////

    prop_compose! {
        pub(crate) fn receiver(
            state: State
        ) (
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize)
        ) -> Receiver<255> {
            let mut receiver = Receiver::new();

            while receiver.state != state {
                match receiver.state {
                    State::Ready => {
                        receiver.state = State::Init(InitState::R);
                    }

                    State::Init(init_state) => {
                        receiver.state = init_state.next_state();
                    }

                    State::Receiving(field) => match field {
                        Field::Code => {
                            receiver.rx_frame.set_code(code);
                            receiver.state = State::Receiving(Field::Length);
                        }

                        Field::Length => {
                            receiver
                                .rx_frame
                                .set_length(value.len() as u8)
                                .unwrap();
                            receiver.state = State::Receiving(Field::Value);
                        }

                        Field::Value => {
                            for &byte in &value {
                                receiver.rx_frame.push_value(byte).unwrap();
                            }

                            receiver.state = State::Receiving(Field::CRC);
                        }

                        Field::CRC => {
                            receiver.rx_frame.set_crc(crc(code, &value));
                            receiver.state = State::Receiving(Field::EOT);
                        }

                        Field::EOT => {
                            receiver.state = State::Complete;
                        }
                    },

                    State::Complete => unreachable!(),
                };
            }

            receiver
        }
    }

    ////////////////////// The receive state machine ///////////////////////

    ///////////////////////////// State::Ready /////////////////////////////

    #[test]
    fn receiver_starts_in_ready_state() {
        let receiver = Receiver::<255>::new();
        assert_eq!(receiver.state, State::Ready);
    }

    proptest! {
        #[test]
        fn receive_returns_an_error_on_random_data(value in 0..=u8::MAX) {
            // 'E' starts a receive sequence, so we do not want it.
            prop_assume!(value != b'E');

            let mut receiver = Receiver::<255>::new();
            assert_eq!(
                receiver.receive(value),
                Err(ReceiveError::UnexpectedValue)
            );
        }
    }

    proptest! {
        #[test]
        fn receive_does_not_advance_on_random_data(value in 0..=u8::MAX) {
            // 'E' starts a receive sequence, so we do not want it.
            prop_assume!(value != b'E');

            let mut receiver = Receiver::<255>::new();
            receiver.receive(value).ok();
            assert_eq!(receiver.state, State::Ready);
        }
    }

    ///////////////////////////// State::Init //////////////////////////////

    #[test]
    fn receive_starts_init_sequence_on_e() {
        let mut receiver = Receiver::<255>::new();
        assert!(receiver.receive(b'E').is_ok());
        assert_eq!(receiver.state, State::Init(InitState::R));
    }

    #[test]
    fn receive_advances_through_the_init_sequence() {
        let mut receiver = Receiver::<255>::new();

        assert!(receiver.receive(b'E').is_ok());
        assert_eq!(receiver.state, State::Init(InitState::R));

        assert!(receiver.receive(b'R').is_ok());
        assert_eq!(receiver.state, State::Init(InitState::C));

        assert!(receiver.receive(b'C').is_ok());
        assert_eq!(receiver.state, State::Init(InitState::P));

        assert!(receiver.receive(b'P').is_ok());
        assert_eq!(receiver.state, State::Init(InitState::B));
    }

    proptest! {
        #[test]
        fn receive_returns_an_error_on_unexpected_sequence(
            num in 0..5,
            value in 0..=u8::MAX,
        ) {
            match num {
                0 => prop_assume!(value != b'E'),
                1 => prop_assume!(value != b'R'),
                2 => prop_assume!(value != b'C'),
                3 => prop_assume!(value != b'P'),
                4 => prop_assume!(value != b'B'),
                _ => ()
            }

            let mut receiver = Receiver::<255>::new();

            if num >= 1 {
                receiver.receive(b'E').ok();
            }
            if num >= 2 {
                receiver.receive(b'R').ok();
            }
            if num >= 3 {
                receiver.receive(b'C').ok();
            }
            if num >= 4 {
                receiver.receive(b'P').ok();
            }

            assert_eq!(
                receiver.receive(value),
                Err(ReceiveError::UnexpectedValue)
            );
        }
    }

    proptest! {
        #[test]
        fn receive_switches_back_to_ready_on_unexpected_sequence(
            num in 0..5,
            value in 0..=u8::MAX,
        ) {
            match num {
                0 => prop_assume!(value != b'E'),
                1 => prop_assume!(value != b'R'),
                2 => prop_assume!(value != b'C'),
                3 => prop_assume!(value != b'P'),
                4 => prop_assume!(value != b'B'),
                _ => ()
            }

            let mut receiver = Receiver::<255>::new();

            if num >= 1 {
                receiver.receive(b'E').ok();
            }
            if num >= 2 {
                receiver.receive(b'R').ok();
            }
            if num >= 3 {
                receiver.receive(b'C').ok();
            }
            if num >= 4 {
                receiver.receive(b'P').ok();
            }

            receiver.receive(value).ok();
            assert_eq!(receiver.state, State::Ready);
        }
    }

    #[test]
    fn receive_waits_for_code_after_init_sequence() {
        let mut receiver = Receiver::<255>::new();
        receiver.receive(b'E').ok();
        receiver.receive(b'R').ok();
        receiver.receive(b'C').ok();
        receiver.receive(b'P').ok();
        receiver.receive(b'B').ok();
        assert_eq!(receiver.state, State::Receiving(Field::Code));
    }

    ///////////////////// State::Receive(Field::Code) //////////////////////

    proptest! {
        #[test]
        fn receive_at_code_stage_returns_ok(
            mut receiver in receiver(State::Receiving(Field::Code)),
            code in 0..=u8::MAX,
        ) {
            assert_eq!(receiver.receive(code), Ok(()));
        }
    }

    proptest! {
        #[test]
        fn receive_at_code_stage_stores_command_code(
            mut receiver in receiver(State::Receiving(Field::Code)),
            code in 0..=u8::MAX,
        ) {
            receiver.receive(code).ok();
            assert_eq!(receiver.rx_frame.code(), code);
        }
    }

    proptest! {
        #[test]
        fn receive_at_code_stage_goes_to_length_stage(
            mut receiver in receiver(State::Receiving(Field::Code)),
            code in 0..=u8::MAX,
        ) {
            receiver.receive(code).ok();
            assert_eq!(receiver.state, State::Receiving(Field::Length));
        }
    }

    //////////////////// State::Receive(Field::Length) /////////////////////

    proptest! {
        #[test]
        fn receive_at_length_stage_returns_ok(
            mut receiver in receiver(State::Receiving(Field::Length)),
            length in 0..=u8::MAX,
        ) {
            assert_eq!(receiver.receive(length), Ok(()));
        }
    }

    proptest! {
        #[test]
        fn receive_at_length_stage_stores_length(
            mut receiver in receiver(State::Receiving(Field::Length)),
            length in 0..=u8::MAX,
        ) {
            receiver.receive(length).ok();
            assert_eq!(receiver.rx_frame.length(), length);
        }
    }

    proptest! {
        #[test]
        fn receive_at_length_stage_goes_to_value_stage_on_non_zero_length(
            mut receiver in receiver(State::Receiving(Field::Length)),
            length in 1..=u8::MAX,
        ) {
            receiver.receive(length).ok();
            assert_eq!(receiver.state, State::Receiving(Field::Value));
        }
    }

    proptest! {
        #[test]
        fn receive_at_length_stage_goes_directly_to_crc_stage_on_zero_length(
            mut receiver in receiver(State::Receiving(Field::Length)),
        ) {
            let length = 0;
            receiver.receive(length).ok();
            assert_eq!(receiver.state, State::Receiving(Field::CRC));
        }
    }

    proptest! {
        #[test]
        fn receive_at_length_stage_returns_an_error_if_length_is_too_long(
            length in 2..=u8::MAX,
        ) {
            let mut receiver = Receiver::<1>::new();

            receiver.state = State::Receiving(Field::Length);

            assert_eq!(receiver.receive(length), Err(ReceiveError::TooLong));
        }
    }

    proptest! {
        #[test]
        fn receive_at_length_stage_goes_back_to_ready_if_length_is_too_long(
            length in 2..=u8::MAX,
        ) {
            let mut receiver = Receiver::<1>::new();

            receiver.state = State::Receiving(Field::Length);

            receiver.receive(length).ok();
            assert_eq!(receiver.state, State::Ready);
        }
    }

    proptest! {
        #[test]
        fn receive_at_length_stage_resets_the_rx_frame_if_length_is_too_long(
            length in 2..=u8::MAX,
        ) {
            let mut receiver = Receiver::<1>::new();

            receiver.rx_frame.set_code(0x9D);
            receiver.state = State::Receiving(Field::Length);

            receiver.receive(length).ok();
            assert_eq!(receiver.rx_frame, FrameBuffer::default());
        }
    }

    //////////////////// State::Receive(Field::Value) //////////////////////

    proptest! {
        #[test]
        fn receive_at_value_stage_returns_ok(
            mut receiver in receiver(State::Receiving(Field::Length)),
            value in vec(0..=u8::MAX, 1..=u8::MAX as usize),
        ) {
            receiver.receive(value.len() as u8).ok();

            for &byte in value.iter() {
                assert_eq!(receiver.receive(byte), Ok(()));
            }
        }
    }

    proptest! {
        #[test]
        fn receive_at_value_stage_stores_value(
            mut receiver in receiver(State::Receiving(Field::Length)),
            value in vec(0..=u8::MAX, 1..=u8::MAX as usize),
        ) {
            receiver.receive(value.len() as u8).ok();

            for (i, &byte) in value.iter().enumerate() {
                receiver.receive(byte).ok();
                assert_eq!(receiver.rx_frame.value()[i], byte);
            }
        }
    }

    proptest! {
        #[test]
        fn receive_remains_at_value_stage_until_it_has_been_completely_received(
            mut receiver in receiver(State::Receiving(Field::Length)),
            value in vec(0..=u8::MAX, 1..=u8::MAX as usize),
        ) {
            receiver.receive(value.len() as u8).ok();

            for &byte in value.iter().take(value.len() - 1) {
                receiver.receive(byte).ok();
                assert_eq!(receiver.state, State::Receiving(Field::Value));
            }
        }
    }

    proptest! {
        #[test]
        fn receive_waits_for_crc_when_value_has_been_received(
            mut receiver in receiver(State::Receiving(Field::Length)),
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            receiver.receive(value.len() as u8).ok();

            for byte in value {
                receiver.receive(byte).ok();
            }

            assert_eq!(receiver.state, State::Receiving(Field::CRC));
        }
    }

    ///////////////////// State::Receive(Field::CRC) ///////////////////////

    proptest! {
        #[test]
        fn receive_at_crc_stage_returns_ok(
            mut receiver in receiver(State::Receiving(Field::CRC)),
            crc in 0..=u8::MAX,
        ) {
            assert_eq!(receiver.receive(crc), Ok(()));
        }
    }

    proptest! {
        #[test]
        fn receive_at_crc_stage_stores_crc(
            mut receiver in receiver(State::Receiving(Field::CRC)),
            crc in 0..=u8::MAX,
        ) {
            receiver.receive(crc).ok();
            assert_eq!(receiver.rx_frame.crc(), crc);
        }
    }

    proptest! {
        #[test]
        fn receive_at_crc_stage_goes_to_eot_stage(
            mut receiver in receiver(State::Receiving(Field::CRC)),
            crc in 0..=u8::MAX,
        ) {
            receiver.receive(crc).ok();
            assert_eq!(receiver.state, State::Receiving(Field::EOT));
        }
    }

    ///////////////////// State::Receive(Field::EOT) ///////////////////////

    proptest! {
        #[test]
        fn receive_at_eot_stage_returns_ok_on_eot(
            mut receiver in receiver(State::Receiving(Field::EOT)),
        ) {
            assert_eq!(receiver.receive(EOT), Ok(()));
        }
    }

    proptest! {
        #[test]
        fn receive_at_eot_stage_goes_to_complete_on_eot(
            mut receiver in receiver(State::Receiving(Field::EOT)),
        ) {
            receiver.receive(EOT).ok();
            assert_eq!(receiver.state, State::Complete);
        }
    }

    proptest! {
        #[test]
        fn receive_at_eot_stage_returns_an_error_on_random_value(
            mut receiver in receiver(State::Receiving(Field::EOT)),
            not_eot in 0..=u8::MAX,
        ) {
            prop_assume!(not_eot != EOT);

            assert_eq!(receiver.receive(not_eot), Err(ReceiveError::NotEot));
        }
    }

    proptest! {
        #[test]
        fn receive_at_eot_stage_goes_back_to_ready_on_random_value(
            mut receiver in receiver(State::Receiving(Field::EOT)),
            not_eot in 0..=u8::MAX,
        ) {
            prop_assume!(not_eot != EOT);

            receiver.receive(not_eot).ok();
            assert_eq!(receiver.state, State::Ready);
        }
    }

    proptest! {
        #[test]
        fn receive_at_eot_stage_resets_the_rx_frame_on_random_value(
            mut receiver in receiver(State::Receiving(Field::EOT)),
            not_eot in 0..=u8::MAX,
        ) {
            prop_assume!(not_eot != EOT);

            receiver.receive(not_eot).ok();
            assert_eq!(receiver.rx_frame, FrameBuffer::default());
        }
    }

    /////////////////////////// State::Complete ////////////////////////////

    proptest! {
        #[test]
        fn receive_at_complete_stage_returns_an_error(
            mut receiver in receiver(State::Complete),
            value in 0..=u8::MAX,
        ) {
            assert_eq!(receiver.receive(value), Err(ReceiveError::Overflow));
        }
    }

    proptest! {
        #[test]
        fn receive_at_complete_stage_does_not_change_the_state(
            mut receiver in receiver(State::Complete),
            value in 0..=u8::MAX,
        ) {
            receiver.receive(value).ok();
            assert_eq!(receiver.state, State::Complete);
        }
    }

    proptest! {
        #[test]
        fn receive_at_complete_stage_does_not_change_the_buffer(
            mut receiver in receiver(State::Complete),
            value in 0..=u8::MAX,
        ) {
            let original_rx_frame = receiver.rx_frame.clone();

            receiver.receive(value).ok();
            assert_eq!(receiver.rx_frame, original_rx_frame);
        }
    }

    ////////////////////////////// Accessors ///////////////////////////////

    #[test]
    fn complete_frame_received_returns_true_in_complete_state() {
        let mut receiver = Receiver::<255>::new();
        receiver.state = State::Complete;
        assert!(receiver.complete_frame_received());
    }

    #[test]
    fn complete_frame_received_returns_false_otherwise() {
        let receiver = Receiver::<255>::new();
        assert!(!receiver.complete_frame_received());
    }
}
