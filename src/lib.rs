//! An implementation of ERCP Basic in Rust.

#![no_std]
#![deny(unsafe_code)]

#[cfg(test)]
#[macro_use]
extern crate std;

mod crc;
mod error;
mod frame;
mod frame_buffer;

use error::{Error, IoError};
use frame_buffer::FrameBuffer;

/// An ERCP Basic instance.
// #[derive(Debug)]
pub struct ERCPBasic<C: Connection, const MAX_LENGTH: usize> {
    state: State,
    rx_frame: FrameBuffer<MAX_LENGTH>,
    connection: C,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum State {
    Ready,
    Init(InitState),
    Receiving(Field),
    Complete,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum InitState {
    R,
    C,
    P,
    B,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Field {
    Type,
    Length,
    Value,
    CRC,
    EOT,
}

pub trait Connection {
    fn read(&mut self) -> Result<Option<u8>, IoError>;
    fn write(&mut self, byte: u8) -> Result<(), IoError>;
}

const EOT: u8 = 0x04;

impl InitState {
    const fn next_state(&self) -> State {
        match self {
            InitState::R => State::Init(InitState::C),
            InitState::C => State::Init(InitState::P),
            InitState::P => State::Init(InitState::B),
            InitState::B => State::Receiving(Field::Type),
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

#[cfg(test)]
impl<C: Connection, const MAX_LENGTH: usize> std::fmt::Debug
    for ERCPBasic<C, MAX_LENGTH>
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ERCPBasic")
            .field("state", &self.state)
            .field("rx_frame", &self.rx_frame)
            .finish()
    }
}

impl<C: Connection, const MAX_LENGTH: usize> ERCPBasic<C, MAX_LENGTH> {
    pub fn new(connection: C) -> Self {
        Self {
            state: State::Ready,
            rx_frame: FrameBuffer::new(),
            connection,
        }
    }

    pub fn handle_data(&mut self) {
        loop {
            match self.connection.read() {
                Ok(Some(byte)) => self.receive(byte),
                Ok(None) => break,
                Err(_) => todo!(),
            }
        }
    }

    // TODO: Return a status.
    fn receive(&mut self, byte: u8) {
        match self.state {
            State::Ready => {
                if byte == b'E' {
                    self.state = State::Init(InitState::R);
                } else {
                    // Ignore unexpected data.
                }
            }

            State::Init(init_state) => {
                if byte == init_state.value() as u8 {
                    self.state = init_state.next_state();
                } else {
                    // Unexpected value => reset.
                    self.state = State::Ready;
                }
            }

            State::Receiving(field) => match field {
                Field::Type => {
                    self.rx_frame.set_command(byte);
                    self.state = State::Receiving(Field::Length);
                }

                Field::Length => match self.rx_frame.set_length(byte) {
                    Ok(()) => {
                        if byte == 0 {
                            // No value field if the length is zero.
                            self.state = State::Receiving(Field::CRC);
                        } else {
                            self.state = State::Receiving(Field::Value);
                        }
                    }

                    Err(Error::TooLong) => {
                        self.state = State::Ready;
                        self.rx_frame.reset();
                        // TODO: Nack(TOO_LONG)
                    }

                    Err(_) => unreachable!(),
                },

                Field::Value => {
                    // NOTE: The error never occurs since we wait for the CRC
                    // when the value is complete.
                    self.rx_frame.push_value(byte).ok();

                    if self.rx_frame.value_is_complete() {
                        self.state = State::Receiving(Field::CRC);
                    }
                }

                Field::CRC => {
                    self.rx_frame.set_crc(byte);
                    self.state = State::Receiving(Field::EOT);
                }

                Field::EOT => {
                    if byte == EOT {
                        self.state = State::Complete;
                    } else {
                        // Unexpected value => reset.
                        self.state = State::Ready;
                        self.rx_frame.reset();
                    }
                }
            },

            State::Complete => {
                // Ignore unexpected data.
            }
        }
    }

    /// Returns wether a complete frame has been received.
    ///
    /// If it returns `true`, you should then call `process`.
    pub fn complete_frame_received(&self) -> bool {
        self.state == State::Complete
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crc::crc;
    use proptest::collection::vec;
    use proptest::prelude::*;

    struct TestConnection {
        tx_buffer: [u8; 264],
        tx_size: usize,
        rx_buffer: [u8; 264],
        rx_size: usize,
        rx_ptr: usize,
    }

    impl TestConnection {
        fn test_send(&mut self, data: &[u8]) {
            self.rx_size = 0;

            for &byte in data {
                self.rx_buffer[self.rx_size] = byte;
                self.rx_size += 1;
            }
        }

        fn test_receive(&mut self) -> &[u8] {
            &self.tx_buffer[0..self.tx_size]
        }
    }

    impl Default for TestConnection {
        fn default() -> Self {
            TestConnection {
                tx_buffer: [0; 264],
                tx_size: 0,
                rx_buffer: [0; 264],
                rx_size: 0,
                rx_ptr: 0,
            }
        }
    }

    impl Connection for TestConnection {
        fn read(&mut self) -> Result<Option<u8>, IoError> {
            if self.rx_ptr < self.rx_size {
                let byte = self.rx_buffer[self.rx_ptr];
                self.rx_ptr += 1;

                Ok(Some(byte))
            } else {
                Ok(None)
            }
        }

        fn write(&mut self, byte: u8) -> Result<(), IoError> {
            self.tx_buffer[self.tx_size] = byte;
            self.tx_size += 1;
            Ok(())
        }
    }

    fn setup(test: impl Fn(ERCPBasic<TestConnection, 255>)) {
        let connection = TestConnection::default();
        let ercp = ERCPBasic::new(connection);
        test(ercp);
    }

    /////////////////////////////// Strategy ///////////////////////////////

    fn ercp(
        state: State,
    ) -> impl Strategy<Value = ERCPBasic<TestConnection, 255>> {
        (0..=u8::MAX, vec(0..=u8::MAX, 0..=u8::MAX as usize)).prop_map(
            move |(command, value)| {
                let connection = TestConnection::default();
                let mut ercp = ERCPBasic::new(connection);

                while ercp.state != state {
                    match ercp.state {
                        State::Ready => {
                            ercp.state = State::Init(InitState::R);
                        }

                        State::Init(init_state) => {
                            ercp.state = init_state.next_state();
                        }

                        State::Receiving(field) => match field {
                            Field::Type => {
                                ercp.rx_frame.set_command(command);
                                ercp.state = State::Receiving(Field::Length);
                            }

                            Field::Length => {
                                ercp.rx_frame
                                    .set_length(value.len() as u8)
                                    .unwrap();
                                ercp.state = State::Receiving(Field::Value);
                            }

                            Field::Value => {
                                for &byte in &value {
                                    ercp.rx_frame.push_value(byte).unwrap();
                                }

                                ercp.state = State::Receiving(Field::CRC);
                            }

                            Field::CRC => {
                                ercp.rx_frame.set_crc(crc(command, &value));
                                ercp.state = State::Receiving(Field::EOT);
                            }

                            Field::EOT => {
                                ercp.state = State::Complete;
                            }
                        },

                        State::Complete => unreachable!(),
                    };
                }

                ercp
            },
        )
    }

    ////////////////////// The receive state machine ///////////////////////

    ///////////////////////////// State::Ready /////////////////////////////

    #[test]
    fn ercp_starts_in_ready_state() {
        setup(|ercp| {
            assert_eq!(ercp.state, State::Ready);
        });
    }

    proptest! {
        #[test]
        fn receive_does_nothing_on_random_data(value in 0..=u8::MAX) {
            // 'E' starts a receive sequence, so we do not want it.
            prop_assume!(value != b'E');

            setup(|mut ercp| {
                ercp.receive(value);
                assert_eq!(ercp.state, State::Ready);
            });
        }
    }

    ///////////////////////////// State::Init //////////////////////////////

    #[test]
    fn receive_starts_init_sequence_on_e() {
        setup(|mut ercp| {
            ercp.receive(b'E');
            assert_eq!(ercp.state, State::Init(InitState::R));
        });
    }

    #[test]
    fn receive_advances_through_the_init_sequence() {
        setup(|mut ercp| {
            ercp.receive(b'E');
            assert_eq!(ercp.state, State::Init(InitState::R));

            ercp.receive(b'R');
            assert_eq!(ercp.state, State::Init(InitState::C));

            ercp.receive(b'C');
            assert_eq!(ercp.state, State::Init(InitState::P));

            ercp.receive(b'P');
            assert_eq!(ercp.state, State::Init(InitState::B));
        });
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

            setup(|mut ercp| {
                if num >= 1 {
                    ercp.receive(b'E');
                }
                if num >= 2 {
                    ercp.receive(b'R');
                }
                if num >= 3 {
                    ercp.receive(b'C');
                }
                if num >= 4 {
                    ercp.receive(b'P');
                }

                ercp.receive(value);
                assert_eq!(ercp.state, State::Ready);
            });
        }
    }

    #[test]
    fn receive_waits_for_type_after_init_sequence() {
        setup(|mut ercp| {
            ercp.receive(b'E');
            ercp.receive(b'R');
            ercp.receive(b'C');
            ercp.receive(b'P');
            ercp.receive(b'B');
            assert_eq!(ercp.state, State::Receiving(Field::Type));
        });
    }

    ///////////////////// State::Receive(Field::Type) //////////////////////

    proptest! {
        #[test]
        fn receive_at_type_stage_stores_command_type(
            mut ercp in ercp(State::Receiving(Field::Type)),
            command in 0..=u8::MAX,
        ) {
            ercp.receive(command);
            assert_eq!(ercp.rx_frame.command(), command);
        }
    }

    proptest! {
        #[test]
        fn receive_at_type_stage_goes_to_length_stage(
            mut ercp in ercp(State::Receiving(Field::Type)),
            command in 0..=u8::MAX,
        ) {
            ercp.receive(command);
            assert_eq!(ercp.state, State::Receiving(Field::Length));
        }
    }

    //////////////////// State::Receive(Field::Length) /////////////////////

    proptest! {
        #[test]
        fn receive_at_length_stage_stores_length(
            mut ercp in ercp(State::Receiving(Field::Length)),
            length in 0..=u8::MAX,
        ) {
            ercp.receive(length);
            assert_eq!(ercp.rx_frame.length(), length);
        }
    }

    proptest! {
        #[test]
        fn receive_at_length_stage_goes_to_value_stage_on_non_zero_length(
            mut ercp in ercp(State::Receiving(Field::Length)),
            length in 1..=u8::MAX,
        ) {
            ercp.receive(length);
            assert_eq!(ercp.state, State::Receiving(Field::Value));
        }
    }

    proptest! {
        #[test]
        fn receive_at_length_stage_goes_directly_to_crc_stage_on_zero_length(
            mut ercp in ercp(State::Receiving(Field::Length)),
        ) {
            let length = 0;
            ercp.receive(length);
            assert_eq!(ercp.state, State::Receiving(Field::CRC));
        }
    }

    proptest! {
        #[test]
        fn receive_at_length_stage_goes_back_to_ready_if_length_is_too_long(
            length in 96..=u8::MAX,
        ) {
            let connection = TestConnection::default();
            let mut ercp = ERCPBasic::<TestConnection, 95>::new(connection);
            ercp.state = State::Receiving(Field::Length);

            ercp.receive(length);
            assert_eq!(ercp.state, State::Ready);
        }
    }

    proptest! {
        #[test]
        fn receive_at_length_stage_resets_the_rx_frame_if_length_is_too_long(
            length in 96..=u8::MAX,
        ) {
            let connection = TestConnection::default();
            let mut ercp = ERCPBasic::<TestConnection, 95>::new(connection);
            ercp.rx_frame.set_command(0x9D);
            ercp.state = State::Receiving(Field::Length);

            ercp.receive(length);
            assert_eq!(ercp.rx_frame, FrameBuffer::default());
        }
    }

    // proptest! {
    //     #[test]
    //     fn receive_at_length_stage_sends_a_nack_if_length_is_too_long(
    //         length in 96..=u8::MAX,
    //     ) {
    //         let mut ercp = ERCPBasic::<95>::new();
    //         ercp.state = State::Receiving(Field::Length);

    //         ercp.receive(length);
    //         todo!(); // TODO:
    //     }
    // }

    //////////////////// State::Receive(Field::Value) //////////////////////

    proptest! {
        #[test]
        fn receive_at_value_stage_stores_value(
            mut ercp in ercp(State::Receiving(Field::Length)),
            value in vec(0..=u8::MAX, 1..=u8::MAX as usize),
        ) {
            ercp.receive(value.len() as u8);

            for (i, &byte) in value.iter().enumerate() {
                ercp.receive(byte);
                assert_eq!(ercp.rx_frame.value()[i], byte);
            }
        }
    }

    proptest! {
        #[test]
        fn receive_remains_at_value_stage_until_it_has_been_completely_received(
            mut ercp in ercp(State::Receiving(Field::Length)),
            value in vec(0..=u8::MAX, 1..=u8::MAX as usize),
        ) {
            ercp.receive(value.len() as u8);

            for &byte in value.iter().take(value.len() - 1) {
                ercp.receive(byte);
                assert_eq!(ercp.state, State::Receiving(Field::Value));
            }
        }
    }

    proptest! {
        #[test]
        fn receive_waits_for_crc_when_value_has_been_received(
            mut ercp in ercp(State::Receiving(Field::Length)),
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            ercp.receive(value.len() as u8);

            for byte in value {
                ercp.receive(byte);
            }

            assert_eq!(ercp.state, State::Receiving(Field::CRC));
        }
    }

    ///////////////////// State::Receive(Field::CRC) ///////////////////////

    proptest! {
        #[test]
        fn receive_at_crc_stage_stores_crc(
            mut ercp in ercp(State::Receiving(Field::CRC)),
            crc in 0..=u8::MAX,
        ) {
            ercp.receive(crc);
            assert_eq!(ercp.rx_frame.crc(), crc);
        }
    }

    proptest! {
        #[test]
        fn receive_at_crc_stage_goes_to_eot_stage(
            mut ercp in ercp(State::Receiving(Field::CRC)),
            crc in 0..=u8::MAX,
        ) {
            ercp.receive(crc);
            assert_eq!(ercp.state, State::Receiving(Field::EOT));
        }
    }

    ///////////////////// State::Receive(Field::EOT) ///////////////////////

    proptest! {
        #[test]
        fn receive_at_eot_stage_goes_to_complete_on_eot(
            mut ercp in ercp(State::Receiving(Field::EOT)),
        ) {
            ercp.receive(EOT);
            assert_eq!(ercp.state, State::Complete);
        }
    }

    proptest! {
        #[test]
        fn receive_at_eot_stage_resets_on_random_value(
            mut ercp in ercp(State::Receiving(Field::EOT)),
            not_eot in 0..=u8::MAX,
        ) {
            prop_assume!(not_eot != EOT);

            ercp.receive(not_eot);
            assert_eq!(ercp.state, State::Ready);
        }
    }

    proptest! {
        #[test]
        fn receive_at_eot_stage_resets_the_rx_frame_on_random_value(
            mut ercp in ercp(State::Receiving(Field::EOT)),
            not_eot in 0..=u8::MAX,
        ) {
            prop_assume!(not_eot != EOT);

            ercp.receive(not_eot);
            assert_eq!(ercp.rx_frame, FrameBuffer::default());
        }
    }

    /////////////////////////// State::Complete ////////////////////////////

    proptest! {
        #[test]
        fn receive_at_validating_state_does_nothing(
            mut ercp in ercp(State::Complete),
            value in 0..=u8::MAX,
        ) {
            let original_rx_frame = ercp.rx_frame.clone();

            ercp.receive(value);
            assert_eq!(ercp.state, State::Complete);
            assert_eq!(ercp.rx_frame, original_rx_frame);
        }
    }

    #[test]
    fn complete_frame_received_returns_true_in_complete_state() {
        setup(|mut ercp| {
            ercp.state = State::Complete;
            assert!(ercp.complete_frame_received());
        });
    }

    #[test]
    fn complete_frame_received_returns_false_otherwise() {
        setup(|ercp| {
            assert!(!ercp.complete_frame_received());
        });
    }

    /////////////////////////// Data input/output //////////////////////////

    #[test]
    fn handle_data_processes_incoming_data() {
        setup(|mut ercp| {
            let data = [b'E', b'R', b'C', b'P', b'B', 0, 0, 0, EOT];
            ercp.connection.test_send(&data);
            ercp.handle_data();
            assert_eq!(ercp.state, State::Complete);
        });
    }

    #[test]
    fn handle_data_does_nothing_on_no_data() {
        setup(|mut ercp| {
            ercp.handle_data();
            assert_eq!(ercp.state, State::Ready);
        });
    }
}
