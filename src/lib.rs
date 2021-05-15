//! An implementation of ERCP Basic in Rust.

#![cfg_attr(all(not(feature = "std"), not(test)), no_std)]
#![deny(unsafe_code)]

pub mod adapter;
pub mod command;
pub mod error;

mod connection;
mod crc;
mod frame_buffer;
mod router;

pub use adapter::Adapter;
pub use command::Command;
pub use error::Error;
pub use router::{DefaultRouter, Router};

use command::{nack_reason, ACK, NACK};
use connection::Connection;
use frame_buffer::FrameBuffer;

/// An ERCP Basic instance.
#[derive(Debug)]
pub struct ErcpBasic<A: Adapter, R: Router, const MAX_LENGTH: usize> {
    state: State,
    rx_frame: FrameBuffer<MAX_LENGTH>,
    connection: Connection<A>,
    router: R,
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

// TODO: Put elsewhere.
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

impl<A: Adapter, R: Router, const MAX_LENGTH: usize>
    ErcpBasic<A, R, MAX_LENGTH>
{
    pub fn new(adapter: A, router: R) -> Self {
        Self {
            state: State::Ready,
            rx_frame: FrameBuffer::new(),
            router,
            connection: Connection::new(adapter),
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

    /// Returns wether a complete frame has been received.
    ///
    /// If it returns `true`, you should then call `process`.
    pub fn complete_frame_received(&self) -> bool {
        self.state == State::Complete
    }

    /// Returns the next command to process.
    pub fn next_command(&self) -> Option<Result<Command, Error>> {
        if self.complete_frame_received() {
            Some(self.rx_frame.check_frame())
        } else {
            None
        }
    }

    // TODO: Async version.
    /// Blocks until a complete frame has been received.
    pub fn wait_for_command(&mut self) -> Result<Command, Error> {
        while !self.complete_frame_received() {
            // TODO: Do different things depending on features.

            // TODO: Only with the blocking feature.
            self.handle_data();

            // TODO: WFI on Cortex-M.
            // TODO: Timeout (idea: use a struct field)
        }

        self.rx_frame.check_frame()
    }

    pub fn process(&mut self, context: &mut R::Context) {
        // TODO: Use next_command once it is in a sub-struct.
        if self.complete_frame_received() {
            match self.rx_frame.check_frame() {
                Ok(command) => {
                    if let Some(reply) = self.router.route(command, context) {
                        self.connection.send(reply);
                    }
                }

                Err(Error::InvalidCRC) => {
                    let nack = Command::new(NACK, &[nack_reason::INVALID_CRC])
                        .unwrap();

                    self.notify(nack);
                }

                Err(_) => unreachable!(),
            }

            self.reset_state();
        }
    }

    pub fn command(&mut self, command: Command) -> Result<Command, Error> {
        self.connection.send(command)?;

        // TODO: When to reset the frame? It is not possible here since we don’t
        // copy the value. Maybe we should?
        // self.rx_frame.reset();

        self.wait_for_command()
    }

    pub fn notify(&mut self, command: Command) -> Result<(), Error> {
        self.connection.send(command)?;
        Ok(())
    }

    pub fn ping(&mut self) -> Result<(), Error> {
        let reply = self.command(Command::ping())?;

        // TODO: Reset the frame buffer. Is it here, wouldn’t it be better to
        // copy the command instead?

        if reply.command() == ACK {
            Ok(())
        } else {
            // TODO: Better error.
            Err(Error::OtherError)
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
                        self.reset_state();

                        let nack = Command::new(NACK, &[nack_reason::TOO_LONG])
                            .unwrap();

                        self.notify(nack);
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
                        self.reset_state();
                    }
                }
            },

            State::Complete => {
                // Ignore unexpected data.
            }
        }
    }

    fn reset_state(&mut self) {
        self.state = State::Ready;
        self.rx_frame.reset();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use connection::tests::TestAdapter;
    use crc::crc;
    use error::IoError;
    use router::DefaultRouter;

    use proptest::collection::vec;
    use proptest::prelude::*;

    #[derive(Debug, Default)]
    struct TestRouter {
        last_command: Option<OwnedCommand>,
        reply: Option<OwnedCommand>,
    }

    #[derive(Debug, PartialEq)]
    struct OwnedCommand {
        command: u8,
        value: Vec<u8>,
    }

    impl Router for TestRouter {
        type Context = ();

        fn route(&mut self, command: Command, _: &mut ()) -> Option<Command> {
            self.last_command = Some(command.into());
            self.reply.as_ref().map(|command| {
                Command::new(command.command, &command.value).unwrap()
            })
        }
    }

    impl<'a> From<Command<'a>> for OwnedCommand {
        fn from(command: Command<'a>) -> Self {
            Self {
                command: command.command(),
                value: command.value().into(),
            }
        }
    }

    impl<'a> PartialEq<Command<'a>> for OwnedCommand {
        fn eq(&self, other: &Command) -> bool {
            self.command == other.command() && self.value == other.value()
        }
    }

    const MAX_LENGTH: usize = u8::MAX as usize;

    ////////////////////////////// Test setup //////////////////////////////

    fn setup(test: impl Fn(ErcpBasic<TestAdapter, TestRouter, MAX_LENGTH>)) {
        let adapter = TestAdapter::default();
        let router = TestRouter::default();
        let ercp = ErcpBasic::new(adapter, router);
        test(ercp);
    }

    /////////////////////////////// Strategy ///////////////////////////////

    fn ercp<'a>(
        state: State,
    ) -> impl Strategy<Value = ErcpBasic<TestAdapter, TestRouter, MAX_LENGTH>>
    {
        (0..=u8::MAX, vec(0..=u8::MAX, 0..=u8::MAX as usize)).prop_map(
            move |(command, value)| {
                let adapter = TestAdapter::default();
                let router = TestRouter::default();
                let mut ercp = ErcpBasic::new(adapter, router);

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
            let adapter = TestAdapter::default();
            let mut ercp = ErcpBasic::<TestAdapter, DefaultRouter, 95>::new(
                adapter,
                DefaultRouter
            );

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
            let adapter = TestAdapter::default();
            let mut ercp = ErcpBasic::<TestAdapter, DefaultRouter, 95>::new(
                adapter,
                DefaultRouter
            );

            ercp.rx_frame.set_command(0x9D);
            ercp.state = State::Receiving(Field::Length);

            ercp.receive(length);
            assert_eq!(ercp.rx_frame, FrameBuffer::default());
        }
    }

    proptest! {
        #[test]
        fn receive_at_length_stage_sends_a_nack_if_length_is_too_long(
            length in 96..=u8::MAX,
        ) {
            let adapter = TestAdapter::default();
            let mut ercp = ErcpBasic::<TestAdapter, DefaultRouter, 95>::new(
                adapter,
                DefaultRouter
            );

            ercp.state = State::Receiving(Field::Length);

            let nack = Command::new(NACK, &[nack_reason::TOO_LONG]).unwrap();

            ercp.receive(length);
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                nack.as_frame()
            );
        }
    }

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

    ////////////////////////////// Data input //////////////////////////////

    #[test]
    fn handle_data_processes_incoming_data() {
        setup(|mut ercp| {
            let frame = [b'E', b'R', b'C', b'P', b'B', 0, 0, 0, EOT];
            ercp.connection.adapter().test_send(&frame);
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

    // #[test]
    // fn handle_data_does_something_with_read_errors() {
    //     // TODO: Error handling.
    //     todo!();
    // }

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

    proptest! {
        #[test]
        fn next_command_returns_the_received_command(
            ercp in ercp(State::Complete),
        ) {
            let command = ercp.rx_frame.check_frame().unwrap();
            assert_eq!(ercp.next_command(), Some(Ok(command)));
        }
    }

    proptest! {
        #[test]
        fn next_command_returns_an_error_if_the_received_frame_is_corrupted(
            mut ercp in ercp(State::Complete),
            bad_crc in 0..=u8::MAX,
        ) {
            prop_assume!(
                bad_crc != crc(ercp.rx_frame.command(), ercp.rx_frame.value())
            );

            ercp.rx_frame.set_crc(bad_crc);
            assert_eq!(ercp.next_command(), Some(Err(Error::InvalidCRC)));
        }
    }

    // TODO: Enable when the design makes it possible.
    // proptest! {
    //     #[test]
    //     fn next_command_resets_state_if_the_received_frame_is_corrupted(
    //         mut ercp in ercp(State::Complete),
    //         bad_crc in 0..=u8::MAX,
    //     ) {
    //         prop_assume!(
    //             bad_crc != crc(ercp.rx_frame.command(), ercp.rx_frame.value())
    //         );

    //         ercp.rx_frame.set_crc(bad_crc);

    //         let _ = ercp.next_command();
    //         assert_eq!(ercp.state, State::Ready);
    //         assert_eq!(ercp.rx_frame, FrameBuffer::default());
    //     }
    // }

    proptest! {
        #[test]
        fn next_command_returns_none_if_no_command_waiting(
            ercp in ercp(State::Ready),
        ) {
            assert_eq!(ercp.next_command(), None);
        }
    }

    proptest! {
        #[test]
        fn wait_for_command_returns_the_received_command(
            mut ercp in ercp(State::Complete),
        ) {
            let received = ercp.rx_frame.check_frame().unwrap();
            let value = received.value().to_owned();
            let command =
                Command::new(received.command(), &value).unwrap();

            assert_eq!(ercp.wait_for_command(), Ok(command));
        }
    }

    proptest! {
        #[test]
        fn wait_for_command_returns_an_error_if_the_received_frame_is_corrupted(
            mut ercp in ercp(State::Complete),
            bad_crc in 0..=u8::MAX,
        ) {
            prop_assume!(
                bad_crc != crc(ercp.rx_frame.command(), ercp.rx_frame.value())
            );

            ercp.rx_frame.set_crc(bad_crc);
            assert_eq!(ercp.wait_for_command(), Err(Error::InvalidCRC));
        }
    }

    // TODO: Enable when the design makes it possible.
    // proptest! {
    //     #[test]
    //     fn wait_for_command_resets_state_if_the_received_frame_is_corrupted(
    //         mut ercp in ercp(State::Complete),
    //         bad_crc in 0..=u8::MAX,
    //     ) {
    //         prop_assume!(
    //             bad_crc != crc(ercp.rx_frame.command(), ercp.rx_frame.value())
    //         );

    //         ercp.rx_frame.set_crc(bad_crc);

    //         let _ = ercp.wait_for_command();
    //         assert_eq!(ercp.state, State::Ready);
    //         assert_eq!(ercp.rx_frame, FrameBuffer::default());
    //     }
    // }

    // proptest! {
    //     #[test]
    //     fn wait_for_command_waits_until_a_frame_has_been_received(
    //         ercp in ercp(State::Ready),
    //     ) {
    //         // TODO:
    //         todo!()
    //     }
    // }

    ////////////////////////// Command processing //////////////////////////

    proptest! {
        #[test]
        fn process_routes_the_command_to_its_handler(
            mut ercp in ercp(State::Complete),
        ) {
            let command: OwnedCommand =
                ercp.rx_frame.check_frame().unwrap().into();

            ercp.process(&mut ());

            assert!(ercp.router.last_command.is_some());
            let expected_command = ercp.router.last_command.unwrap();

            assert_eq!(expected_command, command);
        }
    }

    proptest! {
        #[test]
        fn process_sends_the_reply_if_there_is_some(
            mut ercp in ercp(State::Complete),
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize)
        ) {
            let reply = Command::new(command, &value).unwrap();
            let expected_frame = reply.as_frame();

            ercp.router.reply = Some(reply.into());

            ercp.process(&mut ());
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                expected_frame
            );
        }
    }

    proptest! {
        #[test]
        fn process_does_not_send_a_reply_if_there_is_none(
            mut ercp in ercp(State::Complete),
        ) {
            ercp.router.reply = None;

            ercp.process(&mut ());
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                &[]
            );
        }
    }

    proptest! {
        #[test]
        fn process_sends_a_nack_if_crc_is_invalid(
            mut ercp in ercp(State::Complete),
            bad_crc in 0..=u8::MAX,
        ) {
            prop_assume!(bad_crc != ercp.rx_frame.crc());
            ercp.rx_frame.set_crc(bad_crc);

            let nack = Command::new(NACK, &[nack_reason::INVALID_CRC]).unwrap();

            ercp.process(&mut ());
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                nack.as_frame()
            );
        }
    }

    proptest! {
        #[test]
        fn process_resets_the_state_machine(
            mut ercp in ercp(State::Complete),
        ) {
            ercp.process(&mut ());
            assert_eq!(ercp.state, State::Ready);
        }
    }

    proptest! {
        #[test]
        fn process_resets_the_rx_frame(
            mut ercp in ercp(State::Complete),
        ) {
            ercp.process(&mut ());
            assert_eq!(ercp.rx_frame, FrameBuffer::default());
        }
    }

    ////////////////////////////// Data output /////////////////////////////

    proptest! {
        #[test]
        fn command_writes_a_frame_on_the_connection(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut ercp| {
                let command = Command::new(command, &value).unwrap();
                let expected_frame = command.as_frame();

                // Ensure there is a reply not to block.
                ercp.connection.adapter().test_send(&Command::ack().as_frame());

                assert!(ercp.command(command).is_ok());
                assert_eq!(
                    ercp.connection.adapter().test_receive(),
                    expected_frame
                );
            });
        }
    }

    proptest! {
        #[test]
        fn command_returns_the_reply(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                assert_eq!(ercp.command(Command::ping()), Ok(reply));
            });
        }
    }

    #[test]
    fn command_returns_an_error_on_write_errors() {
        setup(|mut ercp| {
            ercp.connection.adapter().write_error = Some(IoError::IoError);

            assert_eq!(
                ercp.command(Command::ping()),
                Err(Error::IoError(IoError::IoError))
            );
        });
    }

    proptest! {
        #[test]
        fn notify_writes_a_frame_on_the_connection(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut ercp| {
                let command = Command::new(command, &value).unwrap();
                let expected_frame = command.as_frame();

                assert_eq!(ercp.notify(command), Ok(()));
                assert_eq!(
                    ercp.connection.adapter().test_receive(),
                    expected_frame
                );
            });
        }
    }

    proptest! {
        #[test]
        fn notify_returns_an_error_on_write_error(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut ercp| {
                let command = Command::new(command, &value).unwrap();
                ercp.connection.adapter().write_error = Some(IoError::IoError);

                assert_eq!(
                    ercp.notify(command),
                    Err(Error::IoError(IoError::IoError))
                );
            })
        }
    }

    /////////////////////////////// Commands ///////////////////////////////

    #[test]
    fn ping_sends_a_ping() {
        setup(|mut ercp| {
            let expected_frame = Command::ping().as_frame();
            let reply_frame = Command::ack().as_frame();

            ercp.connection.adapter().test_send(&reply_frame);

            assert_eq!(ercp.ping(), Ok(()));
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                expected_frame
            );
        })
    }

    proptest! {
        #[test]
        fn ping_returns_an_error_on_unexpected_reply(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(command != ACK);

            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                // TODO: Better error.
                assert_eq!(ercp.ping(), Err(Error::OtherError));
            });
        }
    }
}
