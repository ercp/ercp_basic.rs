//! An implementation of ERCP Basic in Rust.

#![cfg_attr(all(not(feature = "std"), not(test)), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![deny(unsafe_code)]

pub mod adapter;
pub mod command;
pub mod error;
pub mod version;

mod connection;
mod crc;
mod frame_buffer;
mod router;

pub use ercp_basic_macros::command;

pub use adapter::Adapter;
pub use command::Command;
pub use error::Error;
pub use router::{DefaultRouter, Router};
pub use version::Version;

use command::{
    nack_reason, ACK, DESCRIPTION_REPLY, MAX_LENGTH_REPLY, NACK,
    PROTOCOL_REPLY, VERSION_REPLY,
};
use connection::Connection;
use error::{BufferError, CommandError, FrameError};
use frame_buffer::FrameBuffer;

/// An ERCP Basic driver.
///
/// A driver can be instanciated on any connection for which an [`Adapter`] is
/// provided. There are several built-in adapters:
///
/// * for embedded:
///     * [`adapter::SerialAdapter`] for [`embedded_hal::serial`] (feature:
///       `serial`),
///     * [`adapter::RttAdapter`] for [`rtt_target`] (feature: `rtt`);
/// * for hosts (to build tools):
///     * [`adapter::SerialPortAdapter`] for [`serialport`] (feature:
///       `serial-host`),
///     * [`adapter::RttProbeRsAdapter`] for [`probe_rs_rtt`] (feature:
///       `rtt-probe-rs`).
///
/// If this is not sufficient for your use case, you can still write your own by
/// implementing the [`Adapter`] trait.
///
/// In addition to the adapter, you need do provide a [`Router`] for handling
/// incoming commands. [`DefaultRouter`] handles the built-in commands out of
/// the box, but you can write your own to extend it with custom commands.
///
/// # Minimal requirements
///
/// To get a minimal ERCP Basic enabled device, you need to:
///
/// * instantiate an ERCP Basic driver on the wanted connection with [`ErcpBasic::new`],
/// * call [`ErcpBasic::handle_data`] regularly to handle incoming data (this
///   should be done in the handler for the “data available” event of your
///   connection),
/// * call [`ErcpBasic::process`] regularly to process incoming
///   commands.
#[derive(Debug)]
pub struct ErcpBasic<A: Adapter, R: Router<MAX_LEN>, const MAX_LEN: usize> {
    state: State,
    rx_frame: FrameBuffer<MAX_LEN>,
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

impl<A: Adapter, R: Router<MAX_LEN>, const MAX_LEN: usize>
    ErcpBasic<A, R, MAX_LEN>
{
    /// Instantiates an ERCP Basic driver.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::{ErcpBasic, DefaultRouter};
    ///
    /// # use ercp_basic::{Adapter, error::IoError};
    /// #
    /// # struct SomeAdapter;
    /// #
    /// # impl SomeAdapter { fn new() -> Self { SomeAdapter } }
    /// #
    /// # impl ercp_basic::Adapter for SomeAdapter {
    /// #    fn read(&mut self) -> Result<Option<u8>, IoError> { Ok(None) }
    /// #    fn write(&mut self, byte: u8) -> Result<(), IoError> { Ok(()) }
    /// # }
    /// #
    /// // Instantiate an adapter matching your underlying layer.
    /// let adapter = SomeAdapter::new();
    ///
    /// // Instantiate an ERCP Basic driver using the default router. Here we
    /// // need to partially annotate the type to provide the MAX_LEN parameter.
    /// let ercp: ErcpBasic<_, _, 255> = ErcpBasic::new(adapter, DefaultRouter);
    /// ```
    pub fn new(adapter: A, router: R) -> Self {
        Self {
            state: State::Ready,
            rx_frame: FrameBuffer::new(),
            router,
            connection: Connection::new(adapter),
        }
    }

    /// Releases the `adapter` and `router`.
    pub fn release(self) -> (A, R) {
        (self.connection.release(), self.router)
    }

    /// Handles incoming data.
    ///
    /// This function reads data from the connection and processes it until
    /// there is nothing more to read.
    ///
    /// You **must** call this function regularly somewhere in your code for
    /// ERCP Basic to work properly. Typical places to call it include your
    /// connection interrupt handler, an event loop, etc.
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
    pub fn next_command(&self) -> Option<Result<Command, FrameError>> {
        if self.complete_frame_received() {
            Some(self.rx_frame.check_frame())
        } else {
            None
        }
    }

    // TODO: Async version.
    /// Blocks until a complete frame has been received.
    pub fn wait_for_command(&mut self) -> Result<Command, FrameError> {
        while !self.complete_frame_received() {
            // TODO: Do different things depending on features.

            // TODO: Only with the blocking feature.
            self.handle_data();

            // TODO: WFI on Cortex-M.
            // TODO: Timeout (idea: use a struct field)
        }

        self.rx_frame.check_frame()
    }

    /// Processes any received command.
    ///
    /// The context can be used by your router to make any resource or data
    /// available during the command processing. If you are using the
    /// [`DefaultRouter`], where the context is `()`, you can call `process`
    /// this way:
    ///
    /// ```
    /// # use ercp_basic::{Adapter, DefaultRouter, ErcpBasic, error::IoError};
    /// #
    /// # struct DummyAdapter;
    /// #
    /// # impl ercp_basic::Adapter for DummyAdapter {
    /// #    fn read(&mut self) -> Result<Option<u8>, IoError> { Ok(None) }
    /// #    fn write(&mut self, byte: u8) -> Result<(), IoError> { Ok(()) }
    /// # }
    /// #
    /// # let mut ercp = ErcpBasic::<_, _, 255>::new(DummyAdapter, DefaultRouter);
    /// ercp.process(&mut ());
    /// ```
    ///
    /// You **must** call this function regularly somewhere in your code for
    /// ERCP Basic to work properly. It could be run for instance in a specific
    /// task or thread.
    pub fn process(&mut self, context: &mut R::Context) {
        // TODO: Use next_command once it is in a sub-struct.
        if self.complete_frame_received() {
            match self.rx_frame.check_frame() {
                Ok(command) => {
                    if let Some(reply) = self.router.route(command, context) {
                        self.connection.send(reply);
                    }
                }

                Err(FrameError::InvalidCrc) => {
                    self.notify(nack!(nack_reason::INVALID_CRC));
                }

                Err(_) => unreachable!(),
            }

            self.reset_state();
        }
    }

    /// Sends a command to the peer device, and waits for a reply.
    ///
    /// This function is meant to be used to build *command methods* in a device
    /// driver, like in the example below.
    ///
    /// The returned value is the command (i.e. the reply) received from the
    /// peer device. To avoid copies, its value refers to the receive buffer, so
    /// you must free it after processing it, by using
    /// [`ErcpBasic::reset_state`]. If you need this value later, you should
    /// copy it yourself in some place.
    ///
    /// If you forget to call [`ErcpBasic::reset_state`], your device will not
    /// be able to receive any more commands. This is thankfully automatically
    /// handled if you use the [`ercp_basic_macros::command`] macro, which
    /// creates a wrapper around the command method to ensure the receiver state
    /// is always reset. This is what is shown in the example below.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::{
    ///     command, error::CommandError, Adapter, Command, DefaultRouter,
    ///     ErcpBasic, Error,
    /// };
    ///
    /// // It is always a good idea to represent the peer device as a struct,
    /// // owning an ERCP Basic driver instance.
    /// struct MyDevice<A: Adapter> {
    ///     // Using ercp as the name for the ERCP Basic driver is a convention.
    ///     // The #[command] attribute uses this fact, but you can still use
    ///     // a different name if you want. In this case, you must use
    ///     // #[command(self.field_name)] instead.
    ///     ercp: ErcpBasic<A, DefaultRouter, 255>,
    /// }
    ///
    /// const SOME_COMMAND: u8 = 0x42;
    /// const SOME_COMMAND_REPLY: u8 = 0x43;
    ///
    /// impl<A: Adapter> MyDevice<A> {
    ///     fn new(ercp: ErcpBasic<A, DefaultRouter, 255>) -> Self {
    ///         Self { ercp }
    ///     }
    ///
    ///     // This is a typical command method. Usage of the #[command]
    ///     // attribute ensures the ERCP Basic receiver state is properly reset
    ///     // after the method execution.
    ///     #[command]
    ///     fn some_command(&mut self, arg: u8) -> Result<u8, Error> {
    ///         // 1. Prepare your command.
    ///         let value = [arg];
    ///         let command = Command::new(SOME_COMMAND, &value)?;
    ///
    ///         // 2. Send the command to the peer device and wait for its reply.
    ///         let reply = self.ercp.command(command)?;
    ///
    ///         // 3. Check if the reply is correct and use its value.
    ///         if reply.command() == SOME_COMMAND_REPLY && reply.length() == 1 {
    ///             Ok(reply.value()[0])
    ///         } else {
    ///             Err(CommandError::UnexpectedReply.into())
    ///         }
    ///     }
    /// }
    /// ```
    pub fn command(&mut self, command: Command) -> Result<Command, Error> {
        self.connection.send(command)?;
        self.wait_for_command().map_err(Into::into)
    }

    /// Sends a notification to the peer device.
    ///
    /// This sends the command to the peer device like [`ErcpBasic::command`],
    /// but do not wait for a reply. There is no guarantee that the command has
    /// been received.
    pub fn notify(&mut self, command: Command) -> Result<(), Error> {
        self.connection.send(command)?;
        Ok(())
    }

    /// Pings the peer device.
    ///
    /// This sends a
    /// [`Ping()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ping),
    /// then blocks until the peer device replies. The result is `Ok(())` when
    /// the reply is an
    /// [`Ack()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ack).
    #[command(self)]
    pub fn ping(&mut self) -> Result<(), Error> {
        let reply = self.command(ping!())?;

        if reply.command() == ACK {
            Ok(())
        } else {
            Err(CommandError::UnexpectedReply.into())
        }
    }

    /// Resets the peer device.
    ///
    /// This sends a
    /// [`Reset()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#reset),
    /// then blocks until the peer device replies. The result is `Ok(())` when
    /// the reply is an
    /// [`Ack()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ack).
    /// If the peer device does not support resets, this returns a
    /// [`CommandError::UnhandledCommand`].
    #[command(self)]
    pub fn reset(&mut self) -> Result<(), Error> {
        let reply = self.command(reset!())?;

        match reply.command() {
            ACK => Ok(()),
            NACK => {
                if reply.value() == [nack_reason::UNKNOWN_COMMAND] {
                    Err(CommandError::UnhandledCommand.into())
                } else {
                    Err(CommandError::UnexpectedReply.into())
                }
            }

            _ => Err(CommandError::UnexpectedReply.into()),
        }
    }

    /// Gets the protocol version supported by the peer device.
    ///
    /// This sends a
    /// [`Protocol()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#protocol),
    /// then blocks until the peer device replies. The result is `Ok(version)`
    /// when the reply is a [`Protocol_Reply(major, minor,
    /// patch)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#protocol_replymajor-minor-patch).
    #[command(self)]
    pub fn protocol(&mut self) -> Result<Version, Error> {
        let reply = self.command(protocol!())?;

        if reply.command() == PROTOCOL_REPLY && reply.length() == 3 {
            let version = Version {
                major: reply.value()[0],
                minor: reply.value()[1],
                patch: reply.value()[2],
            };

            Ok(version)
        } else {
            Err(CommandError::UnexpectedReply.into())
        }
    }

    /// Gets the version of the given `component` in the peer device.
    ///
    /// This sends a
    /// [`Version(component)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#versioncomponent),
    /// then blocks until the peer device replies. The result is `Ok(size)` when
    /// the reply is a
    /// [`Version_Reply(version)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#version_replyversion).
    /// In this case, `version[0..size]` contains the version string, encoded in
    /// UTF-8. If the provided buffer is too short to hold the version string, a
    /// [`BufferError::TooShort`] is returned.
    ///
    /// Standard commponents from the ERCP Basic specification are defined in
    /// [`command::component`].
    #[command(self)]
    pub fn version(
        &mut self,
        component: u8,
        version: &mut [u8],
    ) -> Result<usize, Error> {
        let reply = self.command(version!(component))?;

        if reply.command() == VERSION_REPLY {
            if reply.value().len() <= version.len() {
                version[0..reply.value().len()].copy_from_slice(reply.value());
                Ok(reply.value().len())
            } else {
                Err(BufferError::TooShort.into())
            }
        } else {
            Err(CommandError::UnexpectedReply.into())
        }
    }

    /// Gets the version of the given `component` in the peer device, returning
    /// the result as a [`String`].
    ///
    /// This is the same as [`ErcpBasic::version`], but returning an owned
    /// [`String`] instead of writing to a provided buffer.
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    #[cfg(any(feature = "std", test))]
    #[command(self)]
    pub fn version_as_string(
        &mut self,
        component: u8,
    ) -> Result<String, Error> {
        let reply = self.command(version!(component))?;

        if reply.command() == VERSION_REPLY {
            let version = String::from_utf8(reply.value().into())?;
            Ok(version)
        } else {
            Err(CommandError::UnexpectedReply.into())
        }
    }

    /// Gets the maximum length accepted by the peer device.
    ///
    /// This sends a
    /// [`Max_Length()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#max_length),
    /// then blocks until the peer device replies. The result is
    /// `Ok(max_length)` when the reply is a
    /// [`Max_Length_Reply(max_length)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#max_length_replymax_length).
    #[command(self)]
    pub fn max_length(&mut self) -> Result<u8, Error> {
        let reply = self.command(max_length!())?;

        if reply.command() == MAX_LENGTH_REPLY && reply.length() == 1 {
            Ok(reply.value()[0])
        } else {
            Err(CommandError::UnexpectedReply.into())
        }
    }

    /// Gets the description of the peer device.
    ///
    /// This sends a
    /// [`Description()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#description),
    /// then blocks until the peer device replies. The result is `Ok(size)` when
    /// the reply is a
    /// [`Description_Reply(description)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#description_replydescription).
    /// In this case, `description[0..size]` contains the description, encoded
    /// in UTF-8. If the provided buffer is too short to hold the description, a
    /// [`BufferError::TooShort`] is returned.
    #[command(self)]
    pub fn description(
        &mut self,
        description: &mut [u8],
    ) -> Result<usize, Error> {
        let reply = self.command(description!())?;

        if reply.command() == DESCRIPTION_REPLY {
            if reply.value().len() <= description.len() {
                description[0..reply.value().len()]
                    .copy_from_slice(reply.value());

                Ok(reply.value().len())
            } else {
                Err(BufferError::TooShort.into())
            }
        } else {
            Err(CommandError::UnexpectedReply.into())
        }
    }

    /// Gets the description of the peer device, returning the result as a
    /// [`String`].
    ///
    /// This is the same as [`ErcpBasic::description`], but returning an owned
    /// [`String`] instead of writing to a provided buffer.
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    #[cfg(any(feature = "std", test))]
    #[command(self)]
    pub fn description_as_string(&mut self) -> Result<String, Error> {
        let reply = self.command(description!())?;

        if reply.command() == DESCRIPTION_REPLY {
            let description = String::from_utf8(reply.value().into())?;
            Ok(description)
        } else {
            Err(CommandError::UnexpectedReply.into())
        }
    }

    /// Sends a log message to the peer device.
    ///
    /// This sends a
    /// [`Log(message)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#logmessage)
    /// without waiting for an acknowledgement. There is no guarantee that any
    /// peer device receives the log.
    pub fn log(&mut self, message: &str) -> Result<(), Error> {
        let command = Command::log(message)?;
        self.notify(command)
    }

    /// Sends a log message to the peer device and waits for an acknlowledgement.
    ///
    /// This sends a
    /// [`Log(message)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#logmessage),
    /// then blocks until the peer device replies. The result is `Ok(())` when
    /// the reply is an
    /// [`Ack()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ack).
    #[command(self)]
    pub fn sync_log(&mut self, message: &str) -> Result<(), Error> {
        let command = Command::log(message)?;
        let reply = self.command(command)?;

        if reply.command() == ACK {
            Ok(())
        } else {
            Err(CommandError::UnexpectedReply.into())
        }
    }

    // TODO: Call this after handling the reply of a command, or to implement a
    // receive timeout.
    /// Resets the receive state machine and clears the frame buffer.
    pub fn reset_state(&mut self) {
        self.state = State::Ready;
        self.rx_frame.reset();
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

                    Err(FrameError::TooLong) => {
                        self.reset_state();
                        self.notify(nack!(nack_reason::TOO_LONG));
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

    impl<const MAX_LEN: usize> Router<MAX_LEN> for TestRouter {
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

    const MAX_LEN: usize = u8::MAX as usize;

    ////////////////////////////// Test setup //////////////////////////////

    fn setup(test: impl Fn(ErcpBasic<TestAdapter, TestRouter, MAX_LEN>)) {
        let adapter = TestAdapter::default();
        let router = TestRouter::default();
        let ercp = ErcpBasic::new(adapter, router);
        test(ercp);
    }

    /////////////////////////////// Strategy ///////////////////////////////

    fn ercp(
        state: State,
    ) -> impl Strategy<Value = ErcpBasic<TestAdapter, TestRouter, MAX_LEN>>
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

            ercp.receive(length);
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                nack!(nack_reason::TOO_LONG).as_frame()
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
            assert_eq!(ercp.next_command(), Some(Err(FrameError::InvalidCrc)));
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
            assert_eq!(ercp.wait_for_command(), Err(FrameError::InvalidCrc));
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
                // NOTE: Type inference does not work due to an issue in
                // serde-yaml: https://github.com/dtolnay/serde-yaml/issues/140
                &[] as &[u8]
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

            ercp.process(&mut ());
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                nack!(nack_reason::INVALID_CRC).as_frame()
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
                ercp.connection.adapter().test_send(&ack!().as_frame());

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

                assert_eq!(ercp.command(ping!()), Ok(reply));
            });
        }
    }

    #[test]
    fn command_returns_an_error_on_write_errors() {
        setup(|mut ercp| {
            ercp.connection.adapter().write_error = Some(IoError::IoError);
            assert_eq!(ercp.command(ping!()), Err(IoError::IoError.into()));
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

                assert_eq!(ercp.notify(command), Err(IoError::IoError.into()));
            })
        }
    }

    /////////////////////////////// Commands ///////////////////////////////

    #[test]
    fn ping_sends_a_ping() {
        setup(|mut ercp| {
            let expected_frame = ping!().as_frame();
            let reply_frame = ack!().as_frame();

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

                assert_eq!(
                    ercp.ping(),
                    Err(CommandError::UnexpectedReply.into())
                );
            });
        }
    }

    proptest! {
        #[test]
        fn ping_resets_the_state(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                ercp.ping().ok();
                assert_eq!(ercp.state, State::Ready);
            });
        }
    }

    #[test]
    fn reset_sends_a_reset() {
        setup(|mut ercp| {
            let expected_frame = reset!().as_frame();
            let reply_frame = ack!().as_frame();

            ercp.connection.adapter().test_send(&reply_frame);

            assert_eq!(ercp.reset(), Ok(()));
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                expected_frame
            );
        })
    }

    #[test]
    fn reset_returns_an_error_if_the_command_is_unhandled() {
        setup(|mut ercp| {
            let reply = nack!(nack_reason::UNKNOWN_COMMAND);
            ercp.connection.adapter().test_send(&reply.as_frame());

            assert_eq!(
                ercp.reset(),
                Err(CommandError::UnhandledCommand.into())
            );
        });
    }

    proptest! {
        #[test]
        fn reset_returns_an_error_on_unexpected_reply(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(command != ACK && command != NACK);

            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                assert_eq!(
                    ercp.reset(),
                    Err(CommandError::UnexpectedReply.into())
                );
            });
        }
    }

    proptest! {
        #[test]
        fn reset_resets_the_state(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                ercp.reset().ok();
                assert_eq!(ercp.state, State::Ready);
            });
        }
    }

    #[test]
    fn protocol_sends_a_protocol_command() {
        setup(|mut ercp| {
            let expected_frame = protocol!().as_frame();
            let reply_frame =
                protocol_reply!(version::PROTOCOL_VERSION).as_frame();

            ercp.connection.adapter().test_send(&reply_frame);

            assert!(ercp.protocol().is_ok());
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                expected_frame
            );
        })
    }

    proptest! {
        #[test]
        fn protocol_returns_the_received_protocol_version(
            major in 0..=u8::MAX,
            minor in 0..=u8::MAX,
            patch in 0..=u8::MAX,
        ) {
            setup(|mut ercp| {
                let version = Version { major, minor, patch };
                let reply_frame = protocol_reply!(version).as_frame();

                ercp.connection.adapter().test_send(&reply_frame);

                assert_eq!(
                    ercp.protocol(),
                    Ok(Version { major, minor, patch })
                );
            })
        }
    }

    proptest! {
        #[test]
        fn protocol_returns_an_error_on_unexpected_reply(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(command != PROTOCOL_REPLY || value.len() != 3);

            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                assert_eq!(
                    ercp.protocol(),
                    Err(CommandError::UnexpectedReply.into())
                );
            });
        }
    }

    proptest! {
        #[test]
        fn protocol_resets_the_state(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                ercp.protocol().ok();
                assert_eq!(ercp.state, State::Ready);
            });
        }
    }

    proptest! {
        #[test]
        fn version_sends_a_version_command(component in 0..=u8::MAX) {
            setup(|mut ercp| {
                let expected_frame = version!(component).as_frame();
                let reply_frame = version_reply!("").as_frame();

                ercp.connection.adapter().test_send(&reply_frame);

                assert!(ercp.version(component, &mut []).is_ok());
                assert_eq!(
                    ercp.connection.adapter().test_receive(),
                    expected_frame
                );
            })
        }
    }

    proptest! {
        #[test]
        fn version_copies_the_reply_to_the_provided_buffer(
            component in 0..=u8::MAX,
            version in ".{1,100}",
        ) {
            setup(|mut ercp| {
                let reply_frame = version_reply!(&version).as_frame();
                ercp.connection.adapter().test_send(&reply_frame);

                let mut buffer = [0; 255];

                assert!(ercp.version(component, &mut buffer).is_ok());
                assert_eq!(
                    &buffer[0..version.as_bytes().len()],
                    version.as_bytes()
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_returns_the_length_of_the_reply(
            component in 0..=u8::MAX,
            version in ".{1,100}",
        ) {
            setup(|mut ercp| {
                let reply_frame = version_reply!(&version).as_frame();
                ercp.connection.adapter().test_send(&reply_frame);

                assert_eq!(
                    ercp.version(component, &mut [0; 255]),
                    Ok(version.as_bytes().len())
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_returns_an_error_if_the_buffer_is_too_short_for_reply(
            component in 0..=u8::MAX,
            version in ".{1,100}",
        ) {
            setup(|mut ercp| {
                let reply_frame = version_reply!(&version).as_frame();
                ercp.connection.adapter().test_send(&reply_frame);

                assert_eq!(
                    ercp.version(component, &mut []),
                    Err(BufferError::TooShort.into())
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_returns_an_error_on_unexpected_reply(
            component in 0..=u8::MAX,
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(command != VERSION_REPLY);

            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                assert_eq!(
                    ercp.version(component, &mut []),
                    Err(CommandError::UnexpectedReply.into())
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_resets_the_state(
            component in 0..=u8::MAX,
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                ercp.version(component, &mut []).ok();
                assert_eq!(ercp.state, State::Ready);
            });
        }
    }

    proptest! {
        #[test]
            fn version_as_string_sends_a_version_command(
                component in 0..=u8::MAX,
            ) {
            setup(|mut ercp| {
                let expected_frame = version!(component).as_frame();
                let reply_frame = version_reply!("").as_frame();

                ercp.connection.adapter().test_send(&reply_frame);

                assert!(ercp.version_as_string(component).is_ok());
                assert_eq!(
                    ercp.connection.adapter().test_receive(),
                    expected_frame
                );
            })
        }
    }

    proptest! {
        #[test]
        fn version_as_string_returns_the_version(
            component in 0..=u8::MAX,
            version in ".{1,100}",
        ) {
            setup(|mut ercp| {
                let reply_frame = version_reply!(&version).as_frame();
                ercp.connection.adapter().test_send(&reply_frame);

                let result = ercp.version_as_string(component);
                assert!(result.is_ok());
                assert_eq!(&result.unwrap(), &version);
            });
        }
    }

    proptest! {
        #[test]
        fn version_as_string_returns_an_error_on_unexpected_reply(
            component in 0..=u8::MAX,
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(command != VERSION_REPLY);

            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                assert_eq!(
                    ercp.version_as_string(component),
                    Err(CommandError::UnexpectedReply.into())
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_as_string_resets_the_state(
            component in 0..=u8::MAX,
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                ercp.version_as_string(component).ok();
                assert_eq!(ercp.state, State::Ready);
            });
        }
    }

    #[test]
    fn max_length_sends_a_max_length_command() {
        setup(|mut ercp| {
            let expected_frame = max_length!().as_frame();
            let reply_frame = max_length_reply!(0).as_frame();

            ercp.connection.adapter().test_send(&reply_frame);

            assert!(ercp.max_length().is_ok());
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                expected_frame
            );
        })
    }

    proptest! {
        #[test]
        fn max_length_returns_the_received_maximum_length(
            max_length in 0..=u8::MAX,
        ) {
            setup(|mut ercp| {
                let reply_frame = max_length_reply!(max_length).as_frame();
                ercp.connection.adapter().test_send(&reply_frame);

                assert_eq!(
                    ercp.max_length(),
                    Ok(max_length)
                );
            });
        }
    }

    proptest! {
        #[test]
        fn max_length_returns_an_error_on_unexpected_reply(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(command != MAX_LENGTH_REPLY || value.len() != 1);

            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                assert_eq!(
                    ercp.max_length(),
                    Err(CommandError::UnexpectedReply.into())
                );
            });
        }
    }

    proptest! {
        #[test]
        fn max_length_resets_the_state(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                ercp.max_length().ok();
                assert_eq!(ercp.state, State::Ready);
            });
        }
    }

    #[test]
    fn description_sends_a_description_command() {
        setup(|mut ercp| {
            let expected_frame = description!().as_frame();
            let reply_frame = description_reply!("").as_frame();

            ercp.connection.adapter().test_send(&reply_frame);

            assert!(ercp.description(&mut []).is_ok());
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                expected_frame
            );
        })
    }

    proptest! {
        #[test]
        fn description_copies_the_reply_to_the_provided_buffer(
            description in ".{1,100}",
        ) {
            setup(|mut ercp| {
                let reply_frame = description_reply!(&description).as_frame();
                ercp.connection.adapter().test_send(&reply_frame);

                let mut buffer = [0; 255];

                assert!(ercp.description(&mut buffer).is_ok());
                assert_eq!(
                    &buffer[0..description.as_bytes().len()],
                    description.as_bytes()
                );
            });
        }
    }

    proptest! {
        #[test]
        fn description_returns_the_length_of_the_reply(
            description in ".{1,100}",
        ) {
            setup(|mut ercp| {
                let reply_frame = description_reply!(&description).as_frame();
                ercp.connection.adapter().test_send(&reply_frame);

                assert_eq!(
                    ercp.description(&mut [0; 255]),
                    Ok(description.as_bytes().len())
                );
            });
        }
    }

    proptest! {
        #[test]
        fn description_returns_an_error_if_the_buffer_is_too_short_for_reply(
            description in ".{1,100}",
        ) {
            setup(|mut ercp| {
                let reply_frame = description_reply!(&description).as_frame();
                ercp.connection.adapter().test_send(&reply_frame);

                assert_eq!(
                    ercp.description(&mut []),
                    Err(BufferError::TooShort.into())
                );
            });
        }
    }

    proptest! {
        #[test]
        fn description_returns_an_error_on_unexpected_reply(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(command != DESCRIPTION_REPLY);

            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                assert_eq!(
                    ercp.description(&mut []),
                    Err(CommandError::UnexpectedReply.into())
                );
            });
        }
    }

    proptest! {
        #[test]
        fn description_resets_the_state(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                ercp.description(&mut []).ok();
                assert_eq!(ercp.state, State::Ready);
            });
        }
    }

    #[test]
    fn description_as_string_sends_a_description_command() {
        setup(|mut ercp| {
            let expected_frame = description!().as_frame();
            let reply_frame = description_reply!("").as_frame();

            ercp.connection.adapter().test_send(&reply_frame);

            assert!(ercp.description_as_string().is_ok());
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                expected_frame
            );
        })
    }

    proptest! {
        #[test]
        fn description_as_string_returns_the_description(
            description in ".{1,100}",
        ) {
            setup(|mut ercp| {
                let reply_frame = description_reply!(&description).as_frame();
                ercp.connection.adapter().test_send(&reply_frame);

                let result = ercp.description_as_string();
                assert!(result.is_ok());
                assert_eq!(&result.unwrap(), &description);
            });
        }
    }

    proptest! {
        #[test]
        fn description_as_string_returns_an_error_on_unexpected_reply(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(command != DESCRIPTION_REPLY);

            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                assert_eq!(
                    ercp.description_as_string(),
                    Err(CommandError::UnexpectedReply.into())
                );
            });
        }
    }

    proptest! {
        #[test]
        fn description_as_string_resets_the_state(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                ercp.description_as_string().ok();
                assert_eq!(ercp.state, State::Ready);
            });
        }
    }

    proptest! {
        #[test]
        fn log_sends_a_log(message in ".{0,100}") {
            setup(|mut ercp| {
                let expected_frame = Command::log(&message).unwrap().as_frame();

                assert_eq!(ercp.log(&message), Ok(()));
                assert_eq!(
                    ercp.connection.adapter().test_receive(),
                    expected_frame
                );
            })
        }
    }

    proptest! {
        #[test]
        fn sync_log_sends_a_log(message in ".{0,100}") {
            setup(|mut ercp| {
                let expected_frame = Command::log(&message).unwrap().as_frame();
                let reply_frame = ack!().as_frame();

                ercp.connection.adapter().test_send(&reply_frame);

                assert_eq!(ercp.sync_log(&message), Ok(()));
                assert_eq!(
                    ercp.connection.adapter().test_receive(),
                    expected_frame
                );
            })
        }
    }

    proptest! {
        #[test]
        fn sync_log_returns_an_error_on_unexpected_reply(
            message in ".{0,100}",
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(command != ACK);

            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                assert_eq!(
                    ercp.sync_log(&message),
                    Err(CommandError::UnexpectedReply.into())
                );
            });
        }
    }

    proptest! {
        #[test]
        fn sync_log_resets_the_state(
            message in ".{0,100}",
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut ercp| {
                let reply = Command::new(command, &value).unwrap();
                ercp.connection.adapter().test_send(&reply.as_frame());

                ercp.sync_log(&message).ok();
                assert_eq!(ercp.state, State::Ready);
            });
        }
    }
}
