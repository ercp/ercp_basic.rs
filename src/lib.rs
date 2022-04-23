// Copyright 2021-2022 Jean-Philippe Cugnet
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

//! An implementation of ERCP Basic in Rust.

#![cfg_attr(all(not(feature = "std"), not(test)), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![deny(missing_docs)]
#![deny(unsafe_code)]
#![deny(unused_must_use)]

pub mod adapter;
pub mod command;
pub mod error;
pub mod router;
pub mod version;

mod connection;
mod crc;
mod receiver;

pub use ercp_basic_macros::command;

pub use adapter::Adapter;
pub use command::Command;
pub use error::*;
pub use router::{DefaultRouter, Router};
pub use version::Version;

use command::{
    nack_reason, NewCommandError, ACK, DESCRIPTION_REPLY, MAX_LENGTH_REPLY,
    NACK, PROTOCOL_REPLY, VERSION_REPLY,
};
use connection::Connection;
use receiver::{Receiver, StandardReceiver};

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
/// * instantiate an ERCP Basic driver on the wanted connection with
///   [`ErcpBasic::new`],
/// * call [`ErcpBasic::accept_command`] in a loop.
///
/// To have a more fine-grained control on when the different steps occur, you
/// can replace the [`ErcpBasic::accept_command`] loop with:
/// * a call to [`ErcpBasic::handle_data`] to handle incoming data (this should
///   be done in the handler for the “data available” event of your connection),
/// * a call to [`ErcpBasic::process`] to process incoming commands when a
///   complete frame is available, typically in a dedicated task / thread.
#[derive(Debug)]
pub struct ErcpBasic<
    A: Adapter,
    R: Router<MAX_LEN>,
    const MAX_LEN: usize = 255,
    Re: Receiver = StandardReceiver<MAX_LEN>,
> {
    receiver: Re,
    connection: Connection<A>,
    router: R,
}

/// An ERCP Basic commander.
///
/// A commander can only be built by [`ErcpBasic::command`].
pub struct Commander<
    'a,
    A: Adapter,
    R: Router<MAX_LEN>,
    const MAX_LEN: usize,
    Re: Receiver,
> {
    ercp: &'a mut ErcpBasic<A, R, MAX_LEN, Re>,
}

// TODO: Put elsewhere.
const EOT: u8 = 0x04;

impl<A: Adapter, R: Router<MAX_LEN>, const MAX_LEN: usize, Re: Receiver>
    ErcpBasic<A, R, MAX_LEN, Re>
{
    /// Instantiates an ERCP Basic driver.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::{ErcpBasic, DefaultRouter};
    ///
    /// # use ercp_basic::Adapter;
    /// #
    /// # struct SomeAdapter;
    /// #
    /// # impl SomeAdapter { fn new() -> Self { SomeAdapter } }
    /// #
    /// # impl Adapter for SomeAdapter {
    /// #    type Error = ();
    /// #    fn read(&mut self) -> Result<Option<u8>, ()> { Ok(None) }
    /// #    fn write(&mut self, byte: u8) -> Result<(), ()> { Ok(()) }
    /// # }
    /// #
    /// // Instantiate an adapter matching your underlying layer.
    /// let adapter = SomeAdapter::new(/* parameters omitted */);
    ///
    /// // Instantiate an ERCP Basic driver using the default router. Here we
    /// // need to annotate the type, because the compiler is not (yet) able to
    /// // infer it when it contains a default const generic.
    /// let ercp: ErcpBasic<_, _> = ErcpBasic::new(adapter, DefaultRouter);
    /// ```
    pub fn new(adapter: A, router: R) -> Self {
        Self {
            receiver: Receiver::new(),
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
    ///
    /// # Errors
    ///
    /// If the connection adapter encounters an error while trying to read or
    /// write data, this function stops and forwards the error from the adapter.
    pub fn handle_data(&mut self) -> Result<(), A::Error> {
        while let Some(byte) = self.connection.read()? {
            if let Err(ReceiveError::TooLong) = self.receiver.receive(byte) {
                self.notify(nack!(nack_reason::TOO_LONG))?;
            }
        }

        Ok(())
    }

    /// Handles incoming data, returning an error on incorrect input.
    ///
    /// This function behaves like [`ErcpBasic::handle_data`], but stops when
    /// the receive state machine encounters an error, instead of ignoring it.
    ///
    /// Usually, you don’t need such detail, except if you want to log incorrect
    /// inputs in your system.
    ///
    /// # Errors
    ///
    /// This function returns two levels of errors:
    ///
    /// * errors from the connection adapter, in case of read or write error,
    /// * errors from the receive state machine.
    ///
    /// # Example
    ///
    /// ```
    /// # use ercp_basic::{Adapter, DefaultRouter, ErcpBasic};
    /// #
    /// # struct DummyAdapter;
    /// #
    /// # impl Adapter for DummyAdapter {
    /// #    type Error = ();
    /// #    fn read(&mut self) -> Result<Option<u8>, ()> { Ok(None) }
    /// #    fn write(&mut self, byte: u8) -> Result<(), ()> { Ok(()) }
    /// # }
    /// #
    /// # let mut ercp = ErcpBasic::<_, _>::new(DummyAdapter, DefaultRouter);
    /// // You should call handle_data_fallible in a loop to handle the errors,
    /// // yet avoiding to drop some data. If it returns Ok(Ok(())), that means
    /// // there is no more data to handle.
    /// while let Ok(Err(error)) = ercp.handle_data_fallible() {
    ///     // Do something with `error`.
    /// }
    /// ```
    pub fn handle_data_fallible(
        &mut self,
    ) -> Result<Result<(), ReceiveError>, A::Error> {
        while let Some(byte) = self.connection.read()? {
            match self.receiver.receive(byte) {
                Ok(()) => (),
                Err(ReceiveError::TooLong) => {
                    self.notify(nack!(nack_reason::TOO_LONG))?;
                    return Ok(Err(ReceiveError::TooLong));
                }
                Err(error) => return Ok(Err(error)),
            }
        }

        Ok(Ok(()))
    }

    /// Returns wether a complete frame has been received.
    ///
    /// If it returns `true`, you should then call `process`.
    pub fn complete_frame_received(&self) -> bool {
        self.receiver.complete_frame_received()
    }

    /// Processes any received command.
    ///
    /// # Errors
    ///
    /// If the connection adapter encounters an error while trying to write the
    /// reply or a notification, this function forwards it error from the
    /// adapter.
    ///
    /// # Example
    ///
    /// The context can be used by your router to make any resource or data
    /// available during the command processing. If you are using the
    /// [`DefaultRouter`], where the context is `()`, you can call `process`
    /// this way:
    ///
    /// ```
    /// # use ercp_basic::{Adapter, DefaultRouter, ErcpBasic};
    /// #
    /// # struct DummyAdapter;
    /// #
    /// # impl Adapter for DummyAdapter {
    /// #    type Error = ();
    /// #    fn read(&mut self) -> Result<Option<u8>, ()> { Ok(None) }
    /// #    fn write(&mut self, byte: u8) -> Result<(), ()> { Ok(()) }
    /// # }
    /// #
    /// # let mut ercp = ErcpBasic::<_, _>::new(DummyAdapter, DefaultRouter);
    /// if let Err(e) = ercp.process(&mut ()) {
    ///     // Do something with the error.
    /// }
    /// ```
    ///
    /// You **must** call this function regularly somewhere in your code for
    /// ERCP Basic to work properly. It could be run for instance in a specific
    /// task or thread.
    //
    // NOTE: While `process` is not a command, the state must be reset after its
    // execution, even when it fails. As the `command` attribute simply wraps a
    // function to achieve exactly this goal, let’s use it here.
    #[command(self)]
    pub fn process(
        &mut self,
        context: &mut R::Context,
    ) -> Result<(), A::Error> {
        // TODO: Use self.receiver.next_command().
        if self.complete_frame_received() {
            match self.receiver.check_frame() {
                Ok(command) => {
                    if let Some(reply) = self.router.route(command, context) {
                        self.connection.send(reply)?;
                    }
                }

                Err(FrameError::InvalidCrc) => {
                    self.notify(nack!(nack_reason::INVALID_CRC))?;
                }

                // REVIEW: This should not be reachable at this point.
                Err(FrameError::TooLong) => unreachable!(),
            }
        }

        Ok(())
    }

    // TODO: Maybe put above handle_data and process? And update the docs?
    /// Blocks until a command has been received an process it.
    ///
    /// This is an alternative to calling [`ErcpBasic::handle_data`] and
    /// [`ErcpBasic::process`] directly which can be used to integrate ERCP
    /// Basic in a very simple event loop.
    ///
    /// # Errors
    ///
    /// If the connection adapter encounters an error while trying to read data,
    /// this function stops and forwards the error from the adapter.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use ercp_basic::{Adapter, DefaultRouter, ErcpBasic};
    /// #
    /// # struct DummyAdapter;
    /// #
    /// # impl Adapter for DummyAdapter {
    /// #    type Error = ();
    /// #    fn read(&mut self) -> Result<Option<u8>, ()> { Ok(None) }
    /// #    fn write(&mut self, byte: u8) -> Result<(), ()> { Ok(()) }
    /// # }
    /// #
    /// # let mut ercp = ErcpBasic::<_, _>::new(DummyAdapter, DefaultRouter);
    /// loop {
    ///     if let Err(e) = ercp.accept_command(&mut ()) {
    ///         // If the connection adapter has encountered an error. You can
    ///         // just retry gracefully, log the error, or take some action.
    ///     }
    ///
    ///     // Optionally do some post-processing.
    /// }
    /// ```
    pub fn accept_command(
        &mut self,
        context: &mut R::Context,
    ) -> Result<(), A::Error> {
        self.wait_for_command()?;
        self.process(context)?;
        Ok(())
    }

    /// Builds a custom command.
    ///
    /// This function is meant to be used to build *command methods* in a device
    /// driver, like in the example below. It takes a closure as argument, in
    /// which a commander is made available so you can transcieve a command and
    /// its reply.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::{
    ///     error::CommandResult, Adapter, Command, DefaultRouter, ErcpBasic,
    /// };
    ///
    /// // It is always a good idea to represent the peer device as a struct,
    /// // owning an ERCP Basic driver instance.
    /// struct MyDevice<A: Adapter> {
    ///     ercp: ErcpBasic<A, DefaultRouter>,
    /// }
    ///
    /// // When a command can return an error, you should create a type for
    /// // this.
    /// enum SomeCommandError {
    ///     UnexpectedReply,
    /// }
    ///
    /// const SOME_COMMAND: u8 = 0x42;
    /// const SOME_COMMAND_REPLY: u8 = 0x43;
    ///
    /// impl<A: Adapter> MyDevice<A> {
    ///     fn new(ercp: ErcpBasic<A, DefaultRouter>) -> Self {
    ///         Self { ercp }
    ///     }
    ///
    ///     // This is a typical command method.
    ///     //
    ///     // Please note the return type: CommandResult<T, E, IoError>.
    ///     // This is a type alias to Result<Result<T, E>, CommandError<IoError>>.
    ///     // Using two levels of results helps to separate the command-specific
    ///     // errors `E` from the system-level `CommandError` (i.e. I/O errors
    ///     // and frame errors).
    ///     fn some_command(&mut self, arg: u8) -> CommandResult<u8, SomeCommandError, A::Error> {
    ///         // The ERCP Basic driver itself cannot transcieve commands. By
    ///         // calling the command method, you gain access to a commander
    ///         // you can then use to actually transcieve.
    ///         self.ercp.command(|commander| {
    ///             // 1. Prepare your command.
    ///             let value = [arg];
    ///             // NOTE(unwrap): We control the size of `value`, and know it
    ///             // is smaller than u8::MAX.
    ///             let command = Command::new(SOME_COMMAND, &value).unwrap();
    ///
    ///             // 2. Send the command to the peer device and wait for its
    ///             // reply.
    ///             //
    ///             // Note that we can use `?` to propagate system-level errors.
    ///             let reply = commander.transcieve(command)?;
    ///
    ///             // 3. Check if the reply is correct and use its value.
    ///             if reply.code() == SOME_COMMAND_REPLY && reply.length() == 1 {
    ///                 // Don’t forget to wrap your result twice.
    ///                 Ok(Ok(reply.value()[0]))
    ///             } else {
    ///                 // Same goes for errors: the transaction has gone
    ///                 // smoothly on a system level (outside Ok), but there is
    ///                 // a command-specific error (inside Err).
    ///                 Ok(Err(SomeCommandError::UnexpectedReply))
    ///             }
    ///         })
    ///     }
    /// }
    /// ```
    pub fn command<T>(
        &mut self,
        mut callback: impl FnMut(&mut Commander<A, R, MAX_LEN, Re>) -> T,
    ) -> T {
        let result = callback(&mut Commander { ercp: self });
        self.reset_state();
        result
    }

    /// Sends a notification to the peer device.
    ///
    /// This sends the command to the peer device like [`ErcpBasic::command`],
    /// but do not wait for a reply. There is no guarantee that the command has
    /// been received.
    pub fn notify(&mut self, command: Command) -> Result<(), A::Error> {
        self.connection.send(command)?;
        Ok(())
    }

    /// Pings the peer device.
    ///
    /// This sends a
    /// [`Ping()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ping),
    /// then blocks until the peer device replies. The result is `Ok(Ok(()))`
    /// when the reply is an
    /// [`Ack()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ack).
    pub fn ping(&mut self) -> CommandResult<(), PingError, A::Error> {
        self.command(|commander| {
            let reply = commander.transcieve(ping!())?;

            if reply.code() == ACK {
                Ok(Ok(()))
            } else {
                Ok(Err(PingError::UnexpectedReply))
            }
        })
    }

    /// Resets the peer device.
    ///
    /// This sends a
    /// [`Reset()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#reset),
    /// then blocks until the peer device replies. The result is `Ok(Ok(()))`
    /// when the reply is an
    /// [`Ack()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ack).
    /// If the peer device does not support resets, this returns
    /// `Ok(Err(ResetError::UnhandledCommand))`.
    pub fn reset(&mut self) -> CommandResult<(), ResetError, A::Error> {
        self.command(|commander| {
            let reply = commander.transcieve(reset!())?;

            match reply.code() {
                ACK => Ok(Ok(())),
                NACK => {
                    if reply.value() == [nack_reason::UNKNOWN_COMMAND] {
                        Ok(Err(ResetError::UnhandledCommand))
                    } else {
                        Ok(Err(ResetError::UnexpectedReply))
                    }
                }

                _ => Ok(Err(ResetError::UnexpectedReply)),
            }
        })
    }

    /// Gets the protocol version supported by the peer device.
    ///
    /// This sends a
    /// [`Protocol()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#protocol),
    /// then blocks until the peer device replies. The result is
    /// `Ok(Ok(version))` when the reply is a [`Protocol_Reply(major, minor,
    /// patch)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#protocol_replymajor-minor-patch).
    pub fn protocol(
        &mut self,
    ) -> CommandResult<Version, ProtocolError, A::Error> {
        self.command(|commander| {
            let reply = commander.transcieve(protocol!())?;

            if reply.code() == PROTOCOL_REPLY && reply.length() == 3 {
                let version = Version {
                    major: reply.value()[0],
                    minor: reply.value()[1],
                    patch: reply.value()[2],
                };

                Ok(Ok(version))
            } else {
                Ok(Err(ProtocolError::UnexpectedReply))
            }
        })
    }

    /// Gets the version of the given `component` in the peer device.
    ///
    /// This sends a
    /// [`Version(component)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#versioncomponent),
    /// then blocks until the peer device replies. The result is `Ok(Ok(size))`
    /// when the reply is a
    /// [`Version_Reply(version)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#version_replyversion).
    /// In this case, `version[0..size]` contains the version string, encoded in
    /// UTF-8. If the provided buffer is too short to hold the version string,
    /// `Ok(Err(VersionError::BufferTooShort))` is returned.
    ///
    /// Standard commponents from the ERCP Basic specification are defined in
    /// [`command::component`].
    pub fn version(
        &mut self,
        component: u8,
        version: &mut [u8],
    ) -> CommandResult<usize, VersionError, A::Error> {
        self.command(|commander| {
            let reply = commander.transcieve(version!(component))?;

            if reply.code() == VERSION_REPLY {
                let length = reply.value().len();
                if length <= version.len() {
                    version[0..length].copy_from_slice(reply.value());
                    Ok(Ok(length))
                } else {
                    Ok(Err(VersionError::BufferTooShort))
                }
            } else {
                Ok(Err(VersionError::UnexpectedReply))
            }
        })
    }

    /// Gets the version of the given `component` in the peer device, returning
    /// the result as a [`String`].
    ///
    /// This is the same as [`ErcpBasic::version`], but returning an owned
    /// [`String`] instead of writing to a provided buffer.
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    #[cfg(any(feature = "std", test))]
    pub fn version_as_string(
        &mut self,
        component: u8,
    ) -> CommandResult<String, VersionAsStringError, A::Error> {
        self.command(|commander| {
            let reply = commander.transcieve(version!(component))?;

            if reply.code() == VERSION_REPLY {
                Ok(String::from_utf8(reply.value().into()).map_err(Into::into))
            } else {
                Ok(Err(VersionAsStringError::UnexpectedReply))
            }
        })
    }

    /// Gets the maximum length accepted by the peer device.
    ///
    /// This sends a
    /// [`Max_Length()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#max_length),
    /// then blocks until the peer device replies. The result is
    /// `Ok(Ok(max_length))` when the reply is a
    /// [`Max_Length_Reply(max_length)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#max_length_replymax_length).
    pub fn max_length(
        &mut self,
    ) -> CommandResult<u8, MaxLengthError, A::Error> {
        self.command(|commander| {
            let reply = commander.transcieve(max_length!())?;

            if reply.code() == MAX_LENGTH_REPLY && reply.length() == 1 {
                Ok(Ok(reply.value()[0]))
            } else {
                Ok(Err(MaxLengthError::UnexpectedReply))
            }
        })
    }

    /// Gets the description of the peer device.
    ///
    /// This sends a
    /// [`Description()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#description),
    /// then blocks until the peer device replies. The result is `Ok(Ok(size))`
    /// when the reply is a
    /// [`Description_Reply(description)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#description_replydescription).
    /// In this case, `description[0..size]` contains the description, encoded
    /// in UTF-8. If the provided buffer is too short to hold the description, a
    /// `Ok(Err(DescriptionError::BufferTooShort))` is returned.
    pub fn description(
        &mut self,
        description: &mut [u8],
    ) -> CommandResult<usize, DescriptionError, A::Error> {
        self.command(|commander| {
            let reply = commander.transcieve(description!())?;

            if reply.code() == DESCRIPTION_REPLY {
                let length = reply.value().len();
                if length <= description.len() {
                    description[0..length].copy_from_slice(reply.value());
                    Ok(Ok(length))
                } else {
                    Ok(Err(DescriptionError::BufferTooShort))
                }
            } else {
                Ok(Err(DescriptionError::UnexpectedReply))
            }
        })
    }

    /// Gets the description of the peer device, returning the result as a
    /// [`String`].
    ///
    /// This is the same as [`ErcpBasic::description`], but returning an owned
    /// [`String`] instead of writing to a provided buffer.
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    #[cfg(any(feature = "std", test))]
    pub fn description_as_string(
        &mut self,
    ) -> CommandResult<String, DescriptionAsStringError, A::Error> {
        self.command(|commander| {
            let reply = commander.transcieve(description!())?;

            if reply.code() == DESCRIPTION_REPLY {
                Ok(String::from_utf8(reply.value().into()).map_err(Into::into))
            } else {
                Ok(Err(DescriptionAsStringError::UnexpectedReply))
            }
        })
    }

    /// Sends a log message to the peer device.
    ///
    /// This sends a
    /// [`Log(message)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#logmessage)
    /// without waiting for an acknowledgement. There is no guarantee that any
    /// peer device receives the log.
    pub fn log(
        &mut self,
        message: &str,
    ) -> CommandResult<(), LogError, A::Error> {
        if let Ok(command) = Command::log(message) {
            self.notify(command).map_err(CommandError::IoError)?;
            Ok(Ok(()))
        } else {
            Ok(Err(LogError::TooLong))
        }
    }

    /// Sends a log message to the peer device and waits for an acknlowledgement.
    ///
    /// This sends a
    /// [`Log(message)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#logmessage),
    /// then blocks until the peer device replies. The result is `Ok(Ok(()))`
    /// when the reply is an
    /// [`Ack()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ack).
    pub fn sync_log(
        &mut self,
        message: &str,
    ) -> CommandResult<(), LogError, A::Error> {
        self.command(|commander| {
            let command = match Command::log(message) {
                Ok(command) => command,
                Err(NewCommandError::TooLong) => {
                    return Ok(Err(LogError::TooLong))
                }
            };

            let reply = commander.transcieve(command)?;

            if reply.code() == ACK {
                Ok(Ok(()))
            } else {
                Ok(Err(LogError::UnexpectedReply))
            }
        })
    }

    // TODO: Call this after handling the reply of a command, or to implement a
    // receive timeout.
    /// Resets the receive state machine and clears the frame buffer.
    pub fn reset_state(&mut self) {
        self.receiver.reset()
    }

    /// Blocks until a complete frame has been received.
    fn wait_for_command(&mut self) -> Result<(), A::Error> {
        while !self.complete_frame_received() {
            // TODO: Do different things depending on features.

            // TODO: Only with the blocking feature.
            self.handle_data()?;

            // TODO: WFI on Cortex-M.
            // TODO: Timeout (idea: use a struct field)
        }

        Ok(())
    }
}

impl<
        'a,
        A: Adapter,
        R: Router<MAX_LEN>,
        const MAX_LEN: usize,
        Re: Receiver,
    > Commander<'a, A, R, MAX_LEN, Re>
{
    /// Sends a command to the peer device, and waits for a reply.
    ///
    /// This function is meant to be used inside a command closure. Please see
    /// the documentation for [`ErcpBasic::command`].
    pub fn transcieve(
        &mut self,
        command: Command,
    ) -> Result<Command, CommandError<A::Error>> {
        self.ercp
            .connection
            .send(command)
            .map_err(CommandError::IoError)?;

        self.wait_for_command_fallible()
            .map_err(CommandError::IoError)?
            .map_err(Into::into)
            .map_err(CommandError::ReceivedFrameError)?;

        let reply = self
            .ercp
            .receiver
            .check_frame()
            .map_err(Into::into)
            .map_err(CommandError::ReceivedFrameError)?;

        // Check for any frame-level error notification from the peer.
        match (reply.code(), reply.value()) {
            (NACK, [nack_reason::TOO_LONG]) => {
                Err(CommandError::SentFrameError(FrameError::TooLong))
            }

            (NACK, [nack_reason::INVALID_CRC]) => {
                Err(CommandError::SentFrameError(FrameError::InvalidCrc))
            }

            _ => Ok(reply),
        }
    }

    /// Blocks until a complete frame has been received.
    fn wait_for_command_fallible(
        &mut self,
    ) -> Result<Result<(), ReceiveError>, A::Error> {
        while !self.ercp.complete_frame_received() {
            // TODO: Do different things depending on features.

            // TODO: Only with the blocking feature.
            if let Err(error) = self.ercp.handle_data_fallible()? {
                return Ok(Err(error));
            }

            // TODO: WFI on Cortex-M.
            // TODO: Timeout (idea: use a struct field)
        }

        Ok(Ok(()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use connection::tests::TestAdapter;

    use proptest::collection::vec;
    use proptest::prelude::*;

    #[derive(Debug)]
    struct TestReceiver {
        receive: ReceiveInfo,
        complete_frame_received: bool,
        check_frame: CheckFrameInfo,
        reset: ResetInfo,
    }

    #[derive(Debug, Default)]
    struct ReceiveInfo {
        call_count: usize,
        data: Vec<u8>,
        results: Option<Vec<Result<(), ReceiveError>>>,
    }

    #[derive(Debug)]
    struct CheckFrameInfo {
        result: Result<OwnedCommand, FrameError>,
    }

    #[derive(Debug, Default)]
    struct ResetInfo {
        call_count: usize,
    }

    #[derive(Debug, Default)]
    struct TestRouter {
        last_command: Option<OwnedCommand>,
        reply: Option<OwnedCommand>,
    }

    // IDEA: Try to remove the need for owned commands.
    #[derive(Debug, Default, Clone, PartialEq)]
    struct OwnedCommand {
        code: u8,
        value: Vec<u8>,
    }

    impl Receiver for TestReceiver {
        fn new() -> Self {
            Self {
                receive: ReceiveInfo::default(),
                complete_frame_received: false,
                check_frame: CheckFrameInfo {
                    result: Err(FrameError::InvalidCrc),
                },
                reset: ResetInfo::default(),
            }
        }

        fn receive(&mut self, byte: u8) -> Result<(), ReceiveError> {
            self.receive.call_count += 1;
            self.receive.data.push(byte);

            match &mut self.receive.results {
                None => Ok(()),
                Some(results) => results
                    .pop()
                    .expect("receive has been called more than expected"),
            }
        }

        fn complete_frame_received(&self) -> bool {
            self.complete_frame_received
        }

        fn check_frame(&self) -> Result<Command, FrameError> {
            self.check_frame
                .result
                .as_ref()
                .map(|command| {
                    Command::new(command.code, &command.value).unwrap()
                })
                .map_err(|&e| e)
        }

        fn reset(&mut self) {
            self.reset.call_count += 1;
        }
    }

    impl<const MAX_LEN: usize> Router<MAX_LEN> for TestRouter {
        type Context = ();

        fn route(&mut self, command: Command, _: &mut ()) -> Option<Command> {
            self.last_command = Some(command.into());
            self.reply.as_ref().map(|command| {
                Command::new(command.code, &command.value).unwrap()
            })
        }
    }

    impl<'a> From<Command<'a>> for OwnedCommand {
        fn from(command: Command<'a>) -> Self {
            Self {
                code: command.code(),
                value: command.value().into(),
            }
        }
    }

    impl<'a> From<&Command<'a>> for OwnedCommand {
        fn from(command: &Command<'a>) -> Self {
            Self {
                code: command.code(),
                value: command.value().into(),
            }
        }
    }

    impl<'a> PartialEq<Command<'a>> for OwnedCommand {
        fn eq(&self, other: &Command) -> bool {
            self.code == other.code() && self.value == other.value()
        }
    }

    ////////////////////////////// Test setup //////////////////////////////

    fn setup(
        test: impl Fn(ErcpBasic<TestAdapter, TestRouter, 255, TestReceiver>),
    ) {
        let adapter = TestAdapter::default();
        let router = TestRouter::default();
        let ercp = ErcpBasic::new(adapter, router);
        test(ercp);
    }

    fn setup_commander(
        test: impl Fn(Commander<TestAdapter, TestRouter, 255, TestReceiver>),
    ) {
        let adapter = TestAdapter::default();
        let router = TestRouter::default();
        let mut ercp = ErcpBasic::new(adapter, router);
        let commander = Commander { ercp: &mut ercp };
        test(commander);
    }

    ////////////////////////////// Data input //////////////////////////////

    #[test]
    fn handle_data_returns_ok() {
        setup(|mut ercp| {
            assert_eq!(ercp.handle_data(), Ok(()));
        });
    }

    proptest! {
        #[test]
        fn handle_data_calls_receive_while_there_is_data_to_handle(
            frame in vec(0..=u8::MAX, 0..=1000),
        ) {
            setup(|mut ercp| {
                ercp.connection.adapter().test_send(&frame);
                ercp.handle_data().ok();
                assert_eq!(ercp.receiver.receive.call_count, frame.len());
            });
        }
    }

    proptest! {
        #[test]
        fn handle_data_calls_receive_with_bytes_from_the_frame(
            frame in vec(0..=u8::MAX, 0..=1000),
        ) {
            setup(|mut ercp| {
                ercp.connection.adapter().test_send(&frame);
                ercp.handle_data().ok();
                assert_eq!(ercp.receiver.receive.data, frame);
            });
        }
    }

    #[test]
    fn handle_data_does_nothing_on_no_data() {
        setup(|mut ercp| {
            ercp.handle_data().ok();
            assert_eq!(ercp.receiver.receive.call_count, 0);
        });
    }

    #[test]
    fn handle_data_returns_an_error_on_read_errors() {
        setup(|mut ercp| {
            ercp.connection.adapter().read_error = Some(());
            assert_eq!(ercp.handle_data(), Err(()));
        });
    }

    #[test]
    fn handle_data_ignores_receive_errors() {
        setup(|mut ercp| {
            let frame = [0; 4];
            let errors = vec![
                Err(ReceiveError::UnexpectedValue),
                Err(ReceiveError::TooLong),
                Err(ReceiveError::NotEot),
                Err(ReceiveError::Overflow),
            ];

            ercp.connection.adapter().test_send(&frame);
            ercp.receiver.receive.results = Some(errors);

            assert_eq!(ercp.handle_data(), Ok(()));
            assert_eq!(ercp.receiver.receive.data, frame);
        });
    }

    #[test]
    fn handle_data_sends_a_nack_if_the_receiver_reports_a_too_long_length() {
        setup(|mut ercp| {
            ercp.connection.adapter().test_send(&[0]);
            ercp.receiver.receive.results =
                Some(vec![Err(ReceiveError::TooLong)]);

            ercp.handle_data().ok();
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                nack!(nack_reason::TOO_LONG).as_frame()
            );
        });
    }

    #[test]
    fn handle_data_fallible_returns_ok() {
        setup(|mut ercp| {
            assert_eq!(ercp.handle_data_fallible(), Ok(Ok(())));
        });
    }

    proptest! {
        #[test]
        fn handle_data_fallible_calls_receive_while_there_is_data_to_handle(
            frame in vec(0..=u8::MAX, 0..=1000),
        ) {
            setup(|mut ercp| {
                ercp.connection.adapter().test_send(&frame);
                ercp.handle_data_fallible().ok();
                assert_eq!(ercp.receiver.receive.call_count, frame.len());
            });
        }
    }

    proptest! {
        #[test]
        fn handle_data_fallible_calls_receive_with_bytes_from_the_frame(
            frame in vec(0..=u8::MAX, 0..=1000),
        ) {
            setup(|mut ercp| {
                ercp.connection.adapter().test_send(&frame);
                ercp.handle_data_fallible().ok();
                assert_eq!(ercp.receiver.receive.data, frame);
            });
        }
    }

    #[test]
    fn handle_data_fallible_does_nothing_on_no_data() {
        setup(|mut ercp| {
            ercp.handle_data_fallible().ok();
            assert_eq!(ercp.receiver.receive.call_count, 0);
        });
    }

    #[test]
    fn handle_data_fallible_returns_an_error_on_read_errors() {
        setup(|mut ercp| {
            ercp.connection.adapter().read_error = Some(());
            assert_eq!(ercp.handle_data_fallible(), Err(()));
        });
    }

    #[test]
    fn handle_data_fallible_returns_an_error_on_receive_errors() {
        setup(|mut ercp| {
            ercp.connection.adapter().test_send(&[0]);
            ercp.receiver.receive.results =
                Some(vec![Err(ReceiveError::UnexpectedValue)]);

            assert_eq!(
                ercp.handle_data_fallible(),
                Ok(Err(ReceiveError::UnexpectedValue))
            );
        });
    }

    #[test]
    fn handle_data_fallible_stops_to_handle_data_on_receive_errors() {
        setup(|mut ercp| {
            ercp.connection.adapter().test_send(&[0; 2]);
            ercp.receiver.receive.results =
                Some(vec![Err(ReceiveError::UnexpectedValue)]);

            ercp.handle_data_fallible().err();
            assert_eq!(ercp.receiver.receive.call_count, 1);
        });
    }

    #[test]
    fn handle_data_fallible_returns_an_error_if_the_receiver_reports_a_too_long_length(
    ) {
        setup(|mut ercp| {
            ercp.connection.adapter().test_send(&[0]);
            ercp.receiver.receive.results =
                Some(vec![Err(ReceiveError::TooLong)]);

            assert_eq!(
                ercp.handle_data_fallible(),
                Ok(Err(ReceiveError::TooLong))
            );
        })
    }

    #[test]
    fn handle_data_fallible_sends_a_nack_if_the_receiver_reports_a_too_long_length(
    ) {
        setup(|mut ercp| {
            ercp.connection.adapter().test_send(&[0]);
            ercp.receiver.receive.results =
                Some(vec![Err(ReceiveError::TooLong)]);

            ercp.handle_data_fallible().ok();
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                nack!(nack_reason::TOO_LONG).as_frame()
            );
        });
    }

    proptest! {
        #[test]
        fn complete_frame_received_returns_the_state_returned_by_the_receiver(
            complete_frame in proptest::bool::weighted(0.5),
        ) {
            setup(|mut ercp| {
                ercp.receiver.complete_frame_received = complete_frame;
                assert_eq!(ercp.complete_frame_received(), complete_frame);
            });
        }
    }

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

    #[test]
    fn process_returns_ok() {
        setup(|mut ercp| {
            assert_eq!(ercp.process(&mut ()), Ok(()));
        });
    }

    // TODO: Process gets the next command from the receiver (once implemented).

    proptest! {
        #[test]
        fn process_passes_the_command_to_the_router(
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut ercp| {
                let command = Command::new(code, &value).unwrap();
                // TODO: Replace both these values with next_command.result once
                // it is implemented.
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result =
                    Ok(OwnedCommand::from(&command));

                ercp.process(&mut ()).ok();

                assert!(ercp.router.last_command.is_some());
                assert_eq!(
                    ercp.router.last_command.unwrap(),
                    OwnedCommand::from(&command)
                );
            });
        }
    }

    proptest! {
        #[test]
        fn process_sends_the_reply_if_there_is_some(
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize)
        ) {
            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap();
                let expected_frame = reply.as_frame();

                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(OwnedCommand::default());
                ercp.router.reply = Some(reply.into());

                ercp.process(&mut ()).ok();
                assert_eq!(
                    ercp.connection.adapter().test_receive(),
                    expected_frame
                );
            });
        }
    }

    #[test]
    fn process_does_not_send_a_reply_if_there_is_none() {
        setup(|mut ercp| {
            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(OwnedCommand::default());
            ercp.router.reply = None;

            ercp.process(&mut ()).ok();
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                // NOTE: Type inference does not work due to an issue in
                // serde-yaml: https://github.com/dtolnay/serde-yaml/issues/140
                &[] as &[u8]
            );
        });
    }

    #[test]
    fn process_sends_a_nack_if_crc_is_invalid() {
        setup(|mut ercp| {
            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Err(FrameError::InvalidCrc);

            ercp.process(&mut ()).ok();
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                nack!(nack_reason::INVALID_CRC).as_frame()
            );
        });
    }

    #[test]
    fn process_resets_the_receiver() {
        setup(|mut ercp| {
            ercp.process(&mut ()).ok();
            assert_eq!(ercp.receiver.reset.call_count, 1);
        });
    }

    #[test]
    fn process_returns_an_error_on_write_errors() {
        setup(|mut ercp| {
            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(OwnedCommand::default());
            ercp.router.reply = Some(ack!().into());
            ercp.connection.adapter().write_error = Some(());

            assert_eq!(ercp.process(&mut ()), Err(()));
        });
    }

    #[test]
    fn process_still_resets_the_receiver_on_errors() {
        setup(|mut ercp| {
            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(OwnedCommand::default());
            ercp.router.reply = Some(ack!().into());
            ercp.connection.adapter().write_error = Some(());
            ercp.process(&mut ()).err();

            assert_eq!(ercp.receiver.reset.call_count, 1);
        });
    }

    // TODO: Test accept_command.

    ////////////////////////////// Data output /////////////////////////////

    proptest! {
        #[test]
        fn transcieve_writes_a_frame_on_the_connection(
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup_commander(|mut commander| {
                let command = Command::new(code, &value).unwrap();
                let expected_frame = command.as_frame();

                // Ensure there is a reply not to block.
                commander.ercp.receiver.complete_frame_received = true;
                commander.ercp.receiver.check_frame.result =
                    Ok(OwnedCommand::default());

                assert!(commander.transcieve(command).is_ok());
                assert_eq!(
                    commander.ercp.connection.adapter().test_receive(),
                    expected_frame
                );
            });
        }
    }

    proptest! {
     #[test]
        fn transcieve_returns_the_reply(
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup_commander(|mut commander| {
                let reply = Command::new(code, &value).unwrap();
                commander.ercp.receiver.complete_frame_received = true;
                commander.ercp.receiver.check_frame.result =
                    Ok(OwnedCommand::from(&reply));

                assert_eq!(commander.transcieve(ping!()), Ok(reply));
            });
        }
    }

    #[test]
    fn transcieve_returns_an_error_on_write_errors() {
        setup_commander(|mut commander| {
            commander.ercp.connection.adapter().write_error = Some(());
            assert_eq!(
                commander.transcieve(ping!()),
                Err(CommandError::IoError(()))
            );
        });
    }

    #[test]
    fn transcieve_returns_an_error_on_read_errors() {
        setup_commander(|mut commander| {
            commander.ercp.connection.adapter().read_error = Some(());
            assert_eq!(
                commander.transcieve(ping!()),
                Err(CommandError::IoError(()))
            );
        });
    }

    #[test]
    fn transcieve_returns_an_error_on_crc_errors() {
        setup_commander(|mut commander| {
            commander.ercp.receiver.complete_frame_received = true;
            commander.ercp.receiver.check_frame.result =
                Err(FrameError::InvalidCrc);

            assert_eq!(
                commander.transcieve(ping!()),
                Err(CommandError::ReceivedFrameError(
                    ReceivedFrameError::InvalidCrc
                ))
            );
        });
    }

    #[test]
    fn transcieve_returns_an_error_when_the_receiver_reports_a_too_long_reply()
    {
        setup_commander(|mut commander| {
            commander.ercp.receiver.complete_frame_received = true;
            commander.ercp.receiver.check_frame.result =
                Err(FrameError::TooLong);

            assert_eq!(
                commander.transcieve(ping!()),
                Err(CommandError::ReceivedFrameError(
                    ReceivedFrameError::TooLong
                ))
            );
        });
    }

    #[test]
    fn transcieve_returns_an_error_when_an_unexpected_init_sequence_is_received(
    ) {
        setup_commander(|mut commander| {
            commander.ercp.connection.adapter().test_send(&[0]);
            commander.ercp.receiver.receive.results =
                Some(vec![Err(ReceiveError::UnexpectedValue)]);

            assert_eq!(
                commander.transcieve(ping!()),
                Err(CommandError::ReceivedFrameError(
                    ReceivedFrameError::UnexpectedValue
                ))
            );
        })
    }

    #[test]
    fn transcieve_returns_an_error_when_the_eot_is_not_proper() {
        setup_commander(|mut commander| {
            commander.ercp.connection.adapter().test_send(&[0]);
            commander.ercp.receiver.receive.results =
                Some(vec![Err(ReceiveError::NotEot)]);

            assert_eq!(
                commander.transcieve(ping!()),
                Err(CommandError::ReceivedFrameError(
                    ReceivedFrameError::NotEot
                ))
            );
        })
    }

    #[test]
    fn transcieve_returns_an_error_when_received_data_overflows() {
        setup_commander(|mut commander| {
            commander.ercp.connection.adapter().test_send(&[0]);
            commander.ercp.receiver.receive.results =
                Some(vec![Err(ReceiveError::Overflow)]);

            assert_eq!(
                commander.transcieve(ping!()),
                Err(CommandError::ReceivedFrameError(
                    ReceivedFrameError::Overflow
                ))
            );
        })
    }

    #[test]
    fn transcieve_returns_an_error_when_the_peer_reports_an_invalid_crc() {
        setup_commander(|mut commander| {
            let reply = nack!(nack_reason::INVALID_CRC).into();
            commander.ercp.receiver.complete_frame_received = true;
            commander.ercp.receiver.check_frame.result = Ok(reply);

            assert_eq!(
                commander.transcieve(ping!()),
                Err(CommandError::SentFrameError(FrameError::InvalidCrc))
            );
        });
    }

    #[test]
    fn transcieve_returns_an_error_when_the_frame_is_too_long_for_the_peer() {
        setup_commander(|mut commander| {
            let reply = nack!(nack_reason::TOO_LONG).into();
            commander.ercp.receiver.complete_frame_received = true;
            commander.ercp.receiver.check_frame.result = Ok(reply);

            assert_eq!(
                commander.transcieve(ping!()),
                Err(CommandError::SentFrameError(FrameError::TooLong))
            );
        });
    }

    proptest! {
        #[test]
        fn notify_writes_a_frame_on_the_connection(
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut ercp| {
                let command = Command::new(code, &value).unwrap();
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
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut ercp| {
                let command = Command::new(code, &value).unwrap();
                ercp.connection.adapter().write_error = Some(());

                assert_eq!(ercp.notify(command), Err(()));
            })
        }
    }

    /////////////////////////////// Commands ///////////////////////////////

    #[test]
    fn command_calls_the_user_defined_callback() {
        setup(|mut ercp| {
            let mut callback_called = false;
            ercp.command(|_| callback_called = true);
            assert!(callback_called);
        })
    }

    #[test]
    fn command_returns_the_value_returned_by_the_callback() {
        setup(|mut ercp| {
            assert_eq!(
                ercp.command(|_| (9, true, "hello")),
                (9, true, "hello")
            );
        })
    }

    #[test]
    fn command_resets_the_receiver() {
        setup(|mut ercp| {
            ercp.command(|_| {});
            assert_eq!(ercp.receiver.reset.call_count, 1);
        })
    }

    #[test]
    fn ping_sends_a_ping() {
        setup(|mut ercp| {
            let expected_frame = ping!().as_frame();

            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(ack!().into());

            assert_eq!(ercp.ping().unwrap(), Ok(()));
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                expected_frame
            );
        })
    }

    proptest! {
        #[test]
        fn ping_returns_an_error_on_unexpected_replies(
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != ACK);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.ping().unwrap(),
                    Err(PingError::UnexpectedReply)
                );
            });
        }
    }

    #[test]
    fn ping_returns_an_error_on_command_errors() {
        setup(|mut ercp| {
            ercp.connection.adapter().write_error = Some(());
            assert_eq!(ercp.ping(), Err(CommandError::IoError(())));
        });
    }

    #[test]
    fn ping_resets_the_receiver() {
        setup(|mut ercp| {
            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(OwnedCommand::default());

            ercp.ping().ok();
            assert_eq!(ercp.receiver.reset.call_count, 1);
        });
    }

    #[test]
    fn reset_sends_a_reset() {
        setup(|mut ercp| {
            let expected_frame = reset!().as_frame();

            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(ack!().into());

            assert_eq!(ercp.reset().unwrap(), Ok(()));
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
            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(reply.into());

            assert_eq!(
                ercp.reset().unwrap(),
                Err(ResetError::UnhandledCommand)
            );
        });
    }

    proptest! {
        #[test]
        fn reset_returns_an_error_on_unexpected_replies(
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != ACK && code != NACK);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.reset().unwrap(),
                    Err(ResetError::UnexpectedReply)
                );
            });
        }
    }

    #[test]
    fn reset_returns_an_error_on_command_errors() {
        setup(|mut ercp| {
            ercp.connection.adapter().write_error = Some(());
            assert_eq!(ercp.reset(), Err(CommandError::IoError(())));
        });
    }

    #[test]
    fn reset_resets_the_receiver() {
        setup(|mut ercp| {
            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(OwnedCommand::default());

            ercp.reset().ok();
            assert_eq!(ercp.receiver.reset.call_count, 1);
        });
    }

    #[test]
    fn protocol_sends_a_protocol_command() {
        setup(|mut ercp| {
            let expected_frame = protocol!().as_frame();
            let reply = protocol_reply!(version::PROTOCOL_VERSION).into();

            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(reply);

            assert!(ercp.protocol().unwrap().is_ok());
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
                let reply = protocol_reply!(version).into();

                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.protocol().unwrap(),
                    Ok(Version { major, minor, patch })
                );
            })
        }
    }

    proptest! {
        #[test]
        fn protocol_returns_an_error_on_unexpected_replies(
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != PROTOCOL_REPLY || value.len() != 3);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.protocol().unwrap(),
                    Err(ProtocolError::UnexpectedReply)
                );
            });
        }
    }

    #[test]
    fn protocol_returns_an_error_on_command_errors() {
        setup(|mut ercp| {
            ercp.connection.adapter().write_error = Some(());
            assert_eq!(ercp.protocol(), Err(CommandError::IoError(())));
        });
    }

    #[test]
    fn protocol_resets_the_receiver() {
        setup(|mut ercp| {
            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(OwnedCommand::default());

            ercp.protocol().ok();
            assert_eq!(ercp.receiver.reset.call_count, 1);
        });
    }

    proptest! {
        #[test]
        fn version_sends_a_version_command(component in 0..=u8::MAX) {
            setup(|mut ercp| {
                let expected_frame = version!(component).as_frame();
                let reply = version_reply!("").into();

                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert!(ercp.version(component, &mut []).unwrap().is_ok());
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
                let reply = version_reply!(&version).into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                let mut buffer = [0; 255];

                assert!(ercp.version(component, &mut buffer).unwrap().is_ok());
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
                let reply = version_reply!(&version).into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.version(component, &mut [0; 255]).unwrap(),
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
                let reply = version_reply!(&version).into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.version(component, &mut []).unwrap(),
                    Err(VersionError::BufferTooShort)
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_returns_an_error_on_unexpected_replies(
            component in 0..=u8::MAX,
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != VERSION_REPLY);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.version(component, &mut []).unwrap(),
                    Err(VersionError::UnexpectedReply)
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_returns_an_error_on_command_errors(
            component in 0..=u8::MAX,
        ) {
            setup(|mut ercp| {
                ercp.connection.adapter().write_error = Some(());
                assert_eq!(
                    ercp.version(component, &mut []),
                    Err(CommandError::IoError(()))
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_resets_the_receiver(
            component in 0..=u8::MAX,
        ) {
            setup(|mut ercp| {
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(OwnedCommand::default());

                ercp.version(component, &mut []).ok();
                assert_eq!(ercp.receiver.reset.call_count, 1);
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
                let reply = version_reply!("").into();

                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert!(ercp.version_as_string(component).unwrap().is_ok());
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
                let reply = version_reply!(&version).into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                let result = ercp.version_as_string(component).unwrap();
                assert!(result.is_ok());
                assert_eq!(result.unwrap(), version);
            });
        }
    }

    proptest! {
        #[test]
        fn version_as_string_returns_an_error_on_unexpected_replies(
            component in 0..=u8::MAX,
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != VERSION_REPLY);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.version_as_string(component).unwrap(),
                    Err(VersionAsStringError::UnexpectedReply)
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_as_string_returns_an_error_on_command_errors(
            component in 0..=u8::MAX,
        ) {
            setup(|mut ercp| {
                ercp.connection.adapter().write_error = Some(());
                assert_eq!(
                    ercp.version_as_string(component),
                    Err(CommandError::IoError(()))
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_as_string_resets_the_receiver(
            component in 0..=u8::MAX,
        ) {
            setup(|mut ercp| {
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(OwnedCommand::default());

                ercp.version_as_string(component).ok();
                assert_eq!(ercp.receiver.reset.call_count, 1);
            });
        }
    }

    #[test]
    fn max_length_sends_a_max_length_command() {
        setup(|mut ercp| {
            let expected_frame = max_length!().as_frame();
            let reply = max_length_reply!(0).into();

            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(reply);

            assert!(ercp.max_length().unwrap().is_ok());
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
                let reply = max_length_reply!(max_length).into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.max_length().unwrap(),
                    Ok(max_length)
                );
            });
        }
    }

    proptest! {
        #[test]
        fn max_length_returns_an_error_on_unexpected_replies(
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != MAX_LENGTH_REPLY || value.len() != 1);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.max_length().unwrap(),
                    Err(MaxLengthError::UnexpectedReply)
                );
            });
        }
    }

    #[test]
    fn max_length_returns_an_error_on_command_errors() {
        setup(|mut ercp| {
            ercp.connection.adapter().write_error = Some(());
            assert_eq!(ercp.max_length(), Err(CommandError::IoError(())));
        });
    }

    #[test]
    fn max_length_resets_the_receiver() {
        setup(|mut ercp| {
            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(OwnedCommand::default());

            ercp.max_length().ok();
            assert_eq!(ercp.receiver.reset.call_count, 1);
        });
    }

    #[test]
    fn description_sends_a_description_command() {
        setup(|mut ercp| {
            let expected_frame = description!().as_frame();
            let reply = description_reply!("").into();

            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(reply);

            assert!(ercp.description(&mut []).unwrap().is_ok());
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
                let reply = description_reply!(&description).into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                let mut buffer = [0; 255];

                assert!(ercp.description(&mut buffer).unwrap().is_ok());
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
                let reply = description_reply!(&description).into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.description(&mut [0; 255]).unwrap(),
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
                let reply = description_reply!(&description).into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.description(&mut []).unwrap(),
                    Err(DescriptionError::BufferTooShort)
                );
            });
        }
    }

    proptest! {
        #[test]
        fn description_returns_an_error_on_unexpected_replies(
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != DESCRIPTION_REPLY);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.description(&mut []).unwrap(),
                    Err(DescriptionError::UnexpectedReply)
                );
            });
        }
    }

    #[test]
    fn description_returns_an_error_on_command_errors() {
        setup(|mut ercp| {
            ercp.connection.adapter().write_error = Some(());
            assert_eq!(
                ercp.description(&mut []),
                Err(CommandError::IoError(()))
            );
        });
    }

    #[test]
    fn description_resets_the_receiver() {
        setup(|mut ercp| {
            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(OwnedCommand::default());

            ercp.description(&mut []).ok();
            assert_eq!(ercp.receiver.reset.call_count, 1);
        });
    }

    #[test]
    fn description_as_string_sends_a_description_command() {
        setup(|mut ercp| {
            let expected_frame = description!().as_frame();
            let reply = description_reply!("").into();

            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(reply);

            assert!(ercp.description_as_string().unwrap().is_ok());
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
                let reply = description_reply!(&description).into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                let result = ercp.description_as_string().unwrap();
                assert!(result.is_ok());
                assert_eq!(&result.unwrap(), &description);
            });
        }
    }

    proptest! {
        #[test]
        fn description_as_string_returns_an_error_on_unexpected_replies(
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != DESCRIPTION_REPLY);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.description_as_string().unwrap(),
                    Err(DescriptionAsStringError::UnexpectedReply)
                );
            });
        }
    }

    #[test]
    fn description_as_string_returns_an_error_on_command_errors() {
        setup(|mut ercp| {
            ercp.connection.adapter().write_error = Some(());
            assert_eq!(
                ercp.description_as_string(),
                Err(CommandError::IoError(()))
            );
        });
    }

    #[test]
    fn description_as_string_resets_the_receiver() {
        setup(|mut ercp| {
            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(OwnedCommand::default());

            ercp.description_as_string().ok();
            assert_eq!(ercp.receiver.reset.call_count, 1);
        });
    }

    proptest! {
        #[test]
        fn log_sends_a_log(message in ".{0,100}") {
            setup(|mut ercp| {
                let expected_frame = Command::log(&message).unwrap().as_frame();

                assert_eq!(ercp.log(&message).unwrap(), Ok(()));
                assert_eq!(
                    ercp.connection.adapter().test_receive(),
                    expected_frame
                );
            })
        }
    }

    proptest! {
        #[test]
        fn log_returns_an_error_on_io_errors(
            message in ".{0,100}",
        ) {
            setup(|mut ercp| {
                ercp.connection.adapter().write_error = Some(());
                assert_eq!(
                    ercp.log(&message),
                    Err(CommandError::IoError(()))
                );
            });
        }
    }

    proptest! {
        #[test]
        fn sync_log_sends_a_log(message in ".{0,100}") {
            setup(|mut ercp| {
                let expected_frame = Command::log(&message).unwrap().as_frame();

                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(ack!().into());

                assert_eq!(ercp.sync_log(&message).unwrap(), Ok(()));
                assert_eq!(
                    ercp.connection.adapter().test_receive(),
                    expected_frame
                );
            })
        }
    }

    proptest! {
        #[test]
        fn sync_log_returns_an_error_on_unexpected_replies(
            message in ".{0,100}",
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != ACK);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.sync_log(&message).unwrap(),
                    Err(LogError::UnexpectedReply)
                );
            });
        }
    }

    proptest! {
        #[test]
        fn sync_log_returns_an_error_on_command_errors(
            message in ".{0,100}",
        ) {
            setup(|mut ercp| {
                ercp.connection.adapter().write_error = Some(());
                assert_eq!(
                    ercp.sync_log(&message),
                    Err(CommandError::IoError(()))
                );
            });
        }
    }

    proptest! {
        #[test]
        fn sync_log_resets_the_receiver(
            message in ".{0,100}",
        ) {
            setup(|mut ercp| {
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(OwnedCommand::default());

                ercp.sync_log(&message).ok();
                assert_eq!(ercp.receiver.reset.call_count, 1);
            });
        }
    }
}
