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
#![warn(clippy::redundant_pub_crate)]
#![warn(clippy::use_self)]
#![deny(missing_docs)]
#![deny(unsafe_code)]
#![deny(unused_must_use)]

pub mod adapter;
pub mod command;
pub mod error;
pub mod router;
pub mod timer;
pub mod version;

mod connection;
mod crc;
mod receiver;

pub use adapter::Adapter;
pub use command::Command;
pub use error::*;
pub use router::{DefaultRouter, Router};
pub use timer::Timer;
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
/// To handle timeouts appropriately, you also need to provide a [`Timer`]
/// implementation. The following are built-in:
///
/// * [`timer::StdTimer`], backed by [`std::time`] (feature: `std`).
///
/// In addition to the adapter and timer, which define your platform, you need
/// do provide a [`Router`] for handling incoming commands. [`DefaultRouter`]
/// handles the built-in commands out of the box, but you can write your own to
/// extend it with custom commands.
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
    T: Timer,
    R: Router<MAX_LEN>,
    const MAX_LEN: usize = 255,
    Re: Receiver = StandardReceiver<MAX_LEN>,
> {
    receiver: Re,
    connection: Connection<A>,
    timer: T,
    router: R,
}

/// An ERCP Basic commander.
///
/// A commander can only be built by [`ErcpBasic::command`].
pub struct Commander<
    'a,
    A: Adapter,
    T: Timer,
    R: Router<MAX_LEN>,
    const MAX_LEN: usize,
    Re: Receiver,
> {
    ercp: &'a mut ErcpBasic<A, T, R, MAX_LEN, Re>,
}

// TODO: Put elsewhere.
const EOT: u8 = 0x04;

impl<
        A: Adapter,
        T: Timer,
        R: Router<MAX_LEN>,
        const MAX_LEN: usize,
        Re: Receiver,
    > ErcpBasic<A, T, R, MAX_LEN, Re>
{
    /// Instantiates an ERCP Basic driver.
    ///
    /// # Example
    ///
    /// ```
    /// use ercp_basic::{ErcpBasic, DefaultRouter};
    ///
    /// # use ercp_basic::{Adapter, Timer};
    /// #
    /// # struct SomeAdapter;
    /// # struct SomeTimer;
    /// #
    /// # impl SomeAdapter { fn new() -> Self { SomeAdapter } }
    /// #
    /// # impl Adapter for SomeAdapter {
    /// #    type Error = ();
    /// #    fn read(&mut self) -> Result<Option<u8>, ()> { Ok(None) }
    /// #    fn write(&mut self, byte: u8) -> Result<(), ()> { Ok(()) }
    /// # }
    /// #
    /// # impl Timer for SomeTimer {
    /// #    type Instant = u8;
    /// #    type Duration = u8;
    /// #    fn now(&mut self) -> u8 { 0 }
    /// # }
    /// #
    /// // Instantiate an adapter matching your underlying layer.
    /// let adapter = SomeAdapter::new(/* parameters omitted */);
    ///
    /// // Select a timer matching your platform.
    /// let timer = SomeTimer;
    ///
    /// // Instantiate an ERCP Basic driver using the default router. Here we
    /// // need to annotate the type, because the compiler is not (yet) able to
    /// // infer it when it contains a default const generic.
    /// let ercp = ErcpBasic::<_, _, _>::new(adapter, timer, DefaultRouter);
    /// ```
    pub fn new(adapter: A, timer: T, router: R) -> Self {
        Self {
            receiver: Receiver::new(),
            router,
            connection: Connection::new(adapter),
            timer,
        }
    }

    /// Releases the `adapter`, `timer` and `router`.
    pub fn release(self) -> (A, T, R) {
        (self.connection.release(), self.timer, self.router)
    }

    /// Blocks until a command has been received an processes it.
    ///
    /// To have a more fine-grained control over when to handle incoming data
    /// and processing commands, you may consider to call
    /// [`ErcpBasic::handle_data`] and [`ErcpBasic::process`] instead.
    ///
    /// # Errors
    ///
    /// If the connection adapter encounters an error while trying to read data,
    /// this function stops and forwards the error from the adapter. You may
    /// want to retry in this case.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use ercp_basic::{Adapter, DefaultRouter, ErcpBasic, Timer};
    /// #
    /// # struct DummyAdapter;
    /// # struct DummyTimer;
    /// #
    /// # impl Adapter for DummyAdapter {
    /// #    type Error = ();
    /// #    fn read(&mut self) -> Result<Option<u8>, ()> { Ok(None) }
    /// #    fn write(&mut self, byte: u8) -> Result<(), ()> { Ok(()) }
    /// # }
    /// #
    /// # impl Timer for DummyTimer {
    /// #    type Instant = u8;
    /// #    type Duration = u8;
    /// #    fn now(&mut self) -> u8 { 0 }
    /// # }
    /// #
    /// # let mut ercp = ErcpBasic::<_, _, _>::new(DummyAdapter, DummyTimer, DefaultRouter);
    /// // Call accept_command in a loop to continuously accept commands.
    /// loop {
    ///     if let Err(e) = ercp.accept_command(&mut ()) {
    ///         // If the connection adapter has encountered an error. You can
    ///         // just ignore it to retry gracefully, log the error, or take
    ///         // some action.
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

    /// Handles incoming data.
    ///
    /// This function reads data from the connection and processes it until
    /// there is nothing more to read.
    ///
    /// You should typically call this function in the handler for the “data
    /// available” event of your connection adapter. It will only copy data to
    /// an internal buffer and update a state machine.
    ///
    /// After calling this function, you should check if a complete frame has
    /// been received by calling [`ErcpBasic::complete_frame_received`], and
    /// program an execution of [`ErcpBasic::process`] if it is the case.
    ///
    /// # Errors
    ///
    /// If the connection adapter encounters an error while trying to read or
    /// write data, this function stops and forwards the error from the adapter.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use ercp_basic::{Adapter, DefaultRouter, ErcpBasic, Timer};
    /// #
    /// # struct DummyAdapter;
    /// # struct DummyTimer;
    /// #
    /// # struct Context<'a> {
    /// #    ercp: &'a mut ErcpBasic::<DummyAdapter, DummyTimer, DefaultRouter>,
    /// #    ercp_context: &'a mut (),
    /// # }
    /// #
    /// # impl Adapter for DummyAdapter {
    /// #    type Error = ();
    /// #    fn read(&mut self) -> Result<Option<u8>, ()> { Ok(None) }
    /// #    fn write(&mut self, byte: u8) -> Result<(), ()> { Ok(()) }
    /// # }
    /// #
    /// # impl Timer for DummyTimer {
    /// #    type Instant = u8;
    /// #    type Duration = u8;
    /// #    fn now(&mut self) -> u8 { 0 }
    /// # }
    /// #
    /// # fn spawn_task(task: impl Fn(Context)) {}
    /// #
    /// # let mut ercp = ErcpBasic::<_, _, _>::new(DummyAdapter, DummyTimer, DefaultRouter);
    /// // This is the “data available” event handler for your connection.
    /// fn data_available(ctx: Context) {
    ///     // As data is available, you need first to handle it.
    ///     ctx.ercp.handle_data().ok();
    ///
    ///     // Then check if a complete frame has been received.
    ///     if ctx.ercp.complete_frame_received() {
    ///         // If it is the case, it is ready to be processed. As it is a
    ///         // more expensive operation, let’s defer it to another task,
    ///         // maybe with a different priority.
    ///         spawn_task(ercp_process);
    ///     }
    /// }
    ///
    /// // This is a task to actually process any received command.
    /// fn ercp_process(ctx: Context) {
    ///     ctx.ercp.process(ctx.ercp_context).ok();
    /// }
    /// ```
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
    /// * errors from the connection adapter in the outer [`Result`], in case of
    ///   read or write error,
    /// * errors from the receive state machine in the inner [`Result`].
    ///
    /// # Example
    ///
    /// ```
    /// # use ercp_basic::{Adapter, DefaultRouter, ErcpBasic, Timer};
    /// #
    /// # struct DummyAdapter;
    /// # struct DummyTimer;
    /// #
    /// # impl Adapter for DummyAdapter {
    /// #    type Error = ();
    /// #    fn read(&mut self) -> Result<Option<u8>, ()> { Ok(None) }
    /// #    fn write(&mut self, byte: u8) -> Result<(), ()> { Ok(()) }
    /// # }
    /// #
    /// # impl Timer for DummyTimer {
    /// #    type Instant = u8;
    /// #    type Duration = u8;
    /// #    fn now(&mut self) -> u8 { 0 }
    /// # }
    /// #
    /// # let mut ercp = ErcpBasic::<_, _, _>::new(DummyAdapter, DummyTimer, DefaultRouter);
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
    /// If it returns `true`, you should then call [`ErcpBasic::process`].
    pub fn complete_frame_received(&self) -> bool {
        self.receiver.complete_frame_received()
    }

    /// Processes any received command.
    ///
    /// You should typically call this command inside a dedicated thread or task
    /// whenever a complete frame has been received. See
    /// [`ErcpBasic::handle_data`]. for more information.
    ///
    /// The `context` parameter is passed to the [`Router`] to make any resource
    /// available in command handlers.
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
    /// # use ercp_basic::{Adapter, DefaultRouter, ErcpBasic, Timer};
    /// #
    /// # struct DummyAdapter;
    /// # struct DummyTimer;
    /// #
    /// # impl Adapter for DummyAdapter {
    /// #    type Error = ();
    /// #    fn read(&mut self) -> Result<Option<u8>, ()> { Ok(None) }
    /// #    fn write(&mut self, byte: u8) -> Result<(), ()> { Ok(()) }
    /// # }
    /// #
    /// # impl Timer for DummyTimer {
    /// #    type Instant = u8;
    /// #    type Duration = u8;
    /// #    fn now(&mut self) -> u8 { 0 }
    /// # }
    /// #
    /// # let mut ercp = ErcpBasic::<_, _, _>::new(DummyAdapter, DummyTimer, DefaultRouter);
    /// if let Err(e) = ercp.process(&mut ()) {
    ///     // Do something with the error.
    /// }
    /// ```
    pub fn process(
        &mut self,
        context: &mut R::Context,
    ) -> Result<(), A::Error> {
        let result = (|| {
            // TODO: Use self.receiver.next_command().
            if self.complete_frame_received() {
                match self.receiver.check_frame() {
                    Ok(command) => {
                        if let Some(reply) = self.router.route(command, context)
                        {
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
        })();

        self.reset_state();
        result
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
    ///     Timer,
    /// };
    ///
    /// // It is always a good idea to represent the peer device as a struct,
    /// // owning an ERCP Basic driver instance.
    /// struct MyDevice<A: Adapter, T: Timer> {
    ///     ercp: ErcpBasic<A, T, DefaultRouter>,
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
    /// impl<A: Adapter, T: Timer> MyDevice<A, T> {
    ///     fn new(ercp: ErcpBasic<A, T, DefaultRouter>) -> Self {
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
    ///     fn some_command(
    ///         &mut self,
    ///         arg: u8,
    ///         timeout: Option<T::Duration>
    ///     ) -> CommandResult<u8, SomeCommandError, A::Error> {
    ///         // The ERCP Basic driver itself cannot transcieve commands. By
    ///         // calling the command method, you gain access to a commander
    ///         // you can then use to actually transcieve.
    ///         self.ercp.command(|mut commander| {
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
    ///             let reply = commander.transcieve(command, timeout)?;
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
    pub fn command<RT>(
        &mut self,
        mut callback: impl FnMut(Commander<A, T, R, MAX_LEN, Re>) -> RT,
    ) -> RT {
        let result = callback(Commander { ercp: self });
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
    pub fn ping(
        &mut self,
        timeout: Option<T::Duration>,
    ) -> CommandResult<(), PingError, A::Error> {
        self.command(|mut commander| {
            let reply = commander.transcieve(ping!(), timeout)?;

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
    pub fn reset(
        &mut self,
        timeout: Option<T::Duration>,
    ) -> CommandResult<(), ResetError, A::Error> {
        self.command(|mut commander| {
            let reply = commander.transcieve(reset!(), timeout)?;

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
        timeout: Option<T::Duration>,
    ) -> CommandResult<Version, ProtocolError, A::Error> {
        self.command(|mut commander| {
            let reply = commander.transcieve(protocol!(), timeout)?;

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
        timeout: Option<T::Duration>,
    ) -> CommandResult<usize, VersionError, A::Error> {
        self.command(|mut commander| {
            let reply = commander.transcieve(version!(component), timeout)?;

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
        timeout: Option<T::Duration>,
    ) -> CommandResult<String, VersionAsStringError, A::Error> {
        self.command(|mut commander| {
            let reply = commander.transcieve(version!(component), timeout)?;

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
        timeout: Option<T::Duration>,
    ) -> CommandResult<u8, MaxLengthError, A::Error> {
        self.command(|mut commander| {
            let reply = commander.transcieve(max_length!(), timeout)?;

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
        timeout: Option<T::Duration>,
    ) -> CommandResult<usize, DescriptionError, A::Error> {
        self.command(|mut commander| {
            let reply = commander.transcieve(description!(), timeout)?;

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
        timeout: Option<T::Duration>,
    ) -> CommandResult<String, DescriptionAsStringError, A::Error> {
        self.command(|mut commander| {
            let reply = commander.transcieve(description!(), timeout)?;

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
        timeout: Option<T::Duration>,
    ) -> CommandResult<(), LogError, A::Error> {
        self.command(|mut commander| {
            let command = match Command::log(message) {
                Ok(command) => command,
                Err(NewCommandError::TooLong) => {
                    return Ok(Err(LogError::TooLong))
                }
            };

            let reply = commander.transcieve(command, timeout)?;

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
        T: Timer,
        R: Router<MAX_LEN>,
        const MAX_LEN: usize,
        Re: Receiver,
    > Commander<'a, A, T, R, MAX_LEN, Re>
{
    /// Sends a command to the peer device, and waits for a reply.
    ///
    /// This function is meant to be used inside a command closure. Please see
    /// the documentation for [`ErcpBasic::command`].
    pub fn transcieve(
        &mut self,
        command: Command,
        timeout: Option<T::Duration>,
    ) -> Result<Command, CommandError<A::Error>> {
        self.ercp
            .connection
            .send(command)
            .map_err(CommandError::IoError)?;

        let reply = self.receive(timeout)?;

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

    /// Blocks until a command has been received.
    ///
    /// This function is meant to be used inside a command closure. Please see
    /// the documentation for [`ErcpBasic::command`].
    pub fn receive(
        &mut self,
        timeout: Option<T::Duration>,
    ) -> Result<Command, ReceivedCommandError<A::Error>> {
        self.wait_for_command_fallible(timeout)?;

        self.ercp
            .receiver
            .check_frame()
            .map_err(Into::into)
            .map_err(ReceivedCommandError::ReceivedFrameError)
    }

    /// Blocks until a complete frame has been received.
    fn wait_for_command_fallible(
        &mut self,
        timeout: Option<T::Duration>,
    ) -> Result<(), ReceivedCommandError<A::Error>> {
        let start = self.ercp.timer.now();

        while !self.ercp.complete_frame_received() {
            // TODO: Do different things depending on features.

            // TODO: Only with the blocking feature.
            self.ercp
                .handle_data_fallible()
                .map_err(ReceivedCommandError::IoError)?
                .map_err(Into::into)
                .map_err(ReceivedCommandError::ReceivedFrameError)?;

            // TODO: WFI on Cortex-M.

            if let Some(timeout) = timeout {
                if self.ercp.timer.now() >= start + timeout {
                    return Err(ReceivedCommandError::Timeout);
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::time::{Duration, Instant};

    use super::*;
    use connection::tests::TestAdapter;
    use timer::StdTimer;

    use proptest::collection::vec;
    use proptest::num::u8;
    use proptest::prelude::*;

    const TIMEOUT: Option<Duration> = Some(Duration::from_nanos(1));

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
        test: impl Fn(
            ErcpBasic<TestAdapter, StdTimer, TestRouter, 255, TestReceiver>,
        ),
    ) {
        let adapter = TestAdapter::default();
        let timer = StdTimer;
        let router = TestRouter::default();
        let ercp = ErcpBasic::new(adapter, timer, router);
        test(ercp);
    }

    fn setup_commander(
        test: impl Fn(
            Commander<TestAdapter, StdTimer, TestRouter, 255, TestReceiver>,
        ),
    ) {
        let adapter = TestAdapter::default();
        let timer = StdTimer;
        let router = TestRouter::default();
        let mut ercp = ErcpBasic::new(adapter, timer, router);
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
            frame in vec(u8::ANY, 0..=1000),
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
            frame in vec(u8::ANY, 0..=1000),
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
            frame in vec(u8::ANY, 0..=1000),
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
            frame in vec(u8::ANY, 0..=1000),
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
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize),
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
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize)
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
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize),
        ) {
            setup_commander(|mut commander| {
                let command = Command::new(code, &value).unwrap();
                let expected_frame = command.as_frame();

                // Ensure there is a reply not to block.
                commander.ercp.receiver.complete_frame_received = true;
                commander.ercp.receiver.check_frame.result =
                    Ok(OwnedCommand::default());

                assert!(commander.transcieve(command, TIMEOUT).is_ok());
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
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize),
        ) {
            setup_commander(|mut commander| {
                let reply = Command::new(code, &value).unwrap();
                commander.ercp.receiver.complete_frame_received = true;
                commander.ercp.receiver.check_frame.result =
                    Ok(OwnedCommand::from(&reply));

                assert_eq!(commander.transcieve(ping!(), TIMEOUT), Ok(reply));
            });
        }
    }

    #[test]
    fn transcieve_returns_an_error_on_write_errors() {
        setup_commander(|mut commander| {
            commander.ercp.connection.adapter().write_error = Some(());
            assert_eq!(
                commander.transcieve(ping!(), TIMEOUT),
                Err(CommandError::IoError(()))
            );
        });
    }

    #[test]
    fn transcieve_returns_an_error_on_read_errors() {
        setup_commander(|mut commander| {
            commander.ercp.connection.adapter().read_error = Some(());
            assert_eq!(
                commander.transcieve(ping!(), TIMEOUT),
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
                commander.transcieve(ping!(), TIMEOUT),
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
                commander.transcieve(ping!(), TIMEOUT),
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
                commander.transcieve(ping!(), TIMEOUT),
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
                commander.transcieve(ping!(), TIMEOUT),
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
                commander.transcieve(ping!(), TIMEOUT),
                Err(CommandError::ReceivedFrameError(
                    ReceivedFrameError::Overflow
                ))
            );
        })
    }

    #[test]
    fn transcieve_returns_an_error_when_there_is_no_reply_after_timeout() {
        setup_commander(|mut commander| {
            assert_eq!(
                commander.transcieve(ping!(), TIMEOUT),
                Err(CommandError::Timeout),
            );
        })
    }

    #[test]
    fn transcieve_returns_after_the_timeout() {
        setup_commander(|mut commander| {
            let timeout = Duration::from_millis(100);

            let before = Instant::now();
            commander.transcieve(ping!(), Some(timeout)).err();
            let elapsed = before.elapsed();

            assert!(elapsed > timeout);
            assert!(elapsed < timeout + timeout / 2);
        })
    }

    #[test]
    fn transcieve_returns_an_error_when_the_peer_reports_an_invalid_crc() {
        setup_commander(|mut commander| {
            let reply = nack!(nack_reason::INVALID_CRC).into();
            commander.ercp.receiver.complete_frame_received = true;
            commander.ercp.receiver.check_frame.result = Ok(reply);

            assert_eq!(
                commander.transcieve(ping!(), TIMEOUT),
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
                commander.transcieve(ping!(), TIMEOUT),
                Err(CommandError::SentFrameError(FrameError::TooLong))
            );
        });
    }

    proptest! {
        #[test]
        fn notify_writes_a_frame_on_the_connection(
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize),
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
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize),
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

            assert_eq!(ercp.ping(TIMEOUT).unwrap(), Ok(()));
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                expected_frame
            );
        })
    }

    proptest! {
        #[test]
        fn ping_returns_an_error_on_unexpected_replies(
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != ACK);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.ping(TIMEOUT).unwrap(),
                    Err(PingError::UnexpectedReply)
                );
            });
        }
    }

    #[test]
    fn ping_returns_an_error_on_command_errors() {
        setup(|mut ercp| {
            ercp.connection.adapter().write_error = Some(());
            assert_eq!(ercp.ping(TIMEOUT), Err(CommandError::IoError(())));
        });
    }

    #[test]
    fn ping_returns_an_error_when_there_is_no_reply_after_timeout() {
        setup(|mut ercp| {
            assert_eq!(ercp.ping(TIMEOUT), Err(CommandError::Timeout));
        });
    }

    #[test]
    fn ping_resets_the_receiver() {
        setup(|mut ercp| {
            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(OwnedCommand::default());

            ercp.ping(TIMEOUT).ok();
            assert_eq!(ercp.receiver.reset.call_count, 1);
        });
    }

    #[test]
    fn reset_sends_a_reset() {
        setup(|mut ercp| {
            let expected_frame = reset!().as_frame();

            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(ack!().into());

            assert_eq!(ercp.reset(TIMEOUT).unwrap(), Ok(()));
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
                ercp.reset(TIMEOUT).unwrap(),
                Err(ResetError::UnhandledCommand)
            );
        });
    }

    proptest! {
        #[test]
        fn reset_returns_an_error_on_unexpected_replies(
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != ACK && code != NACK);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.reset(TIMEOUT).unwrap(),
                    Err(ResetError::UnexpectedReply)
                );
            });
        }
    }

    #[test]
    fn reset_returns_an_error_on_command_errors() {
        setup(|mut ercp| {
            ercp.connection.adapter().write_error = Some(());
            assert_eq!(ercp.reset(TIMEOUT), Err(CommandError::IoError(())));
        });
    }

    #[test]
    fn reset_returns_an_error_when_there_is_no_reply_after_timeout() {
        setup(|mut ercp| {
            assert_eq!(ercp.reset(TIMEOUT), Err(CommandError::Timeout));
        });
    }

    #[test]
    fn reset_resets_the_receiver() {
        setup(|mut ercp| {
            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(OwnedCommand::default());

            ercp.reset(TIMEOUT).ok();
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

            assert!(ercp.protocol(TIMEOUT).unwrap().is_ok());
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                expected_frame
            );
        })
    }

    proptest! {
        #[test]
        fn protocol_returns_the_received_protocol_version(
            major in u8::ANY,
            minor in u8::ANY,
            patch in u8::ANY,
        ) {
            setup(|mut ercp| {
                let version = Version { major, minor, patch };
                let reply = protocol_reply!(version).into();

                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.protocol(TIMEOUT).unwrap(),
                    Ok(Version { major, minor, patch })
                );
            })
        }
    }

    proptest! {
        #[test]
        fn protocol_returns_an_error_on_unexpected_replies(
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != PROTOCOL_REPLY || value.len() != 3);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.protocol(TIMEOUT).unwrap(),
                    Err(ProtocolError::UnexpectedReply)
                );
            });
        }
    }

    #[test]
    fn protocol_returns_an_error_on_command_errors() {
        setup(|mut ercp| {
            ercp.connection.adapter().write_error = Some(());
            assert_eq!(ercp.protocol(TIMEOUT), Err(CommandError::IoError(())));
        });
    }

    #[test]
    fn protocol_returns_an_error_when_there_is_no_reply_after_timeout() {
        setup(|mut ercp| {
            assert_eq!(ercp.protocol(TIMEOUT), Err(CommandError::Timeout));
        });
    }

    #[test]
    fn protocol_resets_the_receiver() {
        setup(|mut ercp| {
            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(OwnedCommand::default());

            ercp.protocol(TIMEOUT).ok();
            assert_eq!(ercp.receiver.reset.call_count, 1);
        });
    }

    proptest! {
        #[test]
        fn version_sends_a_version_command(component in u8::ANY) {
            setup(|mut ercp| {
                let expected_frame = version!(component).as_frame();
                let reply = version_reply!("").into();

                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert!(
                    ercp.version(component, &mut [], TIMEOUT).unwrap().is_ok()
                );
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
            component in u8::ANY,
            version in ".{1,100}",
        ) {
            setup(|mut ercp| {
                let reply = version_reply!(&version).into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                let mut buffer = [0; 255];

                assert!(
                    ercp.version(component, &mut buffer, TIMEOUT)
                        .unwrap()
                        .is_ok()
                );
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
            component in u8::ANY,
            version in ".{1,100}",
        ) {
            setup(|mut ercp| {
                let reply = version_reply!(&version).into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.version(component, &mut [0; 255], TIMEOUT).unwrap(),
                    Ok(version.as_bytes().len())
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_returns_an_error_if_the_buffer_is_too_short_for_reply(
            component in u8::ANY,
            version in ".{1,100}",
        ) {
            setup(|mut ercp| {
                let reply = version_reply!(&version).into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.version(component, &mut [], TIMEOUT).unwrap(),
                    Err(VersionError::BufferTooShort)
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_returns_an_error_on_unexpected_replies(
            component in u8::ANY,
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != VERSION_REPLY);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.version(component, &mut [], TIMEOUT).unwrap(),
                    Err(VersionError::UnexpectedReply)
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_returns_an_error_on_command_errors(
            component in u8::ANY,
        ) {
            setup(|mut ercp| {
                ercp.connection.adapter().write_error = Some(());
                assert_eq!(
                    ercp.version(component, &mut [], TIMEOUT),
                    Err(CommandError::IoError(()))
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_returns_an_error_when_there_is_no_reply_after_timeout(
            component in u8::ANY,
        ) {
            setup(|mut ercp| {
                assert_eq!(
                    ercp.version(component, &mut [], TIMEOUT),
                    Err(CommandError::Timeout),
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_resets_the_receiver(
            component in u8::ANY,
        ) {
            setup(|mut ercp| {
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(OwnedCommand::default());

                ercp.version(component, &mut [], TIMEOUT).ok();
                assert_eq!(ercp.receiver.reset.call_count, 1);
            });
        }
    }

    proptest! {
        #[test]
            fn version_as_string_sends_a_version_command(
                component in u8::ANY,
            ) {
            setup(|mut ercp| {
                let expected_frame = version!(component).as_frame();
                let reply = version_reply!("").into();

                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert!(
                    ercp.version_as_string(component, TIMEOUT).unwrap().is_ok()
                );
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
            component in u8::ANY,
            version in ".{1,100}",
        ) {
            setup(|mut ercp| {
                let reply = version_reply!(&version).into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                let result =
                    ercp.version_as_string(component, TIMEOUT).unwrap();
                assert!(result.is_ok());
                assert_eq!(result.unwrap(), version);
            });
        }
    }

    proptest! {
        #[test]
        fn version_as_string_returns_an_error_on_unexpected_replies(
            component in u8::ANY,
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != VERSION_REPLY);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.version_as_string(component, TIMEOUT).unwrap(),
                    Err(VersionAsStringError::UnexpectedReply)
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_as_string_returns_an_error_on_command_errors(
            component in u8::ANY,
        ) {
            setup(|mut ercp| {
                ercp.connection.adapter().write_error = Some(());
                assert_eq!(
                    ercp.version_as_string(component, TIMEOUT),
                    Err(CommandError::IoError(()))
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_as_string_returns_an_error_when_there_is_no_reply_after_timeout(
            component in u8::ANY,
        ) {
            setup(|mut ercp| {
                assert_eq!(
                    ercp.version_as_string(component, TIMEOUT),
                    Err(CommandError::Timeout),
                );
            });
        }
    }

    proptest! {
        #[test]
        fn version_as_string_resets_the_receiver(
            component in u8::ANY,
        ) {
            setup(|mut ercp| {
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(OwnedCommand::default());

                ercp.version_as_string(component, TIMEOUT).ok();
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

            assert!(ercp.max_length(TIMEOUT).unwrap().is_ok());
            assert_eq!(
                ercp.connection.adapter().test_receive(),
                expected_frame
            );
        })
    }

    proptest! {
        #[test]
        fn max_length_returns_the_received_maximum_length(
            max_length in u8::ANY,
        ) {
            setup(|mut ercp| {
                let reply = max_length_reply!(max_length).into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.max_length(TIMEOUT).unwrap(),
                    Ok(max_length)
                );
            });
        }
    }

    proptest! {
        #[test]
        fn max_length_returns_an_error_on_unexpected_replies(
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != MAX_LENGTH_REPLY || value.len() != 1);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.max_length(TIMEOUT).unwrap(),
                    Err(MaxLengthError::UnexpectedReply)
                );
            });
        }
    }

    #[test]
    fn max_length_returns_an_error_on_command_errors() {
        setup(|mut ercp| {
            ercp.connection.adapter().write_error = Some(());
            assert_eq!(
                ercp.max_length(TIMEOUT),
                Err(CommandError::IoError(()))
            );
        });
    }

    #[test]
    fn max_length_returns_an_error_when_there_is_no_reply_after_timeout() {
        setup(|mut ercp| {
            assert_eq!(ercp.max_length(TIMEOUT), Err(CommandError::Timeout),);
        });
    }

    #[test]
    fn max_length_resets_the_receiver() {
        setup(|mut ercp| {
            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(OwnedCommand::default());

            ercp.max_length(TIMEOUT).ok();
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

            assert!(ercp.description(&mut [], TIMEOUT).unwrap().is_ok());
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

                assert!(
                    ercp.description(&mut buffer, TIMEOUT).unwrap().is_ok()
                );
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
                    ercp.description(&mut [0; 255], TIMEOUT).unwrap(),
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
                    ercp.description(&mut [], TIMEOUT).unwrap(),
                    Err(DescriptionError::BufferTooShort)
                );
            });
        }
    }

    proptest! {
        #[test]
        fn description_returns_an_error_on_unexpected_replies(
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != DESCRIPTION_REPLY);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.description(&mut [], TIMEOUT).unwrap(),
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
                ercp.description(&mut [], TIMEOUT),
                Err(CommandError::IoError(()))
            );
        });
    }

    #[test]
    fn description_returns_an_error_when_there_is_no_reply_after_timeout() {
        setup(|mut ercp| {
            assert_eq!(
                ercp.description(&mut [], TIMEOUT),
                Err(CommandError::Timeout),
            );
        });
    }

    #[test]
    fn description_resets_the_receiver() {
        setup(|mut ercp| {
            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(OwnedCommand::default());

            ercp.description(&mut [], TIMEOUT).ok();
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

            assert!(ercp.description_as_string(TIMEOUT).unwrap().is_ok());
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

                let result = ercp.description_as_string(TIMEOUT).unwrap();
                assert!(result.is_ok());
                assert_eq!(&result.unwrap(), &description);
            });
        }
    }

    proptest! {
        #[test]
        fn description_as_string_returns_an_error_on_unexpected_replies(
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != DESCRIPTION_REPLY);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.description_as_string(TIMEOUT).unwrap(),
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
                ercp.description_as_string(TIMEOUT),
                Err(CommandError::IoError(()))
            );
        });
    }

    #[test]
    fn description_as_string_returns_an_error_when_there_is_no_reply_after_timeout(
    ) {
        setup(|mut ercp| {
            assert_eq!(
                ercp.description_as_string(TIMEOUT),
                Err(CommandError::Timeout),
            );
        });
    }

    #[test]
    fn description_as_string_resets_the_receiver() {
        setup(|mut ercp| {
            ercp.receiver.complete_frame_received = true;
            ercp.receiver.check_frame.result = Ok(OwnedCommand::default());

            ercp.description_as_string(TIMEOUT).ok();
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

                assert_eq!(ercp.sync_log(&message, TIMEOUT).unwrap(), Ok(()));
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
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize),
        ) {
            prop_assume!(code != ACK);

            setup(|mut ercp| {
                let reply = Command::new(code, &value).unwrap().into();
                ercp.receiver.complete_frame_received = true;
                ercp.receiver.check_frame.result = Ok(reply);

                assert_eq!(
                    ercp.sync_log(&message, TIMEOUT).unwrap(),
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
                    ercp.sync_log(&message, TIMEOUT),
                    Err(CommandError::IoError(()))
                );
            });
        }
    }

    proptest! {
        #[test]
        fn sync_log_returns_an_error_when_there_is_no_reply_after_timeout(
            message in ".{0,100}",
        ) {
            setup(|mut ercp| {
                assert_eq!(
                    ercp.sync_log(&message, TIMEOUT),
                    Err(CommandError::Timeout),
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

                ercp.sync_log(&message, TIMEOUT).ok();
                assert_eq!(ercp.receiver.reset.call_count, 1);
            });
        }
    }
}
