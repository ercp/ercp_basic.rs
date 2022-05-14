// Copyright 2021 Jean-Philippe Cugnet
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

//! Command router and default implementation.

use crate::command::*;
use crate::{
    ack, description_reply, max_length_reply, nack, protocol_reply, version,
    version_reply,
};

#[cfg(doc)]
use crate::ErcpBasic;

/// A command router.
///
/// The router is a central element in the command processing machinery: this is
/// where incoming commands are dispatched to the correct handler, and where the
/// handlers themselves are implemented. The entry point of a router is
/// [`Router::route`], which is called internally by [`ErcpBasic::process`] or
/// [`ErcpBasic::accept_command`]. This method takes as input the incoming
/// command and a context. It matches on the command code to calls the
/// appropriate handler, then returns an optional reply command.
///
/// A default implementation is provided for every method, so that you only need
/// to implement what you want to override. The [`DefaultRouter`] is a concrete
/// [`Router`] using the default implementations.
///
/// # Implementing a router
///
/// After ensuring your device works properly with the [`DefaultRouter`], you
/// want typically to define your own, to change the device description or
/// accept application-specific commands. The next subsections will guide you
/// through standard use cases.
///
/// ## The minimal router implementation
///
/// Let’s start with the simplest router: [`DefaultRouter`] itself. It is
/// defined as follows:
///
/// ```
/// use ercp_basic::Router;
///
/// // An empty struct, as it does not need to store data.
/// struct DefaultRouter;
///
/// impl<const MAX_LEN: usize> Router<MAX_LEN> for DefaultRouter {
///     // It does not need a context, so let’s use unit.
///     type Context = ();
///
///     // Nothing more to add since it uses all the default implementations.
/// }
/// ```
///
/// When writing your own router, you should start with something like this.
///
/// ## Setting the description and the firmware version
///
/// The
/// [`Version(FIRMWARE)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#versioncomponent)
/// and
/// [`Description()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#description)
/// commands get their respective values from [`Router::firmware_version`] and
/// [`Router::description`]. Simply override these methods to set your own
/// values:
///
/// ```
/// use ercp_basic::Router;
///
/// struct ApplicationRouter;
///
/// impl Router for ApplicationRouter {
///     type Context = ();
///
///     fn firmware_version(&self) -> &str {
///         concat!(env!("CARGO_PKG_NAME"), " ", env!("CARGO_PKG_VERSION"))
///     }
///
///     fn description(&self) -> &str {
///         "Example object"
///     }
/// }
/// ```
///
/// ## Handling an application-specific command
///
/// To handle an application-specific command, you need to:
///
/// * define a handler for your command,
/// * add a route for this command, by overriding [`Router::route`].
///
/// ```
/// use ercp_basic::{
///     ack,
///     command::{nack_reason, Command},
///     nack, Router,
/// };
///
/// struct ApplicationRouter;
///
/// const MY_COMMAND: u8 = 0x20;
///
/// impl Router for ApplicationRouter {
///     type Context = ();
///
///     // Override the route method.
///     fn route(
///         &mut self,
///         command: Command,
///         _ctx: &mut Self::Context,
///     ) -> Option<Command> {
///         // Match on the command code.
///         match command.code() {
///             // Dispatch application-specific commands to their handlers.
///             MY_COMMAND => self.handle_my_command(command),
///
///             // Redirect all other commands to the default routes.
///             // NOTE: It is important to always put this in your custom route
///             // method, so the built-in commands are handled.
///             _ => self.default_routes(command),
///         }
///     }
/// }
///
/// impl ApplicationRouter {
///     // Define a handler for the command.
///     fn handle_my_command(&self, command: Command) -> Option<Command> {
///         // Do whatever you want here.
///         if command.length() == 1 && command.value()[0] == 0x42 {
///             // Return some command as a reply. Typically, reply an Ack()
///             // when the command is successful. If you do not want to reply,
///             // simply return None.
///             Some(ack!())
///         } else {
///             Some(nack!(nack_reason::NO_REASON))
///         }
///     }
/// }
/// ```
///
/// ## Working with external resources
///
/// In a real-life use-case, you could need to access an external resource from
/// your command handlers. This can be achieved by using a context.
///
/// Both [`ErcpBasic::process`] and [`ErcpBasic::accept_command`] take a
/// parameter of type [`Router::Context`], which they pass to [`Router::route`].
/// By defining this type, you can control the resources that are available to
/// your router. Let’s say for instance that you have a LED, which you can
/// switch on. You could expose this feature via ERCP Basic like this:
///
/// ```no_run
/// use ercp_basic::{ack, Command, ErcpBasic, Router};
///
/// struct ApplicationRouter;
///
/// # struct Led;
/// # impl Led {
/// #   fn init() -> Self { Led }
/// #   fn on(&mut self) {}
/// # }
/// #
/// // Define a type to gather the resources that are driveable though your
/// // ERCP Basic instance.
/// struct DriveableResources {
///     led: Led,
/// }
///
/// const LED_ON: u8 = 0x20;
///
/// impl Router for ApplicationRouter {
///     // Use the type defined above as the context for your router.
///     type Context = DriveableResources;
///
///     fn route(
///         &mut self,
///         command: Command,
///         // It will be passed to the route command, so you can use parts of
///         // in in your handlers.
///         ctx: &mut Self::Context,
///     ) -> Option<Command> {
///         match command.code() {
///             // Pass the LED driver to the LED_ON command handler.
///             LED_ON => self.handle_led_on(command, &mut ctx.led),
///             _ => self.default_routes(command),
///         }
///     }
/// }
///
/// impl ApplicationRouter {
///     fn handle_led_on(&self, command: Command, led: &mut Led) -> Option<Command> {
///         // You can then swith the LED on in your handler.
///         led.on();
///         Some(ack!())
///     }
/// }
///
/// fn main() {
///     // Initialise your resources.
///     let mut led = Led::init();
///
///     # use ercp_basic::{Adapter, Timer};
///     #
///     # struct SomeAdapter;
///     # struct SomeTimer;
///     #
///     # impl SomeAdapter { fn new() -> Self { SomeAdapter } }
///     #
///     # impl Adapter for SomeAdapter {
///     #    type Error = ();
///     #    fn read(&mut self) -> Result<Option<u8>, ()> { Ok(None) }
///     #    fn write(&mut self, byte: u8) -> Result<(), ()> { Ok(()) }
///     # }
///     #
///     # impl Timer for SomeTimer {
///     #    type Instant = u8;
///     #    type Duration = u8;
///     #    fn now(&mut self) -> u8 { 0 }
///     # }
///     #
///     // Initialise the ERCP Basic driver with your router.
///     let adapter = SomeAdapter::new();
///     let timer = SomeTimer;
///     let mut ercp: ErcpBasic<_, _, _> = ErcpBasic::new(adapter, timer, ApplicationRouter);
///
///     // Gather your driveable resources.
///     let mut resources = DriveableResources { led };
///
///     loop {
///         // Pass the resources as the context to accept_command (or process).
///         // It will be passed internally to the router.
///         ercp.accept_command(&mut resources);
///     }
/// }
/// ```
///
/// ## Returning some data
///
/// Some command handlers also need to return some data. To do so, you will need
/// a buffer to build the value of the command, but doing so in your commaand
/// handler directly would end in a temporary value being returned, which is
/// illegal. You can instead define your buffer in the router itself, so every
/// handler can use it. Imagine we want to build an echo command:
///
/// ```
/// use ercp_basic::{ack, nack, Command, Router};
///
/// struct ApplicationRouter {
///     // Add a buffer to your router. It should be as big as the maximum
///     // length of the value you want to be able to build. Let’s say we can
///     // echo up to 10 bytes.
///     buffer: [u8; 10],
/// }
///
/// // The ECHO command and its reply.
/// const ECHO: u8 = 0x20;
/// const ECHO_REPLY: u8 = 0x21;
///
/// // A custom reason for Nack replies, in case the value to echo would be
/// // longer than 10 bytes.
/// const VALUE_TOO_LONG: u8 = 0x10;
///
/// impl Router for ApplicationRouter {
///     type Context = ();
///
///     fn route(
///         &mut self,
///         command: Command,
///         _ctx: &mut Self::Context,
///     ) -> Option<Command> {
///         match command.code() {
///             ECHO => self.handle_echo(command),
///             _ => self.default_routes(command),
///         }
///     }
/// }
///
/// impl ApplicationRouter {
///     fn handle_echo(&mut self, command: Command) -> Option<Command> {
///         if command.value().len() <= self.buffer.len() {
///             // We can now use self.buffer to build the value of our
///             // ECHO_REPLY command, simply copying from the value of the ECHO
///             // command.
///             let value = &mut self.buffer[0..command.value().len()];
///             value.copy_from_slice(command.value());
///
///             // NOTE(unwrap): value <= 10 < u8::MAX.
///             let reply = Command::new(ECHO_REPLY, value).unwrap();
///             Some(reply)
///         } else {
///             Some(nack!(VALUE_TOO_LONG))
///         }
///     }
/// }
/// ```
///
/// ## Overriding a built-in command
///
/// You should not need to override most build-in commands, but there can be a
/// few exceptions. For instance, the default implementation of
/// [`Router::handle_reset`] replies a
/// [`Nack(UNKNOWN_COMMAND)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#nackreason),
/// as its actual implementation is optional. To actually reset the device when
/// this command is received, you can something like:
///
/// ```
/// use ercp_basic::{ack, Command, Router};
///
/// struct ApplicationRouter;
///
/// impl Router for ApplicationRouter {
///     type Context = ();
///
///     // Simply override the handle_reset method.
///     fn handle_reset(&mut self, _command: Command) -> Option<Command> {
///         # fn reset_device() {}
///         reset_device();
///         Some(ack!())
///     }
/// }
/// ```
///
/// ## Adding the version of a component
///
/// The
/// [`Version(component)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#versioncomponent)
/// command can be used to get the version of an arbitrary component. The
/// firmware version and the ERCP Basic library version are built-in components,
/// but you can add the version of any component you would like. To do so, you
/// should override [`Router::version`] and map the component number to a
/// version string. For instance, let’s return the version of an imaginary
/// component `my_extension`:
///
/// ```
/// # mod my_extension { pub const VERSION: &str = ""; }
/// use ercp_basic::{ack, Command, Router};
///
/// struct ApplicationRouter;
///
/// // Define a component number for your component.
/// const MY_EXTENSION: u8 = 0x10;
///
/// impl Router for ApplicationRouter {
///     type Context = ();
///
///     // Override the version method.
///     fn version(&self, component: u8) -> &str {
///         match component {
///             // Map the extension number to a version string (let’s say it
///             // is provided directly by the my_extension crate).
///             MY_EXTENSION => my_extension::VERSION,
///
///             // Handle the built-in components.
///             // NOTE: It is important to always put this in your custom
///             // version method, so that the versions for the built-in
///             // components are still properly returned.
///             _ => self.default_versions(component),
///         }
///     }
/// }
/// ```
pub trait Router<const MAX_LEN: usize = 255> {
    /// The context for the router.
    ///
    /// The [`Router::route`] methode takes a context as argument, which can be
    /// used to make resources or data available to the command handlers. You
    /// can use a struct gathering all needed resources, then dispatch them to
    /// the command handlers.
    ///
    /// If you do not need a context, just use unit:
    ///
    /// ```
    /// type Context = ();
    /// ```
    type Context;

    /// Routes the command to the proper handler.
    ///
    /// This method takes a command and a context as arguments. It routes the
    /// command to the proper handler, optionally providing elements from the
    /// context to it, then returns an optional command to be replied.
    ///
    /// The default implementation simply calls [`Router::default_routes`]. When
    /// implementing your own router with application commands, you need to
    /// override it to add your routes:
    ///
    /// ```
    /// use ercp_basic::{Command, Router};
    ///
    /// struct ApplicationRouter;
    ///
    /// # const COMMAND_A: u8 = 0x20;
    /// # const COMMAND_B: u8 = 0x21;
    /// #
    /// impl Router for ApplicationRouter {
    ///     type Context = ();
    ///
    ///     fn route(
    ///         &mut self,
    ///         command: Command,
    ///         _ctx: &mut Self::Context,
    ///     ) -> Option<Command> {
    ///         // Match on the command code.
    ///         match command.code() {
    ///             // Dispatch application-specific commands to their handlers.
    ///             COMMAND_A => self.handle_command_a(command),
    ///             COMMAND_B => self.handle_command_b(command),
    ///
    ///            // Always call self.default_routes in the default path.
    ///             _ => self.default_routes(command),
    ///         }
    ///     }
    /// }
    /// #
    /// # impl ApplicationRouter {
    /// #   fn handle_command_a(&self, _: Command) -> Option<Command> { None }
    /// #   fn handle_command_b(&self, _: Command) -> Option<Command> { None }
    /// # }
    /// ```
    fn route(
        &mut self,
        command: Command,
        _ctx: &mut Self::Context,
    ) -> Option<Command> {
        self.default_routes(command)
    }

    /// Routes the built-in commands to their respective handler.
    ///
    /// *Do not override this one, as it provides the routes to built-in
    /// commands. Changing it to something else could lead to your device not
    /// being compliant with the ERCP Basic specification.*
    fn default_routes(&mut self, command: Command) -> Option<Command> {
        match command.code() {
            PING => self.handle_ping(command),
            ACK => self.handle_ack(command),
            NACK => self.handle_nack(command),
            RESET => self.handle_reset(command),
            PROTOCOL => self.handle_protocol(command),
            VERSION => self.handle_version(command),
            MAX_LENGTH => self.handle_max_length(command),
            DESCRIPTION => self.handle_description(command),
            LOG => self.handle_log(command),
            _ => self.default_handler(command),
        }
    }

    /// Handles a [`Ping()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ping).
    ///
    /// Replies an
    /// [`Ack()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ack)
    /// in all cases.
    fn handle_ping(&mut self, _command: Command) -> Option<Command> {
        Some(ack!())
    }

    /// Handles an [`Ack()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ack).
    ///
    /// Returns `None`.
    fn handle_ack(&mut self, _command: Command) -> Option<Command> {
        None
    }

    /// Handles a [`Nack(reason)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#nackreason).
    ///
    /// Returns `None`.
    fn handle_nack(&mut self, _command: Command) -> Option<Command> {
        None
    }

    /// Handles a [`Reset()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#reset).
    ///
    /// The default implementation forwards the command to
    /// [`Router::default_handler`]. You can override it with an implementation
    /// that actually resets the device.
    fn handle_reset(&mut self, command: Command) -> Option<Command> {
        self.default_handler(command)
    }

    /// Handles a [`Protocol()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#protocol).
    ///
    /// Replies with the protocol version implemented by `ercp_basic.rs`.
    fn handle_protocol(&mut self, _command: Command) -> Option<Command> {
        Some(protocol_reply!(version::PROTOCOL_VERSION))
    }

    /// Handles a [`Version(component)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#versioncomponent).
    ///
    /// Replies with the version of the component passed as argument. The
    /// version itself is resolved by [`Router::version`]. You should override
    /// the latter and not this one.
    ///
    /// If the provided arguments are not valid, replies a
    /// [`Nack(INVALID_ARGUMENTS)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#nackreason)
    /// instead.
    fn handle_version(&mut self, command: Command) -> Option<Command> {
        if command.length() == 1 {
            let version = self.version(command.value()[0]);
            Some(version_reply!(version))
        } else {
            Some(nack!(nack_reason::INVALID_ARGUMENTS))
        }
    }

    /// Handles a [`Max_Length()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#max_length).
    ///
    /// Replies with the `MAX_LEN` parameter specified when instantiating the
    /// ERCP Basic driver.
    fn handle_max_length(&mut self, _command: Command) -> Option<Command> {
        Some(max_length_reply!(MAX_LEN as u8))
    }

    /// Handles a [`Description()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#description).
    ///
    /// Replies with the device description returned by [`Router::description`].
    /// You should override the latter and not this one.
    fn handle_description(&mut self, _command: Command) -> Option<Command> {
        Some(description_reply!(self.description()))
    }

    /// Handles a [`Log(message)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#logmessage).
    ///
    /// Replies an
    /// [`Ack()`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#ack)
    /// in all cases.
    fn handle_log(&mut self, _command: Command) -> Option<Command> {
        Some(ack!())
    }

    /// Handles any unknown command.
    ///
    /// Replies a
    /// [`Nack(UNKNOWN_COMMAND)`](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md#nackreason)
    /// in all cases.
    fn default_handler(&mut self, _command: Command) -> Option<Command> {
        Some(nack!(nack_reason::UNKNOWN_COMMAND))
    }

    /// Returns the version of the given component.
    ///
    /// The default implementation simply calls [`Router::default_versions`],
    /// which returns the version for the built-in components. To add your own
    /// component versions, you need to override it:
    ///
    /// ```
    /// use ercp_basic::{Command, Router};
    ///
    /// struct ApplicationRouter;
    ///
    /// # const COMPONENT_A: u8 = 0x10;
    /// # const COMPONENT_B: u8 = 0x11;
    /// # const VERSION_OF_A: &str = "";
    /// # const VERSION_OF_B: &str = "";
    /// #
    /// impl Router for ApplicationRouter {
    ///     type Context = ();
    ///
    ///     fn version(&self, component: u8) -> &str {
    ///         match component {
    ///             // Map custom components to their version.
    ///             COMPONENT_A => VERSION_OF_A,
    ///             COMPONENT_B => VERSION_OF_B,
    ///
    ///             // Always call self.default_versions in the default path.
    ///             _ => self.default_versions(component),
    ///         }
    ///     }
    /// }
    /// ```
    fn version(&self, component: u8) -> &str {
        self.default_versions(component)
    }

    /// Returns the version for built-in components.
    ///
    /// This returns:
    ///
    /// * the value returned by [`Router::firmware_version`] for the firmware,
    /// * the current [version](`version::LIBRARY_VERSION`) of `ercp_basic.rs`
    ///   for the ERCP library.
    /// * `"unknown_component"` for any other component.
    fn default_versions(&self, component: u8) -> &str {
        match component {
            component::FIRMWARE => self.firmware_version(),
            component::ERCP_LIBRARY => version::LIBRARY_VERSION,
            _ => "unknown_component",
        }
    }

    /// Returns the version of the firmware.
    ///
    /// *You should override this function to return the actual version of your
    /// firmware.*
    ///
    /// The default implementation returns `"Generic ERCP firmware"`.
    fn firmware_version(&self) -> &str {
        "Generic ERCP firmware"
    }

    /// Returns the description of the device.
    ///
    /// *You should override this function to return the actual description of
    /// your firmware.*
    ///
    /// The default implementation returns `"Generic ERCP device"`.
    fn description(&self) -> &str {
        "Generic ERCP device"
    }
}

/// A concrete router using the default implementations.
#[derive(Debug)]
pub struct DefaultRouter;

impl<const MAX_LEN: usize> Router<MAX_LEN> for DefaultRouter {
    type Context = ();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{description, max_length, ping, protocol};

    use proptest::collection::vec;
    use proptest::num::u8;
    use proptest::prelude::*;

    #[test]
    fn to_ping_replies_an_ack() {
        let mut router: Box<dyn Router<255, Context = _>> =
            Box::new(DefaultRouter);

        assert_eq!(router.route(ping!(), &mut ()), Some(ack!()));
    }

    #[test]
    fn to_ack_replies_nothing() {
        let mut router: Box<dyn Router<255, Context = _>> =
            Box::new(DefaultRouter);

        assert_eq!(router.route(ack!(), &mut ()), None);
    }

    proptest! {
        #[test]
        fn to_nack_replies_nothing(
            reason in vec(u8::ANY, 0..=u8::MAX as usize)
        ) {
            let mut router: Box<dyn Router<255, Context = _>> =
                Box::new(DefaultRouter);

            let nack = Command::new(NACK, &reason).unwrap();
            assert_eq!(router.route(nack, &mut ()), None);
        }
    }

    #[test]
    fn to_protocol_replies_the_protocol_version() {
        let mut router: Box<dyn Router<255, Context = _>> =
            Box::new(DefaultRouter);

        assert_eq!(
            router.route(protocol!(), &mut ()),
            Some(protocol_reply!(version::PROTOCOL_VERSION))
        );
    }

    #[test]
    fn to_firmware_version_replies_a_generic_version_by_default() {
        let mut router: Box<dyn Router<255, Context = _>> =
            Box::new(DefaultRouter);

        assert_eq!(
            router.route(version!(component::FIRMWARE), &mut ()),
            Some(version_reply!("Generic ERCP firmware"))
        );
    }

    #[test]
    fn to_ercp_lib_version_replies_the_current_ercp_basic_rs_version() {
        let mut router: Box<dyn Router<255, Context = _>> =
            Box::new(DefaultRouter);

        assert_eq!(
            router.route(version!(component::ERCP_LIBRARY), &mut ()),
            Some(version_reply!(version::LIBRARY_VERSION))
        );
    }

    proptest! {
        #[test]
        fn to_other_components_version_replies_unknown_component(
            component in u8::ANY,
        ) {
            prop_assume!(
                component != component::FIRMWARE
                && component != component::ERCP_LIBRARY
            );

            let mut router: Box<dyn Router<255, Context = _>> =
                Box::new(DefaultRouter);

            assert_eq!(
                router.route(version!(component), &mut ()),
                Some(version_reply!("unknown_component"))
            );
        }
    }

    proptest! {
        #[test]
        fn to_version_with_invalid_number_of_parameters_replies_an_error(
            value in vec(u8::ANY, 0..=u8::MAX as usize),
        ) {
            prop_assume!(value.len() != 1);

            let mut router: Box<dyn Router<255, Context = _>> =
                Box::new(DefaultRouter);

            let command = Command::new(VERSION, &value).unwrap();

            assert_eq!(
                router.route(command, &mut ()),
                Some(nack!(nack_reason::INVALID_ARGUMENTS))
            );
        }
    }

    #[test]
    fn to_max_length_replies_the_const_max_len() {
        let mut router: Box<dyn Router<92, Context = _>> =
            Box::new(DefaultRouter);

        assert_eq!(
            router.route(max_length!(), &mut ()),
            Some(max_length_reply!(92))
        );
    }

    #[test]
    fn to_description_replies_a_generic_description_by_default() {
        let mut router: Box<dyn Router<255, Context = _>> =
            Box::new(DefaultRouter);

        assert_eq!(
            router.route(description!(), &mut ()),
            Some(description_reply!("Generic ERCP device"))
        );
    }

    proptest! {
        #[test]
        fn to_log_replies_an_ack(message in ".{0,100}") {
            let mut router: Box<dyn Router<255, Context = _>> =
                Box::new(DefaultRouter);

            assert_eq!(
                router.route(Command::log(&message).unwrap(), &mut ()),
                Some(Command::ack())
            );
        }
    }

    proptest! {
        #[test]
        fn to_any_other_command_replies_a_nack_unknown_command(
            code in u8::ANY,
            value in vec(u8::ANY, 0..=u8::MAX as usize),
        ) {
            prop_assume!(
                code != PING
                && code != ACK
                && code != NACK
                && code != PROTOCOL
                && code != VERSION
                && code != MAX_LENGTH
                && code != DESCRIPTION
                && code != LOG
            );

            let mut router: Box<dyn Router<255, Context = _>> =
                Box::new(DefaultRouter);

            let command = Command::new(code, &value).unwrap();

            assert_eq!(
                router.route(command, &mut ()),
                Some(nack!(nack_reason::UNKNOWN_COMMAND))
            );
        }
    }
}
