// TODO: Better documentation.
//! ERCP Router and default implementation.

use crate::command::*;
use crate::{
    ack, description_reply, max_length_reply, nack, protocol_reply, version,
    version_reply,
};

/// An ERCP router.
pub trait Router<const MAX_LEN: usize> {
    type Context;

    fn route(
        &mut self,
        command: Command,
        _: &mut Self::Context,
    ) -> Option<Command> {
        self.default_routes(command)
    }

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

    fn handle_ping(&mut self, _command: Command) -> Option<Command> {
        Some(ack!())
    }

    fn handle_ack(&mut self, _command: Command) -> Option<Command> {
        None
    }

    fn handle_nack(&mut self, _command: Command) -> Option<Command> {
        None
    }

    fn handle_reset(&mut self, command: Command) -> Option<Command> {
        self.default_handler(command)
    }

    fn handle_protocol(&mut self, _command: Command) -> Option<Command> {
        Some(protocol_reply!(version::PROTOCOL_VERSION))
    }

    fn handle_version(&mut self, command: Command) -> Option<Command> {
        if command.length() == 1 {
            let version = self.version(command.value()[0]);
            Some(version_reply!(version))
        } else {
            Some(nack!(nack_reason::INVALID_ARGUMENTS))
        }
    }

    fn handle_max_length(&mut self, _command: Command) -> Option<Command> {
        Some(max_length_reply!(MAX_LEN as u8))
    }

    fn handle_description(&mut self, _command: Command) -> Option<Command> {
        Some(description_reply!(self.description()))
    }

    fn handle_log(&mut self, _command: Command) -> Option<Command> {
        Some(ack!())
    }

    fn default_handler(&mut self, _command: Command) -> Option<Command> {
        Some(nack!(nack_reason::UNKNOWN_COMMAND))
    }

    fn version(&self, component: u8) -> &str {
        self.default_versions(component)
    }

    fn default_versions(&self, component: u8) -> &str {
        match component {
            component::FIRMWARE => self.firmware_version(),
            component::ERCP_LIBRARY => version::LIBRARY_VERSION,
            _ => "unknown_component",
        }
    }

    fn firmware_version(&self) -> &str {
        "Generic ERCP firmware"
    }

    fn description(&self) -> &str {
        "Generic ERCP device"
    }
}

/// A concrete ERCP router using the default implementations.
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
            reason in vec(0..=u8::MAX, 0..=u8::MAX as usize)
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
            component in 0..=u8::MAX,
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
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
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
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
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
