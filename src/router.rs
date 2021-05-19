// TODO: Better documentation.
//! ERCP Router and default implementation.

use crate::command::*;

/// An ERCP router.
pub trait Router {
    type Context;

    fn route(
        &mut self,
        command: Command,
        _: &mut Self::Context,
    ) -> Option<Command> {
        self.default_routes(command)
    }

    fn default_routes(&mut self, command: Command) -> Option<Command> {
        match command.command() {
            PING => self.handle_ping(command),
            ACK => self.handle_ack(command),
            NACK => self.handle_nack(command),
            _ => self.default_handler(command),
        }
    }

    fn handle_ping(&mut self, _command: Command) -> Option<Command> {
        Some(Command::ack())
    }

    fn handle_ack(&mut self, _command: Command) -> Option<Command> {
        None
    }

    fn handle_nack(&mut self, _command: Command) -> Option<Command> {
        None
    }

    fn default_handler(&mut self, _command: Command) -> Option<Command> {
        Command::new(NACK, &[nack_reason::UNKNOWN_COMMAND]).ok()
    }
}

/// A concrete ERCP router using the default implementations.
#[derive(Debug)]
pub struct DefaultRouter;

impl Router for DefaultRouter {
    type Context = ();
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::collection::vec;
    use proptest::prelude::*;

    #[test]
    fn a_ping_replies_an_ack() {
        assert_eq!(
            DefaultRouter.route(Command::ping(), &mut ()),
            Some(Command::ack())
        );
    }

    #[test]
    fn an_ack_replies_nothing() {
        assert_eq!(DefaultRouter.route(Command::ack(), &mut ()), None);
    }

    proptest! {
        #[test]
        fn a_nack_replies_nothing(
            reason in vec(0..=u8::MAX, 0..=u8::MAX as usize)
        ) {
            let nack = Command::new(NACK, &reason).unwrap();
            assert_eq!(DefaultRouter.route(nack, &mut ()), None);
        }
    }

    proptest! {
        #[test]
        fn any_other_command_replies_a_nack_unknown_command(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(
                command != PING
                && command != ACK
                && command != NACK
            );

            let command = Command::new(command, &value).unwrap();
            let nack =
                Command::new(NACK, &[nack_reason::UNKNOWN_COMMAND]).unwrap();

            assert_eq!(DefaultRouter.route(command, &mut ()), Some(nack));
        }
    }
}
