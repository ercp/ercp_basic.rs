// TODO: Better documentation.
//! ERCP Router and default implementation.

use crate::command::*;

/// An ERCP router.
pub trait Router {
    fn route(&mut self, command: Command) -> Option<Command> {
        self.default_routes(command)
    }

    fn default_routes(&mut self, command: Command) -> Option<Command> {
        match command.command() {
            PING => self.handle_ping(command),
            _ => self.default_handler(command),
        }
    }

    fn handle_ping(&mut self, _command: Command) -> Option<Command> {
        Some(Command::ack())
    }

    fn default_handler(&mut self, _command: Command) -> Option<Command> {
        Command::new(NACK, &[nack_reason::UNKNOWN_COMMAND]).ok()
    }
}

/// A concrete ERCP router using the default implementations.
#[derive(Debug)]
pub struct DefaultRouter;

impl Router for DefaultRouter {}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::collection::vec;
    use proptest::prelude::*;

    #[test]
    fn a_ping_replies_an_ack() {
        assert_eq!(DefaultRouter.route(Command::ping()), Some(Command::ack()));
    }

    proptest! {
        #[test]
        fn any_other_command_replies_a_nack_unknown_command(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            prop_assume!(command != PING);

            let command = Command::new(command, &value).unwrap();
            let nack =
                Command::new(NACK, &[nack_reason::UNKNOWN_COMMAND]).unwrap();

            assert_eq!(DefaultRouter.route(command), Some(nack));
        }
    }
}
