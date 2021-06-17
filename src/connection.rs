// TODO: Better documentation.
//! ERCP Connection.

use crate::adapter::Adapter;
use crate::command::Command;
use crate::error::IoError;
use crate::EOT;

/// An ERCP Basic connection.
#[derive(Debug)]
pub(crate) struct Connection<A: Adapter> {
    adapter: A,
}

impl<A: Adapter> Connection<A> {
    pub fn new(adapter: A) -> Self {
        Self { adapter }
    }

    pub fn release(self) -> A {
        self.adapter
    }

    pub fn read(&mut self) -> Result<Option<u8>, IoError> {
        self.adapter.read()
    }

    pub fn write(&mut self, byte: u8) -> Result<(), IoError> {
        self.adapter.write(byte)
    }

    pub fn send(&mut self, command: Command) -> Result<(), IoError> {
        for byte in [b'E', b'R', b'C', b'P', b'B'] {
            self.write(byte)?;
        }

        self.write(command.command())?;
        self.write(command.length())?;

        for &byte in command.value() {
            self.write(byte)?;
        }

        self.write(command.crc())?;
        self.write(EOT)?;

        Ok(())
    }

    /// Returns a mutable reference to the adapter.
    ///
    /// This is useful for accessing the backdoor functions of a test adapter.
    #[cfg(test)]
    pub fn adapter(&mut self) -> &mut A {
        &mut self.adapter
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::error::IoError;

    use std::collections::VecDeque;

    use proptest::collection::vec;
    use proptest::prelude::*;

    #[derive(Debug, Default)]
    pub(crate) struct TestAdapter {
        tx_buffer: VecDeque<u8>,
        rx_buffer: VecDeque<u8>,
        pub write_error: Option<IoError>,
        pub read_error: Option<IoError>,
    }

    impl Adapter for TestAdapter {
        fn read(&mut self) -> Result<Option<u8>, IoError> {
            match self.read_error {
                None => Ok(self.rx_buffer.pop_front()),
                Some(error) => Err(error),
            }
        }

        fn write(&mut self, byte: u8) -> Result<(), IoError> {
            match self.write_error {
                None => {
                    self.tx_buffer.push_back(byte);
                    Ok(())
                }

                Some(error) => Err(error),
            }
        }
    }

    impl TestAdapter {
        pub fn test_send(&mut self, data: &[u8]) {
            self.rx_buffer.extend(data);
        }

        pub fn test_receive(&mut self) -> &[u8] {
            self.tx_buffer.make_contiguous()
        }
    }

    ////////////////////////////// Test setup //////////////////////////////

    fn setup(test: impl Fn(Connection<TestAdapter>)) {
        let adapter = TestAdapter::default();
        let connection = Connection::new(adapter);
        test(connection);
    }

    //////////////////////// Read / write operations ///////////////////////

    proptest! {
        #[test]
        fn read_reads_a_byte_from_the_adapter(byte in 0..=u8::MAX) {
            setup(|mut connection| {
                connection.adapter.test_send(&[byte]);
                assert_eq!(connection.read(), Ok(Some(byte)));
            });
        }
    }

    #[test]
    fn read_returns_none_if_there_is_no_byte_to_read() {
        setup(|mut connection| {
            assert_eq!(connection.read(), Ok(None));
        });
    }

    #[test]
    fn read_returns_an_error_on_read_error() {
        setup(|mut connection| {
            connection.adapter.read_error = Some(IoError::IoError);
            assert_eq!(connection.read(), Err(IoError::IoError));
        });
    }

    proptest! {
        #[test]
        fn write_write_a_byte_with_the_adapter(byte in 0..=u8::MAX) {
            setup(|mut connection| {
                assert_eq!(connection.write(byte), Ok(()));
                assert_eq!(connection.adapter.test_receive(), &[byte]);
            });
        }
    }

    proptest! {
        #[test]
        fn write_returns_an_error_on_write_error(byte in 0..=u8::MAX) {
            setup(|mut connection| {
                connection.adapter.write_error = Some(IoError::IoError);
                assert_eq!(connection.write(byte), Err(IoError::IoError));
            });
        }
    }

    /////////////////////////////// Framing ////////////////////////////////

    proptest! {
        #[test]
        fn send_writes_a_frame_on_the_connection(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut connection| {
                let command = Command::new(command, &value).unwrap();
                let expected_frame = command.as_frame();

                assert_eq!(connection.send(command), Ok(()));
                assert_eq!(connection.adapter.test_receive(), expected_frame);
            });
        }
    }

    proptest! {
        #[test]
        fn send_returns_an_error_if_there_is_one(
            command in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut connection| {
                let command = Command::new(command, &value).unwrap();
                connection.adapter.write_error = Some(IoError::IoError);

                assert_eq!(connection.send(command), Err(IoError::IoError));
            });
        }
    }
}
