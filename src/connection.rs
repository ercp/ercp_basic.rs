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

//! ERCP Basic connection.
//!
//! *This is an internal module.*
//!
//! The connection is an abstraction over the link layer under ERCP Basic. This
//! is where bytes are sent and received, using an [`Adapter`].

use crate::adapter::Adapter;
use crate::command::Command;
use crate::EOT;

/// An ERCP Basic connection.
#[derive(Debug)]
pub struct Connection<A: Adapter> {
    adapter: A,
}

impl<A: Adapter> Connection<A> {
    /// Creates a new connection.
    pub fn new(adapter: A) -> Self {
        Self { adapter }
    }

    /// Releases the `adapter`.
    pub fn release(self) -> A {
        self.adapter
    }

    /// Reads a byte from the connection.
    pub fn read(&mut self) -> Result<Option<u8>, A::Error> {
        self.adapter.read()
    }

    /// Writes a byte to the connection.
    pub fn write(&mut self, byte: u8) -> Result<(), A::Error> {
        self.adapter.write(byte)
    }

    /// Sends a command on the connection.
    pub fn send(&mut self, command: Command) -> Result<(), A::Error> {
        for byte in [b'E', b'R', b'C', b'P', b'B'] {
            self.write(byte)?;
        }

        self.write(command.code())?;
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
pub mod tests {
    use super::*;

    use std::collections::VecDeque;

    use proptest::collection::vec;
    use proptest::prelude::*;

    #[derive(Debug, Default)]
    pub struct TestAdapter {
        tx_buffer: VecDeque<u8>,
        rx_buffer: VecDeque<u8>,
        pub write_error: Option<()>,
        pub read_error: Option<()>,
    }

    impl Adapter for TestAdapter {
        type Error = ();

        fn read(&mut self) -> Result<Option<u8>, Self::Error> {
            match self.read_error {
                None => Ok(self.rx_buffer.pop_front()),
                Some(()) => Err(()),
            }
        }

        fn write(&mut self, byte: u8) -> Result<(), Self::Error> {
            match self.write_error {
                None => {
                    self.tx_buffer.push_back(byte);
                    Ok(())
                }

                Some(()) => Err(()),
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
            connection.adapter.read_error = Some(());
            assert_eq!(connection.read(), Err(()));
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
                connection.adapter.write_error = Some(());
                assert_eq!(connection.write(byte), Err(()));
            });
        }
    }

    /////////////////////////////// Framing ////////////////////////////////

    proptest! {
        #[test]
        fn send_writes_a_frame_on_the_connection(
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut connection| {
                let command = Command::new(code, &value).unwrap();
                let expected_frame = command.as_frame();

                assert_eq!(connection.send(command), Ok(()));
                assert_eq!(connection.adapter.test_receive(), expected_frame);
            });
        }
    }

    proptest! {
        #[test]
        fn send_returns_an_error_if_there_is_one(
            code in 0..=u8::MAX,
            value in vec(0..=u8::MAX, 0..=u8::MAX as usize),
        ) {
            setup(|mut connection| {
                let command = Command::new(code, &value).unwrap();
                connection.adapter.write_error = Some(());

                assert_eq!(connection.send(command), Err(()));
            });
        }
    }
}
