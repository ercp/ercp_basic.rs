// Copyright 2022 Jean-Philippe Cugnet
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

//! ERCP Basic receiver.
//!
//! *This is an internal module.*
//!
//! The receiver is the object that handles incoming data and parses it.

pub mod standard_receiver;

mod frame_buffer;

pub use standard_receiver::StandardReceiver;

use crate::{
    command::Command,
    error::{FrameError, ReceiveError},
};

/// An ERCP Basic receiver.
pub trait Receiver {
    /// Creates a new receiver.
    fn new() -> Self;

    /// Receives a byte.
    fn receive(&mut self, byte: u8) -> Result<(), ReceiveError>;

    /// Returns wether a complete frame has been received.
    ///
    /// If it returns `true`, you should then call `process`.
    fn complete_frame_received(&self) -> bool;

    /// Checks the received frame.
    fn check_frame(&self) -> Result<Command, FrameError>;

    /// Resets the receiver so it is ready to accept and parse frames.
    fn reset(&mut self);
}
