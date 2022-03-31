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

//! Connection adapters.

#[cfg(feature = "rtt")]
mod rtt;
#[cfg(feature = "rtt-probe-rs")]
mod rtt_probe_rs;
#[cfg(feature = "serial")]
mod serial;
#[cfg(feature = "serial-host")]
mod serial_host;

#[cfg(feature = "rtt")]
pub use rtt::RttAdapter;
#[cfg(feature = "rtt-probe-rs")]
pub use rtt_probe_rs::RttProbeRsAdapter;
#[cfg(feature = "serial")]
pub use serial::SerialAdapter;
#[cfg(feature = "serial-host")]
pub use serial_host::SerialPortAdapter;

/// A connection adapter.
///
/// An adapter is the piece of software that makes the link between the ERCP
/// Basic driver and the actual communication medium.
///
/// You can find several built-in adapters in the [`adapter`](`self`) module,
/// and you can write your own by implementing the [`Adapter`] trait.
pub trait Adapter {
    /// The error type for the adapter.
    type Error;

    /// Reads a byte from the connection.
    ///
    /// This function tries to read a byte from the connection. If a byte is
    /// available, it returns `Ok(Some(value))`. If nothing is available, it
    /// does not block and `Ok(None)` is returned. There is however no guarantee
    /// on the time the actual implementation takes to return a `Ok(None)`.
    ///
    /// # Errors
    ///
    /// Any call to this function may generate a [`Self::Error`].
    fn read(&mut self) -> Result<Option<u8>, Self::Error>;

    /// Writes a byte to the connection.
    ///
    /// This function writes a byte to the connection. It may block, and there
    /// is no guarantee that when it returns the byte has been actually written
    /// on the medium.
    ///
    /// # Errors
    ///
    /// Any call to this function may generate a [`Self::Error`].
    fn write(&mut self, byte: u8) -> Result<(), Self::Error>;
}
