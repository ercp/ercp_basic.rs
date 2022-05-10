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

use super::Timer;

/// A timer based on [`std::time`].
///
/// This timer can be used on platforms where the standard library is available.
///
/// # Example
///
/// ```
/// use ercp_basic::{timer::StdTimer, ErcpBasic, DefaultRouter};
///
/// # use ercp_basic::{Adapter};
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
/// let adapter = SomeAdapter::new(/* parameters omitted */);
/// let ercp = ErcpBasic::<_, _, _>::new(adapter, StdTimer, DefaultRouter);
/// ```
pub struct StdTimer;

impl Timer for StdTimer {
    type Instant = std::time::Instant;
    type Duration = std::time::Duration;

    fn now(&mut self) -> Self::Instant {
        std::time::Instant::now()
    }
}
