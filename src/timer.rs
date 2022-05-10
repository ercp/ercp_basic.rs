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

//! Timers.

use core::ops::{Add, Sub};

/// A timer.
///
/// A timer is the piece of software that makes is possible for the ERCP Basic
/// driver to handle time, for providing timeout features.
///
/// You can find built-in timers in the [`timer`](self) module, and you can
/// write your own by implementing the [`Timer`] trait.
pub trait Timer {
    /// The type defining an instant in time.
    type Instant: Ord
        + Copy
        + Add<Self::Duration, Output = Self::Instant>
        + Sub<Self::Duration, Output = Self::Instant>
        + Sub<Self::Instant, Output = Self::Duration>;

    /// The type defining a duration of time.
    type Duration: Copy;

    /// Returns the current time.
    fn now(&mut self) -> Self::Instant;
}
