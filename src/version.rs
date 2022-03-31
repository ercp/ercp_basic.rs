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

//! ERCP Basic protocol and library versions.

/// A protocol version.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Version {
    /// The major version, denoting API-incompatible changes.
    pub major: u8,
    /// The minor version, denoting new features.
    pub minor: u8,
    /// The patch version, denoting fixes.
    pub patch: u8,
}

/// The version of ERCP Basic implemented by the library.
pub const PROTOCOL_VERSION: Version = Version {
    major: 0,
    minor: 1,
    patch: 0,
};

/// The version of `ercp_basic.rs`.
pub const LIBRARY_VERSION: &str =
    concat!(env!("CARGO_PKG_NAME"), ".rs ", env!("CARGO_PKG_VERSION"));
