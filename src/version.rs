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
