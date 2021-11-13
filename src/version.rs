//! ERCP version.

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Version {
    pub major: u8,
    pub minor: u8,
    pub patch: u8,
}

pub const PROTOCOL_VERSION: Version = Version {
    major: 0,
    minor: 1,
    patch: 0,
};

pub const LIBRARY_VERSION: &str =
    concat!(env!("CARGO_PKG_NAME"), ".rs ", env!("CARGO_PKG_VERSION"));
