// TODO: Documentation

#[derive(Debug, PartialEq)]
pub enum Error {
    InvalidCRC,
    TooLong,
}

#[derive(Debug, PartialEq)]
pub enum IoError {
    IoError,
}
