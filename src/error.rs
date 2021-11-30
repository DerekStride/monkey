use std::{fmt, io};
use std::str::Utf8Error;
use std::string::FromUtf8Error;

#[derive(PartialEq, Debug)]
pub struct Error {
    details: String
}

impl Error {
    pub fn new(msg: String) -> Error {
        Self{details: msg}
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.details)
    }
}

impl std::error::Error for Error {
    fn description(&self) -> &str {
        &self.details
    }
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Self {
        Error::new(format!("{}", err))
    }
}

impl From<Utf8Error> for Error {
    fn from(err: Utf8Error) -> Self {
        Error::new(format!("{}", err))
    }
}

impl From<FromUtf8Error> for Error {
    fn from(err: FromUtf8Error) -> Self {
        Error::new(format!("{}", err))
    }
}
