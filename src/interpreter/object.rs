use std::fmt;

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug, Hash)]
pub struct Integer {
    pub value: i128,
}

impl fmt::Display for Integer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug, Hash)]
pub struct Boolean {
    pub value: bool,
}

impl fmt::Display for Boolean {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug, Hash)]
pub enum MObject {
    Int(Integer),
    Bool(Boolean),
    Null,
}

impl fmt::Display for MObject {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MObject::Int(x) => write!(f, "{}", x),
            MObject::Bool(x) => write!(f, "{}", x),
            MObject::Null => write!(f, "null"),
        }
    }
}
