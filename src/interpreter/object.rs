use std::{fmt, collections::HashMap};

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

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Hash)]
pub struct ReturnValue {
    pub value: Box<MObject>,
}

impl fmt::Display for ReturnValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Hash)]
pub struct MError {
    pub value: String,
}

impl fmt::Display for MError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ERROR: {}", self.value)
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Environment {
    store: HashMap<String, MObject>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            store: HashMap::new(),
        }
    }

    pub fn get(&self, key: &String) -> Option<&MObject> {
        self.store.get(key)
    }

    pub fn insert(&mut self, key: String, value: MObject) -> Option<MObject> {
        self.store.insert(key, value)
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Hash)]
pub enum MObject {
    Int(Integer),
    Bool(Boolean),
    Return(ReturnValue),
    Err(MError),
    Null,
}

impl fmt::Display for MObject {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MObject::Int(x) => write!(f, "{}", x),
            MObject::Bool(x) => write!(f, "{}", x),
            MObject::Return(x) => write!(f, "{}", x),
            MObject::Err(x) => write!(f, "{}", x),
            MObject::Null => write!(f, "null"),
        }
    }
}
