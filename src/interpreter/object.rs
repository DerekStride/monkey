use crate::ast;
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

#[derive(PartialEq, Eq, Clone, Debug)]
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
    outer: Option<Box<Environment>>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            store: HashMap::new(),
            outer: None,
        }
    }

    pub fn enclose(env: Environment) -> Self {
        Self {
            store: HashMap::new(),
            outer: Some(Box::new(env)),
        }
    }

    pub fn get(&self, key: &String) -> Option<&MObject> {
        if let Some(x) = self.store.get(key) {
            Some(x)
        } else if let Some(env) = &self.outer {
            env.get(key)
        } else {
            None
        }
    }

    pub fn insert(&mut self, key: String, value: MObject) -> Option<MObject> {
        self.store.insert(key, value)
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Function {
    pub params: Vec<ast::Identifier>,
    pub body: ast::BlockStatement,
    pub env: Environment,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "fn(")?;
        write!(
            f,
            "{}",
            self.params.iter()
                .map(|p| format!("{}", p))
                .collect::<Vec<String>>()
                .join(", ")
        )?;
        write!(f, ") {}", self.body)
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum MObject {
    Int(Integer),
    Bool(Boolean),
    Return(ReturnValue),
    Err(MError),
    Fn(Function),
    Null,
}

impl fmt::Display for MObject {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MObject::Int(x) => write!(f, "{}", x),
            MObject::Bool(x) => write!(f, "{}", x),
            MObject::Return(x) => write!(f, "{}", x),
            MObject::Err(x) => write!(f, "{}", x),
            MObject::Fn(x) => write!(f, "{}", x),
            MObject::Null => write!(f, "null"),
        }
    }
}
