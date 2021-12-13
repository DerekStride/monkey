use crate::{ast, error::Error};
use std::{fmt, collections::HashMap};

type Result<T> = std::result::Result<T, Error>;

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
pub struct MString {
    pub value: String,
}

impl fmt::Display for MString {
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

#[derive(Clone)]
pub enum Builtin {
    Len(fn(&mut Vec<MObject>) -> Result<MObject>),
}

impl fmt::Display for Builtin {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Builtin::Len(_) => write!(f, "Builtin: len(str)")
        }
    }
}

impl fmt::Debug for Builtin {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Builtin::Len(_) => write!(f, "Builtin: len(str)")
        }
    }
}


impl PartialEq for Builtin {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl Eq for Builtin {}

const LEN: MObject = MObject::Builtin(
    Builtin::Len(
        |args: &mut Vec<MObject>| -> Result<MObject> {
            if args.len() != 1 {
                return Ok(
                    MObject::Err(
                        MError {
                            value: format!("wrong number of arguments, got: {}, want: 1", args.len()),
                        }
                    )
                )

            }

            let arg = args.pop().unwrap();

            if let MObject::Str(s) = arg {
                Ok(MObject::Int(Integer { value: s.value.len() as i128 }))
            } else {
                Ok(
                    MObject::Err(
                        MError {
                            value: format!("argument to 'len' not supported, got: {}", arg),
                        }
                    )
                )
            }
        }
    )
);

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Environment {
    store: HashMap<String, MObject>,
    outer: Option<Box<Environment>>,
    builtins: Option<Box<HashMap<String, MObject>>>,
}

impl Environment {
    pub fn new() -> Self {
        let mut builtins = HashMap::new();
        builtins.insert("len".to_string(), LEN);

        Self {
            store: HashMap::new(),
            outer: None,
            builtins: Some(Box::new(builtins)),
        }
    }

    pub fn enclose(env: Environment) -> Self {
        Self {
            store: HashMap::new(),
            outer: Some(Box::new(env)),
            builtins: None,
        }
    }

    pub fn get(&self, key: &String) -> Option<&MObject> {
        if let Some(x) = self.store.get(key) {
            Some(x)
        } else if let Some(env) = &self.outer {
            env.get(key)
        } else if let Some(builtins) = &self.builtins {
            builtins.get(key)
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
    Str(MString),
    Return(ReturnValue),
    Err(MError),
    Fn(Function),
    Builtin(Builtin),
    Null,
}

impl fmt::Display for MObject {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MObject::Int(x) => write!(f, "{}", x),
            MObject::Bool(x) => write!(f, "{}", x),
            MObject::Str(x) => write!(f, "{}", x),
            MObject::Return(x) => write!(f, "{}", x),
            MObject::Err(x) => write!(f, "{}", x),
            MObject::Fn(x) => write!(f, "{}", x),
            MObject::Builtin(x) => write!(f, "{}", x),
            MObject::Null => write!(f, "null"),
        }
    }
}
