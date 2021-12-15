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
        write!(f, "\"{}\"", self.value)
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct MArray {
    pub elements: Vec<MObject>,
}

impl fmt::Display for MArray {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "[{}]",
            self.elements.iter()
                .map(|e| format!("{}", e))
                .collect::<Vec<String>>()
                .join(", ")
        )
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
    First(fn(&mut Vec<MObject>) -> Result<MObject>),
    Last(fn(&mut Vec<MObject>) -> Result<MObject>),
    Rest(fn(&mut Vec<MObject>) -> Result<MObject>),
    Push(fn(&mut Vec<MObject>) -> Result<MObject>),
}

impl fmt::Display for Builtin {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Builtin::Len(_) => write!(f, "Builtin: len(str | array)"),
            Builtin::First(_) => write!(f, "Builtin: first(array)"),
            Builtin::Last(_) => write!(f, "Builtin: last(array)"),
            Builtin::Rest(_) => write!(f, "Builtin: rest(array)"),
            Builtin::Push(_) => write!(f, "Builtin: push(array, arg)"),
        }
    }
}

impl fmt::Debug for Builtin {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Builtin::Len(_) => write!(f, "Builtin: len(str | array)"),
            Builtin::First(_) => write!(f, "Builtin: first(array)"),
            Builtin::Last(_) => write!(f, "Builtin: last(array)"),
            Builtin::Rest(_) => write!(f, "Builtin: rest(array)"),
            Builtin::Push(_) => write!(f, "Builtin: push(array, arg)"),
        }
    }
}


impl PartialEq for Builtin {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Builtin::Len(_) => {
                match other {
                    Builtin::Len(_) => true,
                    _ => false,
                }
            },
            Builtin::First(_) => {
                match other {
                    Builtin::First(_) => true,
                    _ => false,
                }
            },
            Builtin::Last(_) => {
                match other {
                    Builtin::Last(_) => true,
                    _ => false,
                }
            },
            Builtin::Rest(_) => {
                match other {
                    Builtin::Rest(_) => true,
                    _ => false,
                }
            },
            Builtin::Push(_) => {
                match other {
                    Builtin::Push(_) => true,
                    _ => false,
                }
            },
        }
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
            } else if let MObject::Array(arr) = arg {
                Ok(MObject::Int(Integer { value: arr.elements.len() as i128 }))
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

const FIRST: MObject = MObject::Builtin(
    Builtin::First(
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

            if let MObject::Array(arr) = arg {
                if let Some(o) = arr.elements.get(0) {
                    Ok(o.clone())
                } else {
                    Ok(MObject::Null)
                }
            } else {
                Ok(
                    MObject::Err(
                        MError {
                            value: format!("argument to 'first' not supported, got: {}", arg),
                        }
                    )
                )
            }
        }
    )
);

const LAST: MObject = MObject::Builtin(
    Builtin::Last(
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

            if let MObject::Array(arr) = arg {
                if let Some(o) = arr.elements.last() {
                    Ok(o.clone())
                } else {
                    Ok(MObject::Null)
                }
            } else {
                Ok(
                    MObject::Err(
                        MError {
                            value: format!("argument to 'last' not supported, got: {}", arg),
                        }
                    )
                )
            }
        }
    )
);

const REST: MObject = MObject::Builtin(
    Builtin::Rest(
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

            if let MObject::Array(arr) = arg {
                if !arr.elements.is_empty() {
                    let elements = arr.elements[1..].to_vec();
                    Ok(MObject::Array(MArray { elements }))
                } else {
                    Ok(MObject::Null)
                }
            } else {
                Ok(
                    MObject::Err(
                        MError {
                            value: format!("argument to 'rest' not supported, got: {}", arg),
                        }
                    )
                )
            }
        }
    )
);

const PUSH: MObject = MObject::Builtin(
    Builtin::Push(
        |args: &mut Vec<MObject>| -> Result<MObject> {
            if args.len() != 2 {
                return Ok(
                    MObject::Err(
                        MError {
                            value: format!("wrong number of arguments, got: {}, want: 2", args.len()),
                        }
                    )
                )
            }

            let array = args.remove(0);

            if let MObject::Array(arr) = array {
                let arg = args.pop().unwrap();
                let mut elements = arr.elements.clone();
                elements.push(arg);

                Ok(MObject::Array(MArray { elements }))
            } else {
                Ok(
                    MObject::Err(
                        MError {
                            value: format!("first argument to 'push' not supported, got: {}", array),
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
        builtins.insert("first".to_string(), FIRST);
        builtins.insert("last".to_string(), LAST);
        builtins.insert("rest".to_string(), REST);
        builtins.insert("push".to_string(), PUSH);

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
    Array(MArray),
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
            MObject::Array(x) => write!(f, "{}", x),
            MObject::Return(x) => write!(f, "{}", x),
            MObject::Err(x) => write!(f, "{}", x),
            MObject::Fn(x) => write!(f, "{}", x),
            MObject::Builtin(x) => write!(f, "{}", x),
            MObject::Null => write!(f, "null"),
        }
    }
}
