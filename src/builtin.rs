use std::{fmt, io::{self, Write}};

use crate::{
    error::Result,
    object::*,
};

#[derive(Clone)]
pub enum Builtin {
    Len(fn(&mut Vec<MObject>) -> Result<MObject>),
    First(fn(&mut Vec<MObject>) -> Result<MObject>),
    Last(fn(&mut Vec<MObject>) -> Result<MObject>),
    Rest(fn(&mut Vec<MObject>) -> Result<MObject>),
    Push(fn(&mut Vec<MObject>) -> Result<MObject>),
    Puts(fn(&mut Vec<MObject>) -> Result<MObject>),
}

impl fmt::Display for Builtin {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Builtin::Len(_) => write!(f, "Builtin: len(str | array)"),
            Builtin::First(_) => write!(f, "Builtin: first(array)"),
            Builtin::Last(_) => write!(f, "Builtin: last(array)"),
            Builtin::Rest(_) => write!(f, "Builtin: rest(array)"),
            Builtin::Push(_) => write!(f, "Builtin: push(array, arg)"),
            Builtin::Puts(_) => write!(f, "Builtin: puts(object, ...)"),
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
            Builtin::Puts(_) => write!(f, "Builtin: puts(object, ...)"),
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
            Builtin::Puts(_) => {
                match other {
                    Builtin::Puts(_) => true,
                    _ => false,
                }
            },
        }
    }
}

impl Eq for Builtin {}

pub const LEN: MObject = MObject::Builtin(
    Builtin::Len(self::len)
);

pub const FIRST: MObject = MObject::Builtin(
    Builtin::First(self::first)
);

pub const LAST: MObject = MObject::Builtin(
    Builtin::Last(self::last)
);

pub const REST: MObject = MObject::Builtin(
    Builtin::Rest(self::rest)
);

pub const PUSH: MObject = MObject::Builtin(
    Builtin::Push(self::push)
);

pub const PUTS: MObject = MObject::Builtin(
    Builtin::Puts(self::puts)
);

fn len(args: &mut Vec<MObject>) -> Result<MObject> {
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

fn first(args: &mut Vec<MObject>) -> Result<MObject> {
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
            Ok(NULL)
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

fn last(args: &mut Vec<MObject>) -> Result<MObject> {
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
            Ok(NULL)
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

fn rest(args: &mut Vec<MObject>) -> Result<MObject> {
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
            Ok(NULL)
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

fn push(args: &mut Vec<MObject>) -> Result<MObject> {
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

fn puts(args: &mut Vec<MObject>) -> Result<MObject> {
    let mut output = io::stdout();

    for obj in args {
        output.write_all(format!("{}\n", obj).as_bytes())?;
    };

    output.flush()?;

    Ok(NULL)
}
