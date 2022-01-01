use crate::{
    ast::{self, MNode},
    interpreter::{
        builtin::Builtin,
        environment::Environment,
    },
    compiler::code::{Instructions, MCode},
};
use std::{fmt, collections::HashMap};

pub const TRUE: MObject = MObject::Bool(Boolean { value: true });
pub const FALSE: MObject = MObject::Bool(Boolean { value: false });
pub const NULL: MObject = MObject::Null;

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

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Hash)]
pub enum HashKey {
    Str(MString),
    Bool(Boolean),
    Int(Integer),
}

impl fmt::Display for HashKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            HashKey::Str(x) => write!(f, "{}", x),
            HashKey::Bool(x) => write!(f, "{}", x),
            HashKey::Int(x) => write!(f, "{}", x),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct HashPair {
    pub key: MObject,
    pub value: MObject,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct MHash {
    pub pairs: HashMap<HashKey, HashPair>,
}

impl fmt::Display for MHash {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{{{}}}",
            self.pairs.iter()
                .map(|(_, v)| format!("{}: {}", v.key, v.value))
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
pub struct CompiledFunction {
    pub instructions: Instructions,
}

impl fmt::Display for CompiledFunction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CompiledFunction [\n{}]", MCode::new().format(&self.instructions))
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct Quote {
    pub node: MNode,
}

impl fmt::Display for Quote {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "QUOTE({})", self.node)
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Macro {
    pub params: Vec<ast::Identifier>,
    pub body: ast::BlockStatement,
    pub env: Environment,
}

impl fmt::Display for Macro {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "macro({}) {{\n{}\n}}",
            self.params
                .iter()
                .map(|p| format!("{}", p))
                .collect::<Vec<String>>()
                .join(", "),
            self.body,
        )
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum MObject {
    Int(Integer),
    Bool(Boolean),
    Str(MString),
    Array(MArray),
    Hash(MHash),
    Return(ReturnValue),
    Err(MError),
    Fn(Function),
    CompiledFn(CompiledFunction),
    Builtin(Builtin),
    Quote(Quote),
    Macro(Macro),
    Null,
}

impl fmt::Display for MObject {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MObject::Int(x) => write!(f, "{}", x),
            MObject::Bool(x) => write!(f, "{}", x),
            MObject::Str(x) => write!(f, "{}", x),
            MObject::Array(x) => write!(f, "{}", x),
            MObject::Hash(x) => write!(f, "{}", x),
            MObject::Return(x) => write!(f, "{}", x),
            MObject::Err(x) => write!(f, "{}", x),
            MObject::Fn(x) => write!(f, "{}", x),
            MObject::CompiledFn(x) => write!(f, "{}", x),
            MObject::Builtin(x) => write!(f, "{}", x),
            MObject::Quote(x) => write!(f, "{}", x),
            MObject::Macro(x) => write!(f, "{}", x),
            MObject::Null => write!(f, "null"),
        }
    }
}
