use std::collections::HashMap;

use crate::interpreter::{
    builtin,
    object::MObject,
};

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Environment {
    store: HashMap<String, MObject>,
    outer: Option<Box<Environment>>,
    builtins: Option<Box<HashMap<String, MObject>>>,
}

impl Environment {
    pub fn new() -> Self {
        let mut builtins = HashMap::new();
        builtins.insert("len".to_string(), builtin::LEN);
        builtins.insert("first".to_string(), builtin::FIRST);
        builtins.insert("last".to_string(), builtin::LAST);
        builtins.insert("rest".to_string(), builtin::REST);
        builtins.insert("push".to_string(), builtin::PUSH);

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

