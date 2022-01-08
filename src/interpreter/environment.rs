use std::{collections::HashMap, cell::RefCell, rc::Rc};

use crate::{
    builtin,
    object::MObject,
};

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Environment {
    store: HashMap<String, Rc<MObject>>,
    outer: Option<Rc<RefCell<Environment>>>,
    builtins: Option<Box<HashMap<String, Rc<MObject>>>>,
}

impl Environment {
    pub fn new() -> Rc<RefCell<Self>> {
        let mut builtins = HashMap::new();
        builtins.insert("len".to_string(), Rc::new(builtin::LEN));
        builtins.insert("first".to_string(), Rc::new(builtin::FIRST));
        builtins.insert("last".to_string(), Rc::new(builtin::LAST));
        builtins.insert("rest".to_string(), Rc::new(builtin::REST));
        builtins.insert("push".to_string(), Rc::new(builtin::PUSH));
        builtins.insert("puts".to_string(), Rc::new(builtin::PUTS));

        Rc::new(RefCell::new(Self { store: HashMap::new(), outer: None, builtins: Some(Box::new(builtins)) }))
    }

    pub fn enclose(env: Rc<RefCell<Environment>>) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self { store: HashMap::new(), outer: Some(env), builtins: None }))
    }

    pub fn get(&self, key: &String) -> Option<Rc<MObject>> {
        if let Some(x) = self.store.get(key) {
            Some(x.clone())
        } else if let Some(env) = &self.outer {
            env.borrow().get(key)
        } else if let Some(builtins) = &self.builtins {
            if let Some(x) = builtins.get(key) {
                Some(x.clone())
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn insert(&mut self, key: String, value: MObject) -> Option<Rc<MObject>> {
        self.store.insert(key, Rc::new(value))
    }
}

