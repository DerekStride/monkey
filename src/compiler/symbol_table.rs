use std::collections::HashMap;

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum Scope {
    Global,
    Local,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Symbol {
    name: String,
    pub scope: Scope,
    pub index: usize,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct SymbolTable {
    store: HashMap<String, Symbol>,
    outer: Option<Box<SymbolTable>>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            store: HashMap::new(),
            outer: None,
        }
    }

    pub fn enclose(outer: SymbolTable) -> Self {
        Self {
            store: HashMap::new(),
            outer: Some(Box::new(outer)),
        }
    }

    pub fn define(&mut self, name: String) -> &Symbol {
        let index = self.store.len();

        let scope = if self.outer.is_none() {
            Scope::Global
        } else {
            Scope::Local
        };

        let symbol = Symbol {
            name: name.clone(),
            scope,
            index,
        };

        self.store.insert(name.clone(), symbol);

        self.store.get(&name).unwrap()
    }

    pub fn resolve(&self, name: &String) -> Option<&Symbol> {
        if let Some(x) = self.store.get(name) {
            Some(x)
        } else if let Some(outer) = &self.outer {
            outer.resolve(name)
        } else {
            None
        }
    }

    pub fn outer(&mut self) -> Option<Self> {
        if let Some(outer) = self.outer.take() {
            Some(*outer)
        } else {
            None
        }
    }

    pub fn len(&self) -> u8 {
        self.store.len() as u8
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_define_and_resolve() {
        let a = "a".to_string();
        let b = "b".to_string();
        let expected = HashMap::from([
            (a.clone(), Symbol { name: a.clone(), scope: Scope::Global, index: 0 }),
            (b.clone(), Symbol { name: b.clone(), scope: Scope::Global, index: 1 }),
        ]);

        let mut global = SymbolTable::new();

        assert_eq!(0, global.define(a.clone()).index);
        assert_eq!(expected[&a], *global.resolve(&a).unwrap());

        assert_eq!(1, global.define(b.clone()).index);
        assert_eq!(expected[&b], *global.resolve(&b).unwrap());
    }

    #[test]
    fn test_resolve_local() {
        let a = "a".to_string();
        let b = "b".to_string();
        let c = "c".to_string();
        let d = "d".to_string();
        let e = "e".to_string();
        let f = "f".to_string();

        let mut global = SymbolTable::new();
        global.define(a.clone());
        global.define(b.clone());

        let mut local = SymbolTable::enclose(global);
        local.define(c.clone());
        local.define(d.clone());

        let mut nested = SymbolTable::enclose(local);
        nested.define(e.clone());
        nested.define(f.clone());

        let expected = vec![
            Symbol {name: a.clone(), scope: Scope::Global, index: 0 },
            Symbol {name: b.clone(), scope: Scope::Global, index: 1 },
            Symbol {name: c.clone(), scope: Scope::Local, index: 0 },
            Symbol {name: d.clone(), scope: Scope::Local, index: 1 },
            Symbol {name: e.clone(), scope: Scope::Local, index: 0 },
            Symbol {name: f.clone(), scope: Scope::Local, index: 1 },
        ];

        for sym in expected {
            let result = nested.resolve(&sym.name).unwrap();

            assert_eq!(sym, *result);
        };
    }
}
