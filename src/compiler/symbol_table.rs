use std::collections::HashMap;

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum Scope {
    Global,
    Local,
    Builtin,
    Free,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Symbol {
    name: String,
    pub scope: Scope,
    pub index: usize,
}

impl Symbol {
    fn new(name: String, scope: Scope, index: usize) -> Self {
        Self { name, scope, index }
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct SymbolTable {
    store: HashMap<String, Symbol>,
    outer: Option<Box<SymbolTable>>,
    builtins: HashMap<String, Symbol>,
    free: HashMap<String, Symbol>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            store: HashMap::new(),
            outer: None,
            builtins: HashMap::new(),
            free: HashMap::new(),
        }
    }

    pub fn enclose(outer: SymbolTable) -> Self {
        Self {
            store: HashMap::new(),
            outer: Some(Box::new(outer)),
            builtins: HashMap::new(),
            free: HashMap::new(),
        }
    }

    pub fn define(&mut self, name: String) -> &Symbol {
        let scope = if self.outer.is_none() {
            Scope::Global
        } else {
            Scope::Local
        };

        let symbol = Symbol::new(name.clone(), scope, self.store.len());
        self.store.insert(name.clone(), symbol);
        self.store.get(&name).unwrap()
    }

    pub fn define_builtin(&mut self, name: String) -> &Symbol {
        let symbol = Symbol::new(name.clone(), Scope::Builtin, self.builtins.len());
        self.builtins.insert(name.clone(), symbol);
        self.builtins.get(&name).unwrap()
    }

    pub fn resolve(&self, name: &String) -> Option<&Symbol> {
        if let Some(x) = self.store.get(name) {
            Some(x)
        } else if let Some(outer) = &self.outer {
            match outer.resolve(name)? {
                Symbol { scope: Scope::Local, .. } => None,
                x => Some(x),
            }
        } else if let Some(x) = self.builtins.get(name) {
            Some(x)
        } else {
            None
        }
    }

    pub fn define_free(&mut self, name: &String) -> Option<&Symbol> {
        if let Some(outer) = self.outer.as_deref_mut() {
            match outer.resolve(name)? {
                local @ Symbol { scope: Scope::Local, .. } => {
                    let free = Symbol::new(local.name.clone(), Scope::Free, self.free.len());
                    self.store.insert(local.name.clone(), free);
                    self.free.insert(local.name.clone(), local.clone());
                    self.store.get(&local.name)
                },
                _ => None,
            }
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

    pub fn free_symbols(&self, name: &String) -> Option<&Symbol> {
        self.free.get(name)
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
            (a.clone(), Symbol::new(a.clone(), Scope::Global, 0)),
            (b.clone(), Symbol::new(b.clone(), Scope::Global, 1)),
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

        let mut global = SymbolTable::new();
        global.define(a.clone());
        global.define(b.clone());

        let mut local = SymbolTable::enclose(global);
        local.define(c.clone());
        local.define(d.clone());

        let expected = vec![
            Symbol::new(a.clone(), Scope::Global, 0),
            Symbol::new(b.clone(), Scope::Global, 1),
            Symbol::new(c.clone(), Scope::Local, 0),
            Symbol::new(d.clone(), Scope::Local, 1),
        ];

        for sym in expected {
            let result = local.resolve(&sym.name).unwrap();

            assert_eq!(sym, *result);
        };
    }

    #[test]
    fn test_resolve_builtin() {
        let a = "a".to_string();
        let b = "b".to_string();
        let c = "c".to_string();
        let d = "d".to_string();

        let mut global = SymbolTable::new();
        global.define_builtin(a.clone());
        global.define(b.clone());
        global.define_builtin(c.clone());
        global.define_builtin(d.clone());

        let local = SymbolTable::enclose(global);
        let nested = SymbolTable::enclose(local.clone());

        let expected = vec![
            Symbol::new(a.clone(), Scope::Builtin, 0),
            Symbol::new(b.clone(), Scope::Global, 0),
            Symbol::new(c.clone(), Scope::Builtin, 1),
            Symbol::new(d.clone(), Scope::Builtin, 2),
        ];

        for sym in expected {
            let local_result = local.resolve(&sym.name).unwrap();
            let nested_result = nested.resolve(&sym.name).unwrap();

            assert_eq!(sym, *local_result);
            assert_eq!(sym, *nested_result);
        };
    }

    #[test]
    fn test_resolve_free() {
        let a = "a".to_string();
        let b = "b".to_string();
        let c = "c".to_string();
        let d = "d".to_string();
        let e = "e".to_string();
        let f = "f".to_string();

        let mut global = SymbolTable::new();
        global.define(a.clone());
        global.define(b.clone());
        let mut first_local = SymbolTable::enclose(global.clone());
        first_local.define(c.clone());
        first_local.define(d.clone());

        let mut second_local = SymbolTable::enclose(first_local.clone());
        second_local.define(e.clone());
        second_local.define(f.clone());

        let tests = vec![
            (
                &mut global,
                vec![
                    Symbol::new(a.clone(), Scope::Global, 0),
                    Symbol::new(b.clone(), Scope::Global, 1),
                ],
                vec![],
            ),
            (
                &mut first_local,
                vec![
                    Symbol::new(a.clone(), Scope::Global, 0),
                    Symbol::new(b.clone(), Scope::Global, 1),
                    Symbol::new(c.clone(), Scope::Local, 0),
                    Symbol::new(d.clone(), Scope::Local, 1),
                ],
                vec![],
            ),
            (
                &mut second_local,
                vec![
                    Symbol::new(a.clone(), Scope::Global, 0),
                    Symbol::new(b.clone(), Scope::Global, 1),
                    Symbol::new(c.clone(), Scope::Free, 0),
                    Symbol::new(d.clone(), Scope::Free, 1),
                    Symbol::new(e.clone(), Scope::Local, 0),
                    Symbol::new(f.clone(), Scope::Local, 1),
                ],
                vec![
                    Symbol::new(c.clone(), Scope::Local, 0),
                    Symbol::new(d.clone(), Scope::Local, 1),
                ],
            ),
        ];

        for tt in tests {
            for symbol in tt.1 {
                match tt.0.resolve(&symbol.name) {
                    Some(x) => assert_eq!(symbol, *x),
                    None => {
                        match tt.0.define_free(&symbol.name) {
                            Some(x) => assert_eq!(symbol, *x),
                            None => panic!("Expected: {:?}, got: None", symbol),
                        }
                    },
                }
            };
            for symbol in tt.2 {
                assert_eq!(symbol, *tt.0.free_symbols(&symbol.name).unwrap());
            };
        };
    }

    #[test]
    fn test_resolve_unresolved_free() {
        let a = "a".to_string();
        let b = "b".to_string();
        let c = "c".to_string();
        let d = "d".to_string();
        let e = "e".to_string();
        let f = "f".to_string();

        let mut global = SymbolTable::new();
        global.define(a.clone());

        let mut first_local = SymbolTable::enclose(global.clone());
        first_local.define(c.clone());

        let mut second_local = SymbolTable::enclose(first_local.clone());
        second_local.define(e.clone());
        second_local.define(f.clone());

        let tests = vec![
            Symbol::new(a.clone(), Scope::Global, 0),
            Symbol::new(c.clone(), Scope::Free, 0),
            Symbol::new(e.clone(), Scope::Local, 0),
            Symbol::new(f.clone(), Scope::Local, 1),
        ];

        for symbol in tests {
            match second_local.resolve(&symbol.name) {
                Some(x) => assert_eq!(symbol, *x),
                None => {
                    match second_local.define_free(&symbol.name) {
                        Some(x) => assert_eq!(symbol, *x),
                        None => panic!("Expected: {:?}, got: None", symbol),
                    }
                },
            }
        };

        let unresolvable = vec![
            b.clone(),
            d.clone(),
        ];

        for tt in unresolvable {
            assert!(second_local.resolve(&tt).is_none());
            assert!(second_local.define_free(&tt).is_none());
        };
    }
}
