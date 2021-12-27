use std::collections::HashMap;

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
enum Scope {
    Global,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Symbol {
    name: String,
    scope: Scope,
    pub index: usize,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct SymbolTable {
    store: HashMap<String, Symbol>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            store: HashMap::new(),
        }
    }

    pub fn define(&mut self, name: String) -> usize {
        let index = self.store.len();

        let symbol = Symbol {
            name: name.clone(),
            scope: Scope::Global,
            index,
        };

        self.store.insert(name, symbol);

        index
    }

    pub fn resolve(&self, name: &String) -> Option<&Symbol> {
        self.store.get(name)
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

        assert_eq!(0, global.define(a.clone()));
        assert_eq!(expected[&a], *global.resolve(&a).unwrap());

        assert_eq!(1, global.define(b.clone()));
        assert_eq!(expected[&b], *global.resolve(&b).unwrap());
    }
}
