use super::ref_path::ReferencePath;
use super::sym::SymbolTable;
use std::{borrow::Borrow, cell::RefCell, collections::HashMap, rc::Rc};

pub type SymTable<K, T> = Vec<HashMap<K, T>>;

// map name into context
#[derive(Debug, Default)]
pub struct NameContext {
    pub import_env: HashMap<String, Vec<String>>,
    pub fully_qualified_name_env: HashMap<Vec<String>, usize>,
    pub env: SymTable<String, usize>,
    pub ctor_env: Option<Rc<RefCell<HashMap<String, usize>>>>, // share with type context
}

impl NameContext {
    pub fn find_ctor(&self, key: &str) -> Option<usize> {
        let rc = self.ctor_env.as_ref().unwrap();
        rc.take().borrow().get(key).copied()
    }

    pub fn find_symbol(&self, key: &[String]) -> Option<usize> {
        if key.is_empty() {
            panic!("empty symbol name")
        }
        // name resolve order:
        // 1. local name
        // 2. constructor name
        // 3. imported external name
        // 4. external name
        if key.len() == 1 {
            return if let Some(ty) = self.env.find_symbol(key[0].as_str()) {
                Some(*ty)
            } else {
                self.ctor_env
                    .as_ref()
                    .unwrap()
                    .take()
                    .borrow()
                    .get(key[0].as_str())
                    .copied()
            };
        } else if let Some(path) = self.import_env.get(key.root()) {
            let fully_qualified_name = key.suffix().unwrap().with_prefix(path);
            if let Some(ty) = self.fully_qualified_name_env.get(&fully_qualified_name) {
                return Some(*ty);
            }
        }
        if let Some(ty) = self.fully_qualified_name_env.get(key) {
            return Some(*ty);
        }
        None
    }

    #[must_use = "check if symbol exists"]
    pub fn insert_symbol(&mut self, key: String, value: usize) -> Option<usize> {
        self.env.insert_symbol(key, value)
    }

    #[must_use = "check if symbol exists"]
    pub fn insert_fully_qualified_symbol(
        &mut self,
        key: Vec<String>,
        value: usize,
    ) -> Option<usize> {
        self.fully_qualified_name_env.insert(key, value)
    }

    pub fn entry_scope(&mut self) {
        self.env.entry();
    }

    pub fn exit_scope(&mut self) {
        self.env.exit();
    }

    pub fn resolve_import(&mut self, imports: &[&[String]]) {
        for import in imports {
            let name = import.base().clone();
            if self.import_env.contains_key(&name) {
                panic!(
                    "conflict import: {} and {}",
                    import.join("."),
                    self.import_env.get(&name).unwrap().join(".")
                )
            }
            self.import_env.insert(name, import.to_vec());
        }
    }
}
