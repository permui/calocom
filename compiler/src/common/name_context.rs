use super::ref_path::ReferencePath;
use super::sym::SymbolTable;
use std::fmt::Debug;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

type SymTable<K, T> = Vec<HashMap<K, T>>;

// map name into context
#[derive(Debug, Clone)]
pub struct NameContext<T> {
    pub import_env: HashMap<String, Vec<String>>,
    pub fully_qualified_name_env: HashMap<Vec<String>, T>,
    pub env: SymTable<String, T>,
    pub ctor_env: Option<Rc<RefCell<HashMap<String, T>>>>, // share with type context
    pub delimiter: Vec<isize>, // the start symbol depth stack of a lambda expression
}

impl<T> Default for NameContext<T> {
    fn default() -> Self {
        Self {
            import_env: Default::default(),
            fully_qualified_name_env: Default::default(),
            env: Default::default(),
            ctor_env: Default::default(),
            delimiter: vec![-1],
        }
    }
}

impl<T> NameContext<T>
where
    T: Clone + Debug,
{
    pub fn inherit_environment(self) -> Self {
        Self {
            import_env: self.import_env,
            fully_qualified_name_env: self.fully_qualified_name_env,
            env: Default::default(),
            ctor_env: self.ctor_env,
            delimiter: vec![-1],
        }
    }

    pub fn start_delimiter(&mut self, level: isize) {
        self.delimiter.push(level)
    }

    pub fn end_delimiter(&mut self) -> Option<isize> {
        self.delimiter.pop()
    }

    pub fn find_capture_depth_by_level(&self, level: isize) -> usize {
        for (index, delimiter) in self.delimiter.iter().rev().enumerate() {
            if level >= *delimiter {
                return index;
            }
        }
        dbg!(&self.delimiter);
        panic!("no delimiter found")
    }

    pub fn find_ctor(&self, key: &str) -> Option<T> {
        let rc = self.ctor_env.as_ref().unwrap();
        rc.as_ref().borrow().get(key).cloned()
    }

    pub fn get_full_symbol_path(&self, key: &[String]) -> Vec<String> {
        if key.len() == 1 {
            return if self.env.find_symbol(key[0].as_str()).is_some() {
                vec![key[0].to_string()]
            } else if let Some(ctor_env) = self.ctor_env.as_ref() {
                ctor_env
                    .as_ref()
                    .borrow()
                    .get(key[0].as_str())
                    .map_or_else(Vec::new, |_| vec![key[0].to_string()])
            } else {
                vec![]
            };
        } else if let Some(path) = self.import_env.get(key.root()) {
            let fully_qualified_name = key.suffix().unwrap().with_prefix(path);
            if self
                .fully_qualified_name_env
                .get(&fully_qualified_name)
                .is_some()
            {
                return fully_qualified_name;
            }
        }
        if self.fully_qualified_name_env.get(key).is_some() {
            return key.to_vec();
        }
        vec![]
    }

    pub fn find_symbol(&self, key: &[String]) -> Option<T> {
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
                Some(ty.clone())
            } else if let Some(ctor_env) = self.ctor_env.as_ref() {
                ctor_env.as_ref().borrow().get(key[0].as_str()).cloned()
            } else {
                None
            };
        } else if let Some(path) = self.import_env.get(key.root()) {
            let fully_qualified_name = key.suffix().unwrap().with_prefix(path);
            if let Some(ty) = self.fully_qualified_name_env.get(&fully_qualified_name) {
                return Some(ty.clone());
            }
        }
        if let Some(ty) = self.fully_qualified_name_env.get(key) {
            return Some(ty.clone());
        }
        None
    }

    pub fn find_symbol_and_level(&self, key: &[String]) -> (isize, Option<T>) {
        if key.is_empty() {
            panic!("empty symbol name")
        }
        // name resolve order:
        // 1. local name
        // 2. constructor name
        // 3. imported external name
        // 4. external name
        if key.len() == 1 {
            return if let (level, Some(ty)) = self.env.find_symbol_and_level(key[0].as_str()) {
                (level, Some(ty.clone()))
            } else {
                (
                    -1,
                    self.ctor_env
                        .as_ref()
                        .unwrap()
                        .as_ref()
                        .borrow()
                        .get(key[0].as_str())
                        .cloned(),
                )
            };
        } else if let Some(path) = self.import_env.get(key.root()) {
            let fully_qualified_name = key.suffix().unwrap().with_prefix(path);
            if let Some(ty) = self.fully_qualified_name_env.get(&fully_qualified_name) {
                return (-1, Some(ty.clone()));
            }
        }
        if let Some(ty) = self.fully_qualified_name_env.get(key) {
            return (-1, Some(ty.clone()));
        }
        (-1, None)
    }

    #[must_use = "check if symbol exists"]
    pub fn insert_symbol(&mut self, key: String, value: T) -> Option<T> {
        self.env.insert_symbol(key, value)
    }

    #[must_use = "check if symbol exists"]
    pub fn insert_fully_qualified_symbol(&mut self, key: Vec<String>, value: T) -> Option<T> {
        self.fully_qualified_name_env.insert(key, value)
    }

    pub fn entry_scope(&mut self) -> isize {
        self.env.entry()
    }

    pub fn exit_scope(&mut self) -> isize {
        self.env.exit()
    }

    pub fn scope_level(&self) -> isize {
        self.env.level()
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
