use std::{borrow::Borrow, collections::HashMap, hash::Hash};

pub trait SymbolTable<K, V>
where
    K: Eq + Hash,
{
    fn new() -> Self;
    fn find_symbol<Q: ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq;
    fn insert_symbol(&mut self, key: K, value: V) -> Option<V>;
    fn entry(&mut self);
    fn exit(&mut self);
}

impl<K, V> SymbolTable<K, V> for Vec<HashMap<K, V>>
where
    K: Eq + Hash,
{
    fn new() -> Self {
        Default::default()
    }
    fn find_symbol<Q: ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        for map in self.iter().rev() {
            if map.contains_key(key) {
                return map.get(key);
            }
        }
        None
    }
    fn insert_symbol(&mut self, key: K, value: V) -> Option<V> {
        self.last_mut().expect("not in a scope").insert(key, value)
    }
    fn entry(&mut self) {
        self.push(Default::default());
    }
    fn exit(&mut self) {
        self.pop();
    }
}
