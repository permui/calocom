use std::{borrow::Borrow, collections::HashMap, hash::Hash};

pub trait SymbolTable<K, V>
where
    K: Eq + Hash,
{
    fn find_symbol<Q: ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq;
    fn find_symbol_and_level<Q: ?Sized>(&self, key: &Q) -> (isize, Option<&V>)
    where
        K: Borrow<Q>,
        Q: Hash + Eq;
    fn insert_symbol(&mut self, key: K, value: V) -> Option<V>;
    fn entry(&mut self) -> isize;
    fn exit(&mut self) -> isize;
    fn level(&self) -> isize;
}

impl<K, V> SymbolTable<K, V> for Vec<HashMap<K, V>>
where
    K: Eq + Hash,
{
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
    fn find_symbol_and_level<Q: ?Sized>(&self, key: &Q) -> (isize, Option<&V>)
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        for (idx, map) in self.iter().enumerate().rev() {
            if map.contains_key(key) {
                return (idx as isize, map.get(key));
            }
        }
        (-1, None)
    }
    fn insert_symbol(&mut self, key: K, value: V) -> Option<V> {
        self.last_mut().expect("not in a scope").insert(key, value)
    }
    fn entry(&mut self) -> isize {
        self.push(Default::default());
        self.level()
    }
    fn exit(&mut self) -> isize {
        self.pop();
        self.level()
    }
    fn level(&self) -> isize {
        self.len() as isize - 1
    }
}
