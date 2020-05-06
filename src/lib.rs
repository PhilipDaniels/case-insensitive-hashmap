use std::collections::HashMap;
use std::{hash::BuildHasher, collections::hash_map::{Entry, Drain, RandomState, Iter, IterMut, Keys, Values, ValuesMut}};
use unicase::UniCase;


#[derive(Debug, Default, Clone)]
pub struct CiHashMap<V, S = RandomState>
where S: BuildHasher
{
    inner: HashMap<UniCase<String>, V, S>,
}

impl<V, S> CiHashMap<V, S>
where S: BuildHasher + Default
{
    pub fn new() -> Self
    where S: Default
    {
        Self {
            inner: Default::default(),
        }
    }

    pub fn with_capacity(capacity: usize) -> CiHashMap<V, S> {
        Self::with_capacity_and_hasher(capacity, S::default())
    }

    pub fn with_hasher(hash_builder: S) -> Self {
        Self::with_capacity_and_hasher(0, hash_builder)
    }

    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> CiHashMap<V, S> {
        Self {
            inner: HashMap::<UniCase<String>, V, S>::with_capacity_and_hasher(capacity, hash_builder)
        }
    }

    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    pub fn clear(&mut self) {
        self.inner.clear();
    }

    pub fn contains_key<Q: Into<UniCase<String>>>(&self, k: Q) -> bool {
        let key = k.into();
        self.inner.contains_key(&key)
    }

    pub fn drain(&mut self) -> Drain<UniCase<String>, V> {
        self.inner.drain()
    }

    pub fn entry<Q: Into<UniCase<String>>>(&mut self, k: Q) -> Entry<UniCase<String>, V> {
        let key = k.into();
        self.inner.entry(key)
    }

    pub fn get<Q: Into<UniCase<String>>>(&self, k: Q) -> Option<&V> {
        let key = k.into();
        self.inner.get(&key)
    }

    pub fn get_key_value<Q: Into<UniCase<String>>>(&self, k: Q) -> Option<(&UniCase<String>, &V)> {
        let key = k.into();
        self.inner.get_key_value(&key)
    }

    pub fn get_mut<Q: Into<UniCase<String>>>(&mut self, k: Q) -> Option<&mut V> {
        let key = k.into();
        self.inner.get_mut(&key)
    }

    pub fn hasher(&self) -> &S {
        self.inner.hasher()
    }

    pub fn insert<K: Into<UniCase<String>>>(&mut self, k: K, v: V) -> Option<V> {
        let key = k.into();
        self.inner.insert(key, v)
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn iter(&self) -> Iter<UniCase<String>, V> {
        self.inner.iter()
    }

    pub fn iter_mut(&mut self) -> IterMut<UniCase<String>, V> {
        self.inner.iter_mut()
    }

    pub fn keys(&self) -> Keys<UniCase<String>, V> {
        self.inner.keys()
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn remove<K: Into<UniCase<String>>>(&mut self, k: K) -> Option<V> {
        let key = k.into();
        self.inner.remove(&key)
    }

    pub fn remove_entry<K: Into<UniCase<String>>>(&mut self, k: K) -> Option<(UniCase<String>, V)> {
        let key = k.into();
        self.inner.remove_entry(&key)
    }

    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional);
    }

    pub fn retain<F>(&mut self, f: F)
    where F: FnMut(&UniCase<String>, &mut V) -> bool {
        self.inner.retain(f);
    }

    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit();
    }

    pub fn values(&self) -> Values<UniCase<String>, V> {
        self.inner.values()
    }

    pub fn values_mut(&mut self) -> ValuesMut<UniCase<String>, V> {
        self.inner.values_mut()
    }


}

#[cfg(test)]
mod tests {
    use super::CiHashMap;

    #[test]
    fn new() {
        let map = CiHashMap::<u8>::new();
        assert_eq!(map.len(), 0);
    }

    #[test]
    fn clear() {
        let mut map = CiHashMap::<u8>::new();
        assert_eq!(map.len(), 0);
        map.insert("A", 1);
        assert_eq!(map.len(), 1);
        map.clear();
        assert_eq!(map.len(), 0);
    }

    #[test]
    fn contains_key_str() {
        let mut map = CiHashMap::<u8>::new();
        map.insert("A", 1);
        assert!(map.contains_key("A"));
        assert!(map.contains_key("a"));
        assert!(!map.contains_key("B"));
        assert!(!map.contains_key("Å"));
    }

    #[test]
    fn contains_key_string() {
        let mut map = CiHashMap::<u8>::new();
        map.insert("A", 1);
        assert!(map.contains_key("A".to_string()));
        assert!(map.contains_key("a".to_string()));
        assert!(!map.contains_key("B".to_string()));
        assert!(!map.contains_key("Å".to_string()));
    }

    #[test]
    fn get_str() {
        let mut map = CiHashMap::<u8>::new();
        map.insert("A", 1);
        assert_eq!(map.get("A").unwrap(), &1);
        assert_eq!(map.get("a").unwrap(), &1);
        assert!(map.get("B").is_none());
    }

    #[test]
    fn insert_str() {
        let mut map = CiHashMap::<u8>::new();
        map.insert("A", 1);
        map.insert("B", 2);
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn insert_string() {
        let mut map = CiHashMap::<u8>::new();
        map.insert("A".to_string(), 1);
        map.insert("B".to_string(), 2);
        assert_eq!(map.len(), 2);
    }

    // #[test]
    // fn insert_string_ref() {
    //     let mut map = CiHashMap::<u8>::new();
    //     map.insert(&("A".to_string()), 0);
    //     map.insert(&("B".to_string()), 0);
    //     assert_eq!(map.len(), 2);
    // }
}
