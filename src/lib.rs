//! [OrderedHashMap] is an insertion‑ordered hash map that provides O(1) insertion,
//! lookup, update and removal while preserving the order in which keys were first inserted.
//!
//! A new key inserted with [`insert`](OrderedHashMap::insert) is appended to the logical end of the
//! sequence. Updating an
//! existing key only changes its value; its relative position does not move. Removing a key unlinks
//! it in O(1) time. If the same key is inserted again later, it is treated as a fresh insertion and
//! appears at the end of the iteration order.
//!
//! Internally the structure keeps a [`HashMap<K, Index>`] which maps each key to an index inside a
//! doubly‑linked list [`IndexList<(K, V)>`]. The list stores the actual
//! `(K, V)` pairs plus linkage (next / prev indices) inside a single slab / arena structure. Each
//! node is just a slot within that slab; inserting a new element only grows the slab
//! vector, so there is not a separate heap allocation per entry. Removal uses the stored index to
//! unlink a node in O(1) without any traversal and without shifting other live elements. This
//! avoids both the per-node allocation overhead of a classic pointer‑based linked list and the O(n)
//! element movement costs of a simple vector when deleting from the middle.
//!
//! The primary iteration methods ([`iter`](OrderedHashMap::iter), [`keys`](OrderedHashMap::keys),
//! and [`values`](OrderedHashMap::values)) yield items in insertion order.
//! Operations `insert`, `get`, `get_mut`, `contains_key`, and `remove` are all O(1) on average.
//!
//! The API is intentionally similar to `indexmap::IndexMap`, but this implementation relies on an
//! [`IndexList`] rather than a simple [`Vec`] so that removals don't cause O(n) shifts.

use derive_where::derive_where;
use index_list::{Index, IndexList};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::Hash;
use std::mem;

pub mod entry;

pub use crate::entry::{Entry, OccupiedEntry, VacantEntry};

#[derive_where(Default)]
pub struct OrderedHashMap<K, V> {
    map: HashMap<K, Index>,
    order: IndexList<(K, V)>,
}

impl<K, V> OrderedHashMap<K, V> {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            order: IndexList::new(),
        }
    }

    pub fn len(&self) -> usize {
        let Self { map, order } = self;
        assert_eq!(map.len(), order.len());
        order.len()
    }

    pub fn is_empty(&self) -> bool {
        let Self { map, order } = self;
        assert_eq!(map.is_empty(), order.is_empty());
        order.is_empty()
    }

    /// Iterator over (&K, &V) in insertion order.
    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.order.iter().map(|(k, v)| (k, v))
    }

    pub fn for_each_mut(&mut self, mut f: impl FnMut(&K, &mut V)) {
        let mut index = self.order.first_index();
        while let Some((k, v)) = self.order.get_mut(index) {
            f(k, v);
            index = self.order.next_index(index);
        }
    }

    /// Returns an iterator over keys in insertion order.
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.iter().map(|(k, _)| k)
    }

    /// Returns an iterator over values in insertion order.
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.iter().map(|(_, v)| v)
    }
}

impl<K: Eq + Hash, V> OrderedHashMap<K, V> {
    /// Insert a key-value pair.
    /// - If the key is new: appends to the end; returns `None`.
    /// - If the key exists: replaces the value in-place; returns `Some(old_v)`.
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Clone,
    {
        match self.entry(key) {
            Entry::Occupied(occupied_entry) => {
                let old = mem::replace(occupied_entry.into_mut(), value);
                Some(old)
            }
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(value);
                None
            }
        }
    }

    pub fn get<Q: Eq + Hash + ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
    {
        let Self { map, order } = self;
        let &idx = map.get(key)?;
        let (k, v) = order.get(idx).unwrap();
        debug_assert!(*k.borrow() == *key);
        Some(v)
    }

    pub fn get_mut<Q: Eq + Hash + ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
    {
        let Self { map, order } = self;
        let &idx = map.get(key)?;
        let (k, v) = order.get_mut(idx).unwrap();
        debug_assert!(*(*k).borrow() == *key);
        Some(v)
    }

    pub fn contains_key<Q: Eq + Hash + ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
    {
        self.map.contains_key(key)
    }

    /// Removes `key` if present and returns its value, in O(1).
    pub fn remove<Q: Eq + Hash + ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
    {
        self.remove_entry(key).map(|(_, v)| v)
    }

    pub fn remove_entry<Q: Eq + Hash + ?Sized>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
    {
        let Self { map, order } = self;
        let idx = map.remove(key)?;
        let (k_stored, v) = order.remove(idx).unwrap();
        debug_assert!(*k_stored.borrow() == *key);
        Some((k_stored, v))
    }

    pub fn pop_front(&mut self) -> Option<(K, V)> {
        let Self { map, order } = self;
        let (k, v) = order.remove_first()?;
        map.remove(&k).unwrap();
        Some((k, v))
    }

    pub fn pop_back(&mut self) -> Option<(K, V)> {
        let Self { map, order } = self;
        let (k, v) = order.remove_last()?;
        map.remove(&k).unwrap();
        Some((k, v))
    }

    pub fn clear(&mut self) {
        let Self { map, order } = self;
        map.clear();
        order.clear();
    }

    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        let Self { map, order } = self;
        let std_entry = map.entry(key);
        Entry::new(std_entry, order)
    }
}
