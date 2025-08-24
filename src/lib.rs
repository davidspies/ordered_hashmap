use derive_where::derive_where;
use index_list::{Index, IndexList};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::collections::hash_map::{
    Entry as StdEntry, OccupiedEntry as StdOccupiedEntry, VacantEntry as StdVacantEntry,
};
use std::hash::Hash;
use std::mem;

/// An insertion‑ordered hash map that provides O(1) (amortized) insertion, lookup, update and
/// removal while preserving the order in which keys were first inserted.
///
/// A new key inserted with [`insert`] is appended to the logical end of the sequence. Updating an
/// existing key only changes its value; its relative position does not move. Removing a key unlinks
/// it in O(1) time. If the same key is inserted again later, it is treated as a fresh insertion and
/// appears at the end of the iteration order.
///
/// Internally the structure keeps a `HashMap<K, Index>` which maps each key to an index inside a
/// doubly‑linked list (`IndexList<(K, V)>`). The list stores the actual
/// `(K, V)` pairs plus linkage (next / prev indices) inside a single slab / arena structure. Each
/// node is just a slot within that slab; inserting a new element only grows the slab
/// vector, so there is not a separate heap allocation per entry. Removal uses the stored index to
/// unlink a node in O(1) without any traversal and without shifting other live elements. This
/// avoids both the per-node allocation overhead of a classic pointer‑based linked list and the O(n)
/// element movement costs of a simple vector when deleting from the middle.
///
/// The primary iteration methods (`iter`, `keys`, and `values`) yield items in insertion order.
/// Operations `insert`, `get`, `get_mut`, `contains_key`, and `remove` are all O(1) on average.
///
/// Debug assertions enforce two invariants: the `map` and `order` always have the same length, and
/// each stored `(K, V)` pair’s key matches the key held in the hash map entry referencing it.
///
/// The API is intentionally similar to `indexmap::IndexMap`, but this implementation relies on an
/// `IndexList` so that insertions don't typically allocate memory and removals don't cause O(n)
/// shifts.
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

    /// Iterator over (&K, &V) in insertion order.
    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.order.iter().map(|(k, v)| (k, v))
    }

    /// Returns an iterator over keys in insertion order.
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.iter().map(|(k, _)| k)
    }

    /// Returns an iterator over values in insertion order.
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.iter().map(|(_, v)| v)
    }

    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        let Self { map, order } = self;
        match map.entry(key) {
            StdEntry::Occupied(entry) => Entry::Occupied(OccupiedEntry { entry, order }),
            StdEntry::Vacant(entry) => Entry::Vacant(VacantEntry { entry, order }),
        }
    }
}

pub enum Entry<'a, K, V> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

pub struct OccupiedEntry<'a, K, V> {
    entry: StdOccupiedEntry<'a, K, Index>,
    order: &'a mut IndexList<(K, V)>,
}

pub struct VacantEntry<'a, K, V> {
    entry: StdVacantEntry<'a, K, Index>,
    order: &'a mut IndexList<(K, V)>,
}

impl<'a, K: Clone, V> Entry<'a, K, V> {
    pub fn or_insert(self, default: V) -> &'a mut V {
        self.or_insert_with(|| default)
    }

    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(occ) => occ.into_mut(),
            Entry::Vacant(vac) => vac.insert(default()),
        }
    }

    pub fn or_insert_default(self) -> &'a mut V
    where
        V: Default,
    {
        self.or_insert_with(V::default)
    }
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    pub fn key(&self) -> &K {
        self.entry.key()
    }

    pub fn get(&self) -> &V {
        let Self { entry, order } = self;
        let idx = *entry.get();
        let (_, v) = order.get(idx).unwrap();
        v
    }

    pub fn get_mut(&mut self) -> &mut V {
        let Self { entry, order } = self;
        let idx = *entry.get();
        let (_, v) = order.get_mut(idx).unwrap();
        v
    }

    pub fn into_mut(self) -> &'a mut V {
        let Self { entry, order } = self;
        let idx = *entry.get();
        let (_, v) = order.get_mut(idx).unwrap();
        v
    }

    pub fn remove_entry(self) -> (K, V) {
        let Self { entry, order } = self;
        let idx = entry.remove();
        order.remove(idx).unwrap()
    }

    pub fn remove(self) -> V {
        self.remove_entry().1
    }
}

impl<'a, K, V> VacantEntry<'a, K, V> {
    pub fn key(&self) -> &K {
        self.entry.key()
    }

    pub fn into_key(self) -> K {
        self.entry.into_key()
    }

    /// Insert a new entry into the map appended to the end.
    pub fn insert(self, value: V) -> &'a mut V
    where
        K: Clone,
    {
        let Self { entry, order } = self;
        let key = entry.key().clone();
        let idx = order.insert_last((key, value));
        entry.insert(idx);
        let (_, v) = order.get_mut(idx).unwrap();
        v
    }
}
