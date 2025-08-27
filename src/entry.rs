use index_list::{Index, IndexList};
use std::collections::hash_map::{
    Entry as StdEntry, OccupiedEntry as StdOccupiedEntry, VacantEntry as StdVacantEntry,
};

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

impl<'a, K, V> Entry<'a, K, V> {
    pub(crate) fn new(entry: StdEntry<'a, K, Index>, order: &'a mut IndexList<(K, V)>) -> Self {
        match entry {
            StdEntry::Occupied(entry) => Entry::Occupied(OccupiedEntry { entry, order }),
            StdEntry::Vacant(entry) => Entry::Vacant(VacantEntry { entry, order }),
        }
    }
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
