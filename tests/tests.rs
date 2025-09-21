use list_ordered_hashmap::{Entry, OrderedHashMap};

#[test]
fn basic_insert_get_iter_remove() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    assert!(m.is_empty());

    assert_eq!(m.insert("a", 1), None);
    assert_eq!(m.insert("b", 2), None);
    assert_eq!(m.insert("c", 3), None);
    assert_eq!(m.len(), 3);

    // Order iteration
    let items: Vec<_> = m.iter().map(|(&k, &v)| (k, v)).collect();
    assert_eq!(items, vec![("a", 1), ("b", 2), ("c", 3)]);

    // get / get_mut
    assert_eq!(m.get(&"b"), Some(&2));
    *m.get_mut(&"b").unwrap() = 20;
    assert_eq!(m.get(&"b"), Some(&20));

    // replacing insert keeps position
    assert_eq!(m.insert("b", 200), Some(20));
    let items2: Vec<_> = m.iter().map(|(&k, &v)| (k, v)).collect();
    assert_eq!(items2, vec![("a", 1), ("b", 200), ("c", 3)]);

    // O(1) remove by key
    assert_eq!(m.remove(&"b"), Some(200));
    assert!(!m.contains_key(&"b"));
    let items3: Vec<_> = m.iter().map(|(&k, &v)| (k, v)).collect();
    assert_eq!(items3, vec![("a", 1), ("c", 3)]);

    // Clear
    m.clear();
    assert!(m.is_empty());
}

#[test]
fn for_each_mut_updates_values_and_preserves_order() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    m.insert("a", 1);
    m.insert("b", 2);
    m.insert("c", 3);
    let mut seen = Vec::new();
    for (k, v) in m.iter_mut() {
        seen.push(*k);
        *v += 10;
    }
    assert_eq!(seen, vec!["a", "b", "c"], "Keys visited in insertion order");
    let items: Vec<_> = m.iter().map(|(&k, &v)| (k, v)).collect();
    assert_eq!(items, vec![("a", 11), ("b", 12), ("c", 13)]);
    // Ensure a second pass still yields same order / updated values
    let items2: Vec<_> = m.iter().map(|(&k, &v)| (k, v)).collect();
    assert_eq!(items2, items);
}

#[test]
fn get_missing_value() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    m.insert("a", 1);
    m.insert("b", 2);
    // Try to get a value that isn't present
    assert_eq!(m.get(&"z"), None);
}

#[test]
fn get_mut_missing_value() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    m.insert("a", 1);
    m.insert("b", 2);
    // Try to get_mut a value that isn't present
    assert_eq!(m.get_mut(&"z"), None);
}

#[test]
fn remove_missing_value() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    m.insert("a", 1);
    m.insert("b", 2);
    // Try to remove a value that isn't present
    assert_eq!(m.remove(&"z"), None);
}

#[test]
fn entry_api_or_insert_and_or_insert_with() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    // or_insert inserts if missing
    m.entry("a").or_insert(10);
    assert_eq!(m.get(&"a"), Some(&10));
    // or_insert does not overwrite if present
    m.entry("a").or_insert(20);
    assert_eq!(m.get(&"a"), Some(&10));

    // or_insert_with
    m.entry("b").or_insert_with(|| 30);
    assert_eq!(m.get(&"b"), Some(&30));
    m.entry("b").or_insert_with(|| 40);
    assert_eq!(m.get(&"b"), Some(&30));
}

#[test]
fn entry_api_or_insert_default() {
    let mut m = OrderedHashMap::<&'static str, String>::new();
    m.entry("a").or_insert_default().push_str("foo");
    assert_eq!(m.get(&"a"), Some(&"foo".to_string()));
}

#[test]
fn entry_api_occupied_and_vacant_methods() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    // VacantEntry
    match m.entry("a") {
        Entry::Vacant(v) => {
            let vref = v.insert(123);
            assert_eq!(*vref, 123);
        }
        _ => panic!("Expected VacantEntry"),
    }
    // OccupiedEntry
    match m.entry("a") {
        Entry::Occupied(mut o) => {
            assert_eq!(*o.get(), 123);
            *o.get_mut() = 456;
            assert_eq!(*o.get(), 456);
            let (k, v) = o.remove_entry();
            assert_eq!((k, v), ("a", 456));
        }
        _ => panic!("Expected OccupiedEntry"),
    }
    assert!(m.is_empty());
}

#[test]
fn vacant_entry_key_method() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    match m.entry("z") {
        Entry::Vacant(v) => {
            assert_eq!(v.key(), &"z");
            // After checking key we can insert and ensure stored
            v.insert(9);
        }
        _ => panic!("Expected VacantEntry"),
    }
    assert_eq!(m.get(&"z"), Some(&9));
}

#[test]
fn vacant_entry_into_key() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    match m.entry("hello") {
        Entry::Vacant(v) => {
            let k = v.into_key();
            assert_eq!(k, "hello");
        }
        _ => panic!("Expected VacantEntry"),
    }
    // Map should still be empty since we never inserted.
    assert!(m.is_empty());
    assert_eq!(m.get(&"hello"), None);
}

#[test]
fn entry_api_occupied_key_and_remove() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    m.insert("a", 1);
    m.insert("b", 2);
    m.insert("c", 3);

    match m.entry("b") {
        Entry::Occupied(o) => {
            assert_eq!(o.key(), &"b");
            let val = o.remove();
            assert_eq!(val, 2);
        }
        _ => panic!("Expected OccupiedEntry"),
    }

    assert!(!m.contains_key(&"b"));
    let items: Vec<_> = m.iter().map(|(&k, &v)| (k, v)).collect();
    assert_eq!(items, vec![("a", 1), ("c", 3)]);
}

#[test]
fn reinsertion_after_removal_goes_to_end() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    m.insert("a", 1);
    m.insert("b", 2);
    m.insert("c", 3);
    assert_eq!(m.remove(&"b"), Some(2));
    // Reinsert b; should appear at end now.
    m.insert("b", 20);
    let order: Vec<_> = m.iter().map(|(&k, &v)| (k, v)).collect();
    assert_eq!(order, vec![("a", 1), ("c", 3), ("b", 20)]);
}

#[test]
fn remove_first_last_middle_sequence() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    for (k, v) in [("a", 1), ("b", 2), ("c", 3), ("d", 4), ("e", 5)] {
        m.insert(k, v);
    }
    // remove first
    assert_eq!(m.remove(&"a"), Some(1));
    // remove last (currently e)
    assert_eq!(m.remove(&"e"), Some(5));
    // remove middle (currently c)
    assert_eq!(m.remove(&"c"), Some(3));
    let remaining: Vec<_> = m.iter().map(|(&k, &v)| (k, v)).collect();
    assert_eq!(remaining, vec![("b", 2), ("d", 4)]);
}

#[test]
fn or_insert_with_runs_only_when_vacant() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    let mut calls = 0;
    m.entry("a").or_insert_with(|| {
        calls += 1;
        10
    });
    // occupied path; closure must NOT run again
    m.entry("a").or_insert_with(|| {
        calls += 1;
        99
    });
    assert_eq!(calls, 1);
    assert_eq!(m.get(&"a"), Some(&10));
}

#[test]
fn vacant_entry_inserts_clone_exactly_once() {
    use std::cell::Cell;
    use std::hash::{Hash, Hasher};
    use std::rc::Rc;

    struct CountingKey {
        name: &'static str,
        clones: Rc<Cell<usize>>,
    }
    impl Clone for CountingKey {
        fn clone(&self) -> Self {
            self.clones.set(self.clones.get() + 1);
            CountingKey {
                name: self.name,
                clones: Rc::clone(&self.clones),
            }
        }
    }
    impl PartialEq for CountingKey {
        fn eq(&self, other: &Self) -> bool {
            self.name == other.name
        }
    }
    impl Eq for CountingKey {}
    impl Hash for CountingKey {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.name.hash(state);
        }
    }
    let counter = Rc::new(Cell::new(0));
    let k = CountingKey {
        name: "alpha",
        clones: Rc::clone(&counter),
    };
    let mut m = OrderedHashMap::<CountingKey, i32>::new();
    // Insert via entry vacant path
    match m.entry(k) {
        Entry::Vacant(v) => {
            v.insert(1);
        }
        _ => unreachable!(),
    }
    // Expect exactly one clone (for storing key in list node)
    assert_eq!(counter.get(), 1);
    // Re-inserting same logical key requires constructing a new key; ensure no unexpected extra clones tracked here.
}

#[test]
fn clear_then_reuse() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    for (k, v) in [("a", 1), ("b", 2), ("c", 3)] {
        m.insert(k, v);
    }
    m.clear();
    assert!(m.is_empty());
    // reuse after clear
    m.insert("x", 9);
    m.insert("y", 8);
    let order: Vec<_> = m.iter().map(|(&k, &v)| (k, v)).collect();
    assert_eq!(order, vec![("x", 9), ("y", 8)]);
}

#[test]
fn remove_entry_direct() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    m.insert("a", 1);
    m.insert("b", 2);
    assert_eq!(m.remove_entry(&"a"), Some(("a", 1)));
    assert_eq!(m.remove_entry(&"missing"), None);
    assert_eq!(m.get(&"a"), None);
    let order: Vec<_> = m.iter().map(|(&k, &v)| (k, v)).collect();
    assert_eq!(order, vec![("b", 2)]);
}

#[test]
fn empty_iteration() {
    let m = OrderedHashMap::<&'static str, i32>::new();
    assert_eq!(m.len(), 0);
    assert!(m.is_empty());
    assert_eq!(m.iter().count(), 0);
    assert_eq!(m.keys().count(), 0);
    assert_eq!(m.values().count(), 0);
}

#[test]
fn remove_all_via_collected_keys() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    for (k, v) in [("a", 1), ("b", 2), ("c", 3), ("d", 4)] {
        m.insert(k, v);
    }
    let keys: Vec<_> = m.keys().cloned().collect();
    for k in keys {
        m.remove(&k);
    }
    assert!(m.is_empty());
    assert_eq!(m.iter().count(), 0);
}

#[test]
fn occupied_entry_mutation_keeps_position() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    for (k, v) in [("a", 1), ("b", 2), ("c", 3), ("d", 4)] {
        m.insert(k, v);
    }
    // Mutate middle element via entry occupied path
    match m.entry("b") {
        Entry::Occupied(o) => {
            *o.into_mut() = 200;
        }
        _ => unreachable!(),
    }
    let order: Vec<_> = m.iter().map(|(&k, &v)| (k, v)).collect();
    assert_eq!(order, vec![("a", 1), ("b", 200), ("c", 3), ("d", 4)]);
}

#[test]
fn len_and_iteration_consistency() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    assert_eq!(m.len(), m.iter().count());
    m.insert("a", 1);
    m.insert("b", 2);
    m.insert("c", 3);
    assert_eq!(m.len(), 3);
    assert_eq!(m.len(), m.iter().count());
    // Replace value should not change len
    m.insert("b", 20);
    assert_eq!(m.len(), 3);
    assert_eq!(m.len(), m.iter().count());
    // Remove one
    m.remove(&"a");
    assert_eq!(m.len(), 2);
    assert_eq!(m.len(), m.iter().count());
    // Clear
    m.clear();
    assert_eq!(m.len(), 0);
    assert_eq!(m.len(), m.iter().count());
}

#[test]
fn pop_front_and_back() {
    let mut m = OrderedHashMap::<&'static str, i32>::new();
    assert_eq!(m.pop_front(), None);
    assert_eq!(m.pop_back(), None);
    m.insert("a", 1);
    m.insert("b", 2);
    m.insert("c", 3);
    assert_eq!(m.pop_front(), Some(("a", 1)));
    assert_eq!(m.pop_back(), Some(("c", 3)));
    assert_eq!(m.pop_back(), Some(("b", 2)));
    assert_eq!(m.pop_front(), None);
    assert!(m.is_empty());
}

#[test]
fn shrink_to_behavior() {
    // Force the internal list to allocate a large capacity, then drastically reduce len so a shrink is meaningful.
    let mut m = OrderedHashMap::with_capacity(8);
    let total = 500usize; // large enough to grow internal storage
    for i in 0..total {
        m.insert(i, i as u32);
    }
    assert_eq!(m.len(), total);
    // Remove most elements, keep only the first KEEP items.
    let keep = 10usize;
    for i in keep..total {
        m.remove(&i).unwrap();
    }
    assert_eq!(m.len(), keep);
    // Capacity should still reflect the large allocation from before removals.
    let cap_before = m.capacity();
    assert!(
        cap_before > keep,
        "precondition: need slack capacity to test shrink (cap_before={}, keep={})",
        cap_before,
        keep
    );
    let expected: Vec<_> = (0..keep).map(|i| (i, i as u32)).collect();
    let snapshot: Vec<_> = m.iter().map(|(&k, &v)| (k, v)).collect();
    assert_eq!(
        snapshot, expected,
        "order of remaining elements before shrink incorrect"
    );

    // Perform shrink below len (request 0) => should shrink to len.
    m.shrink_to(0);
    let cap_after = m.capacity();
    assert!(cap_after >= keep);
    assert!(
        cap_after < cap_before,
        "expected actual shrink (before={}, after={})",
        cap_before,
        cap_after
    );
    assert_eq!(
        cap_after, keep,
        "order list rebuild should set capacity exactly to len"
    );
    let snapshot_after: Vec<_> = m.iter().map(|(&k, &v)| (k, v)).collect();
    assert_eq!(
        snapshot_after, expected,
        "order/value preservation after shrink"
    );

    // Requesting larger capacity with shrink_to should not grow.
    m.shrink_to(cap_before * 2);
    assert_eq!(m.capacity(), cap_after, "shrink_to must not grow capacity");

    // shrink_to_fit again is a no-op now.
    m.shrink_to_fit();
    assert_eq!(m.capacity(), cap_after);
}

// QuickCheck property: applying a sequence of operations to both the OrderedHashMap and a
// reference (Vec order + HashMap values) yields identical final ordered (k,v) list.
#[derive(Clone, Debug)]
enum Op {
    Insert(u8, u16), // key, value
    Remove(u8),      // key
    Update(u8, u16), // key, new value (simulate via entry if present)
    PopFront,
    PopBack,
}

impl quickcheck::Arbitrary for Op {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let choice = u8::arbitrary(g) % 5;
        match choice {
            0 => Op::Insert(u8::arbitrary(g), u16::arbitrary(g)),
            1 => Op::Remove(u8::arbitrary(g)),
            2 => Op::Update(u8::arbitrary(g), u16::arbitrary(g)),
            3 => Op::PopFront,
            4 => Op::PopBack,
            _ => unreachable!(),
        }
    }
}

fn sequence_preserves_order(ops: Vec<Op>) -> bool {
    use std::collections::HashMap;
    let mut m = OrderedHashMap::<u8, u16>::new();
    let mut order: Vec<u8> = Vec::new();
    let mut values: HashMap<u8, u16> = HashMap::new();

    for op in ops.into_iter() {
        match op {
            Op::Insert(k, v) => {
                let existed = values.contains_key(&k);
                let old = m.insert(k, v);
                if existed {
                    if old.is_none() {
                        return false;
                    }
                    values.insert(k, v);
                } else {
                    if old.is_some() {
                        return false;
                    }
                    values.insert(k, v);
                    order.push(k);
                }
            }
            Op::Remove(k) => {
                if values.remove(&k).is_some() {
                    let removed = m.remove(&k);
                    if removed.is_none() {
                        return false;
                    }
                    // remove from order vec
                    if let Some(pos) = order.iter().position(|&x| x == k) {
                        order.remove(pos);
                    } else {
                        return false;
                    }
                } else {
                    if m.remove(&k).is_some() {
                        return false;
                    }
                }
            }
            Op::Update(k, vnew) => {
                if let Some(cur) = values.get_mut(&k) {
                    *cur = vnew;
                    match m.entry(k) {
                        Entry::Occupied(o) => {
                            *o.into_mut() = vnew;
                        }
                        _ => return false,
                    }
                } else {
                    // updating non-existent: ensure map still doesn't contain
                    if m.get(&k).is_some() {
                        return false;
                    }
                }
            }
            Op::PopFront => {
                let model_expected = if order.is_empty() {
                    None
                } else {
                    let k = order.remove(0);
                    let v = values.remove(&k).unwrap();
                    Some((k, v))
                };
                let got = m.pop_front().map(|(k, v)| (k, v));
                if got != model_expected {
                    return false;
                }
            }
            Op::PopBack => {
                let model_expected = if order.is_empty() {
                    None
                } else {
                    let k = order.pop().unwrap();
                    let v = values.remove(&k).unwrap();
                    Some((k, v))
                };
                let got = m.pop_back().map(|(k, v)| (k, v));
                if got != model_expected {
                    return false;
                }
            }
        }
        // Invariants
        if m.len() != order.len() {
            return false;
        }
        let snapshot: Vec<_> = m.iter().map(|(&k, &v)| (k, v)).collect();
        let model: Vec<_> = order
            .iter()
            .map(|&k| (k, *values.get(&k).unwrap()))
            .collect();
        if snapshot != model {
            return false;
        }
    }
    true
}

quickcheck::quickcheck! {
    fn prop_sequence_preserves_order(ops: Vec<Op>) -> bool {
        sequence_preserves_order(ops)
    }
}
