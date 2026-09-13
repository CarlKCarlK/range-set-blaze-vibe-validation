#![feature(btree_cursors)]

//! Executable semantics for the ordered-map fragment used by RangeSetBlaze.
//!
//! The contract deliberately returns cloned observations. Borrowing, lifetimes,
//! allocation, balancing, and complexity are not part of the model.

use std::collections::BTreeMap;
use std::ops::Bound;

/// Read-only observations available at a gap in increasing key order.
pub trait SemanticCursor<K, V> {
    fn peek_prev(&self) -> Option<(K, V)>;
    fn peek_next(&self) -> Option<(K, V)>;
}

/// Mutations used by the cursor-shaped RangeSetBlaze algorithms.
pub trait SemanticCursorMut<K, V> {
    fn peek_prev(&mut self) -> Option<(K, V)>;
    fn peek_next(&mut self) -> Option<(K, V)>;
    fn set_prev_value(&mut self, value: V) -> bool;
    fn remove_next(&mut self) -> Option<(K, V)>;

    /// Insert immediately before the current next entry.
    ///
    /// The caller must supply a key strictly between the adjacent keys. On
    /// return the cursor gap is after the inserted entry.
    fn insert_before(&mut self, key: K, value: V);
}

/// The implementation-independent ordered-map operations used by the proofs.
pub trait SemanticOrderedMap<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    type Cursor<'a>: SemanticCursor<K, V>
    where
        Self: 'a,
        K: 'a,
        V: 'a;

    type CursorMut<'a>: SemanticCursorMut<K, V>
    where
        Self: 'a,
        K: 'a,
        V: 'a;

    fn ordered_entries(&self) -> Vec<(K, V)>;
    fn predecessor_le(&self, key: &K) -> Option<(K, V)>;
    fn predecessor_lt(&self, key: &K) -> Option<(K, V)>;
    fn successor_ge(&self, key: &K) -> Option<(K, V)>;
    fn predecessors_le_descending(&mut self, key: &K) -> Vec<(K, V)>;
    fn successors_ge_ascending(&mut self, key: &K) -> Vec<(K, V)>;
    fn insert(&mut self, key: K, value: V) -> Option<V>;
    fn remove(&mut self, key: &K) -> Option<V>;
    fn set_predecessor_value(&mut self, key: &K, value: V) -> Option<(K, V)>;
    fn set_successor_value(&mut self, key: &K, value: V) -> Option<(K, V)>;
    fn lower_bound(&self, key: &K) -> Self::Cursor<'_>;
    fn lower_bound_mut(&mut self, key: &K) -> Self::CursorMut<'_>;
}

/// Auditable reference implementation: strictly sorted, unique `(key, value)` pairs.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct VecOrderedMap<K, V> {
    entries: Vec<(K, V)>,
}

impl<K: Ord, V> VecOrderedMap<K, V> {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    pub fn from_entries(entries: impl IntoIterator<Item = (K, V)>) -> Self {
        let mut map = Self::new();
        for (key, value) in entries {
            match map.entries.binary_search_by(|(stored, _)| stored.cmp(&key)) {
                Ok(index) => map.entries[index].1 = value,
                Err(index) => map.entries.insert(index, (key, value)),
            }
        }
        map
    }

    fn lower_bound_index(&self, key: &K) -> usize {
        self.entries.partition_point(|(stored, _)| stored < key)
    }
}

pub struct VecCursor<'a, K, V> {
    entries: &'a [(K, V)],
    gap: usize,
}

impl<K: Clone, V: Clone> SemanticCursor<K, V> for VecCursor<'_, K, V> {
    fn peek_prev(&self) -> Option<(K, V)> {
        self.gap
            .checked_sub(1)
            .map(|index| self.entries[index].clone())
    }

    fn peek_next(&self) -> Option<(K, V)> {
        self.entries.get(self.gap).cloned()
    }
}

pub struct VecCursorMut<'a, K, V> {
    entries: &'a mut Vec<(K, V)>,
    gap: usize,
}

impl<K: Ord + Clone, V: Clone> SemanticCursorMut<K, V> for VecCursorMut<'_, K, V> {
    fn peek_prev(&mut self) -> Option<(K, V)> {
        self.gap
            .checked_sub(1)
            .map(|index| self.entries[index].clone())
    }

    fn peek_next(&mut self) -> Option<(K, V)> {
        self.entries.get(self.gap).cloned()
    }

    fn set_prev_value(&mut self, value: V) -> bool {
        let Some(index) = self.gap.checked_sub(1) else {
            return false;
        };
        self.entries[index].1 = value;
        true
    }

    fn remove_next(&mut self) -> Option<(K, V)> {
        (self.gap < self.entries.len()).then(|| self.entries.remove(self.gap))
    }

    fn insert_before(&mut self, key: K, value: V) {
        let after_previous = self.gap == 0 || self.entries[self.gap - 1].0 < key;
        let before_next = self.gap == self.entries.len() || key < self.entries[self.gap].0;
        assert!(
            after_previous && before_next,
            "key does not belong at cursor gap"
        );
        self.entries.insert(self.gap, (key, value));
        self.gap += 1;
    }
}

impl<K, V> SemanticOrderedMap<K, V> for VecOrderedMap<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    type Cursor<'a>
        = VecCursor<'a, K, V>
    where
        K: 'a,
        V: 'a;
    type CursorMut<'a>
        = VecCursorMut<'a, K, V>
    where
        K: 'a,
        V: 'a;

    fn ordered_entries(&self) -> Vec<(K, V)> {
        self.entries.clone()
    }

    fn predecessor_le(&self, key: &K) -> Option<(K, V)> {
        let index = self.entries.partition_point(|(stored, _)| stored <= key);
        index
            .checked_sub(1)
            .map(|index| self.entries[index].clone())
    }

    fn predecessor_lt(&self, key: &K) -> Option<(K, V)> {
        self.lower_bound_index(key)
            .checked_sub(1)
            .map(|index| self.entries[index].clone())
    }

    fn successor_ge(&self, key: &K) -> Option<(K, V)> {
        self.entries.get(self.lower_bound_index(key)).cloned()
    }

    fn predecessors_le_descending(&mut self, key: &K) -> Vec<(K, V)> {
        self.entries
            .iter()
            .rev()
            .filter(|(stored, _)| stored <= key)
            .cloned()
            .collect()
    }

    fn successors_ge_ascending(&mut self, key: &K) -> Vec<(K, V)> {
        self.entries
            .iter()
            .filter(|(stored, _)| stored >= key)
            .cloned()
            .collect()
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self
            .entries
            .binary_search_by(|(stored, _)| stored.cmp(&key))
        {
            Ok(index) => Some(std::mem::replace(&mut self.entries[index].1, value)),
            Err(index) => {
                self.entries.insert(index, (key, value));
                None
            }
        }
    }

    fn remove(&mut self, key: &K) -> Option<V> {
        self.entries
            .binary_search_by(|(stored, _)| stored.cmp(key))
            .ok()
            .map(|index| self.entries.remove(index).1)
    }

    fn set_predecessor_value(&mut self, key: &K, value: V) -> Option<(K, V)> {
        let index = self
            .entries
            .partition_point(|(stored, _)| stored <= key)
            .checked_sub(1)?;
        let old = self.entries[index].clone();
        self.entries[index].1 = value;
        Some(old)
    }

    fn set_successor_value(&mut self, key: &K, value: V) -> Option<(K, V)> {
        let index = self.lower_bound_index(key);
        let old = self.entries.get(index)?.clone();
        self.entries[index].1 = value;
        Some(old)
    }

    fn lower_bound(&self, key: &K) -> Self::Cursor<'_> {
        VecCursor {
            entries: &self.entries,
            gap: self.lower_bound_index(key),
        }
    }

    fn lower_bound_mut(&mut self, key: &K) -> Self::CursorMut<'_> {
        let gap = self.lower_bound_index(key);
        VecCursorMut {
            entries: &mut self.entries,
            gap,
        }
    }
}

/// Thin adapter that exercises `std::collections::BTreeMap` directly.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BTreeMapAdapter<K, V> {
    map: BTreeMap<K, V>,
}

impl<K: Ord, V> BTreeMapAdapter<K, V> {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }

    pub fn from_entries(entries: impl IntoIterator<Item = (K, V)>) -> Self {
        Self {
            map: entries.into_iter().collect(),
        }
    }
}

pub struct BTreeCursor<'a, K, V> {
    cursor: std::collections::btree_map::Cursor<'a, K, V>,
}

impl<K: Clone, V: Clone> SemanticCursor<K, V> for BTreeCursor<'_, K, V> {
    fn peek_prev(&self) -> Option<(K, V)> {
        self.cursor
            .peek_prev()
            .map(|(key, value)| (key.clone(), value.clone()))
    }

    fn peek_next(&self) -> Option<(K, V)> {
        self.cursor
            .peek_next()
            .map(|(key, value)| (key.clone(), value.clone()))
    }
}

pub struct BTreeCursorMut<'a, K, V> {
    cursor: std::collections::btree_map::CursorMut<'a, K, V>,
}

impl<K: Ord + Clone, V: Clone> SemanticCursorMut<K, V> for BTreeCursorMut<'_, K, V> {
    fn peek_prev(&mut self) -> Option<(K, V)> {
        self.cursor
            .peek_prev()
            .map(|(key, value)| (key.clone(), value.clone()))
    }

    fn peek_next(&mut self) -> Option<(K, V)> {
        self.cursor
            .peek_next()
            .map(|(key, value)| (key.clone(), value.clone()))
    }

    fn set_prev_value(&mut self, value: V) -> bool {
        let Some((_, stored)) = self.cursor.peek_prev() else {
            return false;
        };
        *stored = value;
        true
    }

    fn remove_next(&mut self) -> Option<(K, V)> {
        self.cursor.remove_next()
    }

    fn insert_before(&mut self, key: K, value: V) {
        self.cursor
            .insert_before(key, value)
            .expect("key does not belong at cursor gap");
    }
}

impl<K, V> SemanticOrderedMap<K, V> for BTreeMapAdapter<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    type Cursor<'a>
        = BTreeCursor<'a, K, V>
    where
        K: 'a,
        V: 'a;
    type CursorMut<'a>
        = BTreeCursorMut<'a, K, V>
    where
        K: 'a,
        V: 'a;

    fn ordered_entries(&self) -> Vec<(K, V)> {
        self.map
            .iter()
            .map(|(key, value)| (key.clone(), value.clone()))
            .collect()
    }

    fn predecessor_le(&self, key: &K) -> Option<(K, V)> {
        self.map.range(..=key).next_back().map(clone_entry)
    }

    fn predecessor_lt(&self, key: &K) -> Option<(K, V)> {
        self.map.range(..key).next_back().map(clone_entry)
    }

    fn successor_ge(&self, key: &K) -> Option<(K, V)> {
        self.map.range(key..).next().map(clone_entry)
    }

    fn predecessors_le_descending(&mut self, key: &K) -> Vec<(K, V)> {
        self.map
            .range_mut(..=key)
            .rev()
            .map(clone_mut_entry)
            .collect()
    }

    fn successors_ge_ascending(&mut self, key: &K) -> Vec<(K, V)> {
        self.map.range_mut(key..).map(clone_mut_entry).collect()
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.map.insert(key, value)
    }

    fn remove(&mut self, key: &K) -> Option<V> {
        self.map.remove(key)
    }

    fn set_predecessor_value(&mut self, key: &K, value: V) -> Option<(K, V)> {
        let (stored_key, stored_value) = self.map.range_mut(..=key).next_back()?;
        let old = (stored_key.clone(), stored_value.clone());
        *stored_value = value;
        Some(old)
    }

    fn set_successor_value(&mut self, key: &K, value: V) -> Option<(K, V)> {
        let (stored_key, stored_value) = self.map.range_mut(key..).next()?;
        let old = (stored_key.clone(), stored_value.clone());
        *stored_value = value;
        Some(old)
    }

    fn lower_bound(&self, key: &K) -> Self::Cursor<'_> {
        BTreeCursor {
            cursor: self.map.lower_bound(Bound::Included(key)),
        }
    }

    fn lower_bound_mut(&mut self, key: &K) -> Self::CursorMut<'_> {
        BTreeCursorMut {
            cursor: self.map.lower_bound_mut(Bound::Included(key)),
        }
    }
}

fn clone_entry<K: Clone, V: Clone>((key, value): (&K, &V)) -> (K, V) {
    (key.clone(), value.clone())
}

fn clone_mut_entry<K: Clone, V: Clone>((key, value): (&K, &mut V)) -> (K, V) {
    (key.clone(), value.clone())
}
