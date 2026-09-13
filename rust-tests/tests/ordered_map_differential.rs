use ordered_map::{Cursor, CursorMut, OrderedMap, VecOrderedMap};
use std::cmp::Ordering;
use std::collections::BTreeMap;

type Reference = VecOrderedMap<i32, i32>;
type Adapter = BTreeMap<i32, i32>;

#[derive(Clone, Debug)]
struct TaggedKey {
    order: i32,
    tag: &'static str,
}

impl PartialEq for TaggedKey {
    fn eq(&self, other: &Self) -> bool {
        self.order == other.order
    }
}

impl Eq for TaggedKey {}

impl PartialOrd for TaggedKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TaggedKey {
    fn cmp(&self, other: &Self) -> Ordering {
        self.order.cmp(&other.order)
    }
}

fn maps(entries: impl IntoIterator<Item = (i32, i32)> + Clone) -> (Reference, Adapter) {
    (
        Reference::from_entries(entries.clone()),
        entries.into_iter().collect(),
    )
}

fn assert_same(reference: &Reference, adapter: &Adapter) {
    assert_eq!(reference.ordered_entries(), adapter.ordered_entries());
}

// `BTreeMap::lower_bound[_mut]` and `btree_map::Cursor[Mut]::peek_prev`/
// `peek_next`/`insert_before` are also *inherent* methods on those
// standard-library types, with different signatures than the `OrderedMap`/
// `Cursor`/`CursorMut` trait methods of the same name (see the crate docs).
// Inherent methods shadow trait methods in method-call syntax, so exercising
// them on a concrete `Adapter` value requires going through a function
// that is generic over the trait, as done below, rather than calling them
// directly on `adapter`.

type Gap = Option<(i32, i32)>;

fn gap_observations<M: OrderedMap<i32, i32>>(m: &M, key: &i32) -> (Gap, Gap) {
    let cursor = m.lower_bound(key);
    (cursor.peek_prev(), cursor.peek_next())
}

type CursorSessionA = (Gap, Gap, Gap);

fn cursor_session_peek_then_remove_next<M: OrderedMap<i32, i32>>(
    m: &mut M,
    start: &i32,
) -> CursorSessionA {
    let mut cursor = m.lower_bound_mut(start);
    let prev = cursor.peek_prev();
    let next = cursor.peek_next();
    let removed = cursor.remove_next();
    (prev, next, removed)
}

type CursorSessionB = (Gap, Gap, bool, Gap, Gap, Gap, Gap);

fn cursor_session_set_prev_then_remove_next<M: OrderedMap<i32, i32>>(
    m: &mut M,
    start: &i32,
) -> CursorSessionB {
    let mut cursor = m.lower_bound_mut(start);
    let prev1 = cursor.peek_prev();
    let next1 = cursor.peek_next();
    let did_set = cursor.set_prev_value(101);
    let prev2 = cursor.peek_prev();
    let removed = cursor.remove_next();
    let prev3 = cursor.peek_prev();
    let next3 = cursor.peek_next();
    (prev1, next1, did_set, prev2, removed, prev3, next3)
}

fn cursor_session_insert_before<M: OrderedMap<i32, i32>>(
    m: &mut M,
    start: i32,
    inserted: i32,
) -> (Gap, Gap, Gap) {
    let mut cursor = m.lower_bound_mut(&start);
    let old_next = cursor.peek_next();
    cursor.insert_before(inserted, 99);
    (old_next, cursor.peek_prev(), cursor.peek_next())
}

fn cursor_session_double_insert_before<M: OrderedMap<i32, i32>>(m: &mut M) -> (Gap, Gap) {
    let mut cursor = m.lower_bound_mut(&10);
    cursor.insert_before(10, 20);
    cursor.insert_before(20, 30);
    (cursor.peek_prev(), cursor.peek_next())
}

fn cursor_session_remove_next<M: OrderedMap<i32, i32>>(m: &mut M, key: &i32) -> CursorSessionA {
    let mut cursor = m.lower_bound_mut(key);
    let removed = cursor.remove_next();
    (removed, cursor.peek_prev(), cursor.peek_next())
}

fn cursor_session_set_prev_value<M: OrderedMap<i32, i32>>(
    m: &mut M,
    key: &i32,
    value: i32,
) -> (bool, Gap, Gap) {
    let mut cursor = m.lower_bound_mut(key);
    let did_set = cursor.set_prev_value(value);
    (did_set, cursor.peek_prev(), cursor.peek_next())
}

#[test]
fn vec_reference_contract_has_explicit_expected_results() {
    let mut map = Reference::from_entries([(20, 2), (0, 0), (10, 1), (10, 11)]);
    assert_eq!(map.ordered_entries(), vec![(0, 0), (10, 11), (20, 2)]);
    assert_eq!(map.predecessor_le(&10), Some((10, 11)));
    assert_eq!(map.predecessor_lt(&10), Some((0, 0)));
    assert_eq!(map.successor_ge(&11), Some((20, 2)));
    assert_eq!(map.successors_ge(&10), vec![(10, 11), (20, 2)]);
    assert_eq!(map.insert(10, 12), Some(11));
    assert_eq!(map.remove(&0), Some(0));
    assert_eq!(map.ordered_entries(), vec![(10, 12), (20, 2)]);

    {
        let mut cursor = map.lower_bound_mut(&15);
        assert_eq!(cursor.peek_prev(), Some((10, 12)));
        assert_eq!(cursor.peek_next(), Some((20, 2)));
        assert_eq!(cursor.remove_next(), Some((20, 2)));
        cursor.insert_before(15, 15);
        assert_eq!(cursor.peek_prev(), Some((15, 15)));
        assert_eq!(cursor.peek_next(), None);
    }
    assert_eq!(map.ordered_entries(), vec![(10, 12), (15, 15)]);

    let original = TaggedKey {
        order: 7,
        tag: "original",
    };
    let replacement = TaggedKey {
        order: 7,
        tag: "replacement",
    };
    let mut reference = VecOrderedMap::from_entries([(original.clone(), 1)]);
    let mut adapter: BTreeMap<TaggedKey, i32> = [(original, 1)].into_iter().collect();
    assert_eq!(reference.insert(replacement.clone(), 2), Some(1));
    assert_eq!(adapter.insert(replacement, 2), Some(1));
    assert_eq!(reference.ordered_entries()[0].0.tag, "original");
    assert_eq!(adapter.ordered_entries()[0].0.tag, "original");
}

#[test]
fn exhaustive_small_maps_match_all_order_observations() {
    let keys = [-2, -1, 0, 1, 2];
    for mask in 0..(1_u32 << keys.len()) {
        let entries = keys
            .into_iter()
            .enumerate()
            .filter(|(index, _)| mask & (1 << index) != 0)
            .map(|(_, key)| (key, key * 10));
        let (reference, adapter) = maps(entries);
        assert_same(&reference, &adapter);
        for key in -3..=3 {
            assert_eq!(reference.predecessor_le(&key), adapter.predecessor_le(&key));
            assert_eq!(reference.predecessor_lt(&key), adapter.predecessor_lt(&key));
            assert_eq!(reference.successor_ge(&key), adapter.successor_ge(&key));
            assert_eq!(reference.successors_ge(&key), adapter.successors_ge(&key));
            assert_eq!(
                gap_observations(&reference, &key),
                gap_observations(&adapter, &key)
            );
        }
    }
}

#[test]
fn insert_replace_remove_and_value_mutation_match() {
    let (mut reference, mut adapter) = maps([(0, 10), (20, 30)]);

    assert_eq!(reference.insert(10, 11), adapter.insert(10, 11));
    assert_same(&reference, &adapter);
    assert_eq!(reference.insert(10, 12), adapter.insert(10, 12));
    assert_same(&reference, &adapter);
    assert_eq!(
        reference.set_predecessor_value(&10, 13),
        adapter.set_predecessor_value(&10, 13)
    );
    assert_eq!(
        reference.set_successor_value(&11, 14),
        adapter.set_successor_value(&11, 14)
    );
    assert_eq!(
        reference.set_predecessor_value(&-1, 15),
        adapter.set_predecessor_value(&-1, 15)
    );
    assert_same(&reference, &adapter);
    assert_eq!(reference.remove(&0), adapter.remove(&0));
    assert_eq!(reference.remove(&0), adapter.remove(&0));
    assert_eq!(reference.remove(&20), adapter.remove(&20));
    assert_same(&reference, &adapter);
}

/// The chained-lookup pattern that replaced `predecessors_le_descending`:
/// production code never walks back more than one extra step past the
/// immediate predecessor, so "the predecessor before the predecessor" is
/// expressed with a second `predecessor_lt` call rather than a
/// collection-returning trait method.
#[test]
fn chained_predecessor_lookups_match_two_step_descending_walk() {
    for key in -3..=3 {
        let (reference, adapter) = maps([(-2, -20), (-1, -10), (0, 0), (1, 10), (2, 20)]);
        let reference_first = reference.predecessor_le(&key);
        let adapter_first = adapter.predecessor_le(&key);
        assert_eq!(reference_first, adapter_first);

        let reference_second = reference_first.and_then(|(k, _)| reference.predecessor_lt(&k));
        let adapter_second = adapter_first.and_then(|(k, _)| adapter.predecessor_lt(&k));
        assert_eq!(reference_second, adapter_second);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct StoredRun {
    end: i32,
    value: char,
}

type StoredRunGap = Option<(i32, StoredRun)>;

fn set_prev_value_session<M: OrderedMap<i32, StoredRun>>(
    m: &mut M,
    key: &i32,
    value: StoredRun,
) -> (bool, StoredRunGap, StoredRunGap) {
    let mut cursor = m.lower_bound_mut(key);
    let did_set = cursor.set_prev_value(value);
    (did_set, cursor.peek_prev(), cursor.peek_next())
}

#[test]
fn structured_end_and_payload_mutation_match() {
    let entries = [
        (0, StoredRun { end: 9, value: 'a' }),
        (
            10,
            StoredRun {
                end: 19,
                value: 'b',
            },
        ),
        (
            20,
            StoredRun {
                end: 29,
                value: 'c',
            },
        ),
    ];
    let mut reference = VecOrderedMap::from_entries(entries.clone());
    let mut adapter: BTreeMap<i32, StoredRun> = entries.into_iter().collect();

    let grown = StoredRun {
        end: 24,
        value: 'b',
    };
    assert_eq!(
        reference.set_predecessor_value(&10, grown.clone()),
        adapter.set_predecessor_value(&10, grown)
    );
    let residual = StoredRun {
        end: 29,
        value: 'x',
    };
    assert_eq!(
        reference.set_successor_value(&20, residual.clone()),
        adapter.set_successor_value(&20, residual)
    );

    let trimmed = StoredRun { end: 8, value: 'a' };
    assert_eq!(
        set_prev_value_session(&mut reference, &20, trimmed.clone()),
        set_prev_value_session(&mut adapter, &20, trimmed)
    );
    assert_eq!(reference.ordered_entries(), adapter.ordered_entries());
}

#[test]
fn mutable_cursor_operations_match_gap_semantics() {
    for (entries, start) in [(vec![], 0), (vec![(10, 20)], 10), (vec![(10, 20)], 11)] {
        let (mut reference, mut adapter) = maps(entries);
        assert_eq!(
            cursor_session_peek_then_remove_next(&mut reference, &start),
            cursor_session_peek_then_remove_next(&mut adapter, &start)
        );
        assert_same(&reference, &adapter);
    }

    for start in [-1, 0, 1, 9, 10, 11, 30, 31] {
        let (mut reference, mut adapter) = maps([(0, 10), (10, 20), (20, 30), (30, 40)]);
        assert_eq!(
            cursor_session_set_prev_then_remove_next(&mut reference, &start),
            cursor_session_set_prev_then_remove_next(&mut adapter, &start)
        );
        assert_same(&reference, &adapter);
    }
}

#[test]
fn insert_before_moves_the_gap_after_the_inserted_entry() {
    for (start, inserted) in [(-1, -1), (5, 5), (15, 15), (25, 25), (31, 31)] {
        let (mut reference, mut adapter) = maps([(0, 10), (10, 20), (20, 30), (30, 40)]);
        let reference_result = cursor_session_insert_before(&mut reference, start, inserted);
        let adapter_result = cursor_session_insert_before(&mut adapter, start, inserted);
        assert_eq!(reference_result, adapter_result);
        assert_eq!(reference_result.1, Some((inserted, 99)));
        assert_same(&reference, &adapter);
    }

    let (mut reference, mut adapter) = maps([(0, 10), (30, 40)]);
    let reference_result = cursor_session_double_insert_before(&mut reference);
    let adapter_result = cursor_session_double_insert_before(&mut adapter);
    assert_eq!(reference_result, adapter_result);
    assert_eq!(reference_result, (Some((20, 30)), Some((30, 40))));
    assert_same(&reference, &adapter);
}

#[derive(Clone, Copy)]
enum Operation {
    Insert(i32),
    Remove(i32),
}

fn run_sequence(sequence: &[Operation]) {
    let (mut reference, mut adapter) = maps([]);
    for operation in sequence {
        match *operation {
            Operation::Insert(key) => {
                assert_eq!(
                    reference.insert(key, key * 10),
                    adapter.insert(key, key * 10)
                );
            }
            Operation::Remove(key) => {
                assert_eq!(reference.remove(&key), adapter.remove(&key));
            }
        }
        assert_same(&reference, &adapter);
    }
}

fn enumerate_sequences(prefix: &mut Vec<Operation>, operations: &[Operation], remaining: usize) {
    if remaining == 0 {
        run_sequence(prefix);
        return;
    }
    for operation in operations {
        prefix.push(*operation);
        enumerate_sequences(prefix, operations, remaining - 1);
        prefix.pop();
    }
}

#[test]
fn exhaustive_short_insert_remove_sequences_match() {
    let operations = [
        Operation::Insert(-1),
        Operation::Insert(0),
        Operation::Insert(1),
        Operation::Remove(-1),
        Operation::Remove(0),
        Operation::Remove(1),
    ];
    enumerate_sequences(&mut Vec::new(), &operations, 5);
}

#[test]
fn deterministic_randomized_operation_sequences_match() {
    let (mut reference, mut adapter) = maps([]);
    let mut state = 0x5eed_1234_9876_abcd_u64;

    for step in 0..10_000 {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        let key = ((state >> 32) % 17) as i32 - 8;
        let value = step * 31;
        match state % 8 {
            0 | 1 => assert_eq!(reference.insert(key, value), adapter.insert(key, value)),
            2 => assert_eq!(reference.remove(&key), adapter.remove(&key)),
            3 => assert_eq!(
                reference.set_predecessor_value(&key, value),
                adapter.set_predecessor_value(&key, value)
            ),
            4 => assert_eq!(reference.predecessor_le(&key), adapter.predecessor_le(&key)),
            5 => assert_eq!(reference.successor_ge(&key), adapter.successor_ge(&key)),
            6 => assert_eq!(
                cursor_session_remove_next(&mut reference, &key),
                cursor_session_remove_next(&mut adapter, &key)
            ),
            _ => assert_eq!(
                cursor_session_set_prev_value(&mut reference, &key, value),
                cursor_session_set_prev_value(&mut adapter, &key, value)
            ),
        }
        assert_same(&reference, &adapter);
    }
}
