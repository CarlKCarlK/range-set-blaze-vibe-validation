use ordered_map_semantics::{
    BTreeMapAdapter, SemanticCursor, SemanticCursorMut, SemanticOrderedMap, VecOrderedMap,
};
use std::cmp::Ordering;

type Reference = VecOrderedMap<i32, i32>;
type Adapter = BTreeMapAdapter<i32, i32>;

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
        Adapter::from_entries(entries),
    )
}

fn assert_same(reference: &Reference, adapter: &Adapter) {
    assert_eq!(reference.ordered_entries(), adapter.ordered_entries());
}

#[test]
fn vec_reference_contract_has_explicit_expected_results() {
    let mut map = Reference::from_entries([(20, 2), (0, 0), (10, 1), (10, 11)]);
    assert_eq!(map.ordered_entries(), vec![(0, 0), (10, 11), (20, 2)]);
    assert_eq!(map.predecessor_le(&10), Some((10, 11)));
    assert_eq!(map.predecessor_lt(&10), Some((0, 0)));
    assert_eq!(map.successor_ge(&11), Some((20, 2)));
    assert_eq!(map.predecessors_le_descending(&10), vec![(10, 11), (0, 0)]);
    assert_eq!(map.successors_ge_ascending(&10), vec![(10, 11), (20, 2)]);
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
    let mut adapter = BTreeMapAdapter::from_entries([(original, 1)]);
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

            let reference_cursor = reference.lower_bound(&key);
            let adapter_cursor = adapter.lower_bound(&key);
            assert_eq!(reference_cursor.peek_prev(), adapter_cursor.peek_prev());
            assert_eq!(reference_cursor.peek_next(), adapter_cursor.peek_next());
        }

        let (mut reference, mut adapter) = (reference, adapter);
        for key in -3..=3 {
            assert_eq!(
                reference.predecessors_le_descending(&key),
                adapter.predecessors_le_descending(&key)
            );
            assert_eq!(
                reference.successors_ge_ascending(&key),
                adapter.successors_ge_ascending(&key)
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

#[derive(Clone, Debug, Eq, PartialEq)]
struct StoredRun {
    end: i32,
    value: char,
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
    let mut adapter = BTreeMapAdapter::from_entries(entries);

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
    {
        let mut reference_cursor = reference.lower_bound_mut(&20);
        let mut adapter_cursor = adapter.lower_bound_mut(&20);
        let trimmed = StoredRun { end: 8, value: 'a' };
        assert_eq!(
            reference_cursor.set_prev_value(trimmed.clone()),
            adapter_cursor.set_prev_value(trimmed)
        );
        assert_eq!(reference_cursor.peek_prev(), adapter_cursor.peek_prev());
        assert_eq!(reference_cursor.peek_next(), adapter_cursor.peek_next());
    }
    assert_eq!(reference.ordered_entries(), adapter.ordered_entries());
}

#[test]
fn mutable_cursor_operations_match_gap_semantics() {
    for (entries, start) in [(vec![], 0), (vec![(10, 20)], 10), (vec![(10, 20)], 11)] {
        let (mut reference, mut adapter) = maps(entries);
        {
            let mut reference_cursor = reference.lower_bound_mut(&start);
            let mut adapter_cursor = adapter.lower_bound_mut(&start);
            assert_eq!(reference_cursor.peek_prev(), adapter_cursor.peek_prev());
            assert_eq!(reference_cursor.peek_next(), adapter_cursor.peek_next());
            assert_eq!(reference_cursor.remove_next(), adapter_cursor.remove_next());
        }
        assert_same(&reference, &adapter);
    }

    for start in [-1, 0, 1, 9, 10, 11, 30, 31] {
        let (mut reference, mut adapter) = maps([(0, 10), (10, 20), (20, 30), (30, 40)]);
        {
            let mut reference_cursor = reference.lower_bound_mut(&start);
            let mut adapter_cursor = adapter.lower_bound_mut(&start);
            assert_eq!(reference_cursor.peek_prev(), adapter_cursor.peek_prev());
            assert_eq!(reference_cursor.peek_next(), adapter_cursor.peek_next());
            assert_eq!(
                reference_cursor.set_prev_value(101),
                adapter_cursor.set_prev_value(101)
            );
            assert_eq!(reference_cursor.peek_prev(), adapter_cursor.peek_prev());
            assert_eq!(reference_cursor.remove_next(), adapter_cursor.remove_next());
            assert_eq!(reference_cursor.peek_prev(), adapter_cursor.peek_prev());
            assert_eq!(reference_cursor.peek_next(), adapter_cursor.peek_next());
        }
        assert_same(&reference, &adapter);
    }
}

#[test]
fn insert_before_moves_the_gap_after_the_inserted_entry() {
    for (start, inserted) in [(-1, -1), (5, 5), (15, 15), (25, 25), (31, 31)] {
        let (mut reference, mut adapter) = maps([(0, 10), (10, 20), (20, 30), (30, 40)]);
        {
            let mut reference_cursor = reference.lower_bound_mut(&start);
            let mut adapter_cursor = adapter.lower_bound_mut(&start);
            let old_next = reference_cursor.peek_next();
            assert_eq!(old_next, adapter_cursor.peek_next());
            reference_cursor.insert_before(inserted, 99);
            adapter_cursor.insert_before(inserted, 99);
            assert_eq!(reference_cursor.peek_prev(), Some((inserted, 99)));
            assert_eq!(reference_cursor.peek_prev(), adapter_cursor.peek_prev());
            assert_eq!(reference_cursor.peek_next(), old_next);
            assert_eq!(reference_cursor.peek_next(), adapter_cursor.peek_next());
        }
        assert_same(&reference, &adapter);
    }

    let (mut reference, mut adapter) = maps([(0, 10), (30, 40)]);
    {
        let mut reference_cursor = reference.lower_bound_mut(&10);
        let mut adapter_cursor = adapter.lower_bound_mut(&10);
        reference_cursor.insert_before(10, 20);
        adapter_cursor.insert_before(10, 20);
        reference_cursor.insert_before(20, 30);
        adapter_cursor.insert_before(20, 30);
        assert_eq!(reference_cursor.peek_prev(), Some((20, 30)));
        assert_eq!(reference_cursor.peek_prev(), adapter_cursor.peek_prev());
        assert_eq!(reference_cursor.peek_next(), Some((30, 40)));
        assert_eq!(reference_cursor.peek_next(), adapter_cursor.peek_next());
    }
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
            6 => {
                let mut reference_cursor = reference.lower_bound_mut(&key);
                let mut adapter_cursor = adapter.lower_bound_mut(&key);
                assert_eq!(reference_cursor.remove_next(), adapter_cursor.remove_next());
                assert_eq!(reference_cursor.peek_prev(), adapter_cursor.peek_prev());
                assert_eq!(reference_cursor.peek_next(), adapter_cursor.peek_next());
            }
            _ => {
                let mut reference_cursor = reference.lower_bound_mut(&key);
                let mut adapter_cursor = adapter.lower_bound_mut(&key);
                assert_eq!(
                    reference_cursor.set_prev_value(value),
                    adapter_cursor.set_prev_value(value)
                );
                assert_eq!(reference_cursor.peek_prev(), adapter_cursor.peek_prev());
                assert_eq!(reference_cursor.peek_next(), adapter_cursor.peek_next());
            }
        }
        assert_same(&reference, &adapter);
    }
}
