#![feature(btree_cursors)]

use std::collections::BTreeMap;
use std::ops::Bound;

fn map() -> BTreeMap<i32, char> {
    BTreeMap::from([(0, 'a'), (10, 'b'), (20, 'c'), (30, 'd')])
}

fn observations(map: &mut BTreeMap<i32, char>, start: i32) -> (Vec<i32>, Option<i32>, Option<i32>) {
    let left = map.keys().copied().filter(|key| *key < start).collect();
    let mut cursor = map.lower_bound_mut(Bound::Included(&start));
    let previous = cursor.peek_prev().map(|(key, _)| *key);
    let next = cursor.peek_next().map(|(key, _)| *key);
    (left, previous, next)
}

#[test]
fn btreemap_cursor_lower_bound_matches_gap_model() {
    for start in [-1, 0, 1, 9, 10, 11, 30, 31] {
        let mut map = map();
        let (left, previous, next) = observations(&mut map, start);
        let expected_left = [0, 10, 20, 30]
            .into_iter()
            .filter(|key| *key < start)
            .collect::<Vec<_>>();
        assert_eq!(left, expected_left, "start={start}");
        assert_eq!(previous, expected_left.last().copied(), "start={start}");
        assert_eq!(
            next,
            [0, 10, 20, 30].into_iter().find(|key| *key >= start),
            "start={start}"
        );
    }
}

#[test]
fn btreemap_cursor_remove_next_matches_right_consumption() {
    let mut map = map();
    let mut cursor = map.lower_bound_mut(Bound::Included(&10));
    assert_eq!(cursor.peek_prev().map(|(key, _)| *key), Some(0));
    assert_eq!(cursor.peek_next().map(|(key, _)| *key), Some(10));

    assert_eq!(
        cursor.remove_next().map(|(key, value)| (key, value)),
        Some((10, 'b'))
    );
    assert_eq!(cursor.peek_prev().map(|(key, _)| *key), Some(0));
    assert_eq!(cursor.peek_next().map(|(key, _)| *key), Some(20));

    assert_eq!(
        cursor.remove_next().map(|(key, value)| (key, value)),
        Some((20, 'c'))
    );
    assert_eq!(cursor.peek_prev().map(|(key, _)| *key), Some(0));
    assert_eq!(cursor.peek_next().map(|(key, _)| *key), Some(30));
    assert_eq!(map.keys().copied().collect::<Vec<_>>(), vec![0, 30]);
}

#[test]
fn btreemap_cursor_insert_matches_gap_insertion() {
    let mut map = map();
    let mut cursor = map.lower_bound_mut(Bound::Included(&20));
    assert_eq!(cursor.peek_prev().map(|(key, _)| *key), Some(10));
    assert_eq!(cursor.peek_next().map(|(key, _)| *key), Some(20));

    assert_eq!(cursor.insert_before(15, 'x'), Ok(()));
    assert_eq!(cursor.peek_prev().map(|(key, _)| *key), Some(15));
    assert_eq!(cursor.peek_next().map(|(key, _)| *key), Some(20));
    assert_eq!(
        map.into_iter().collect::<Vec<_>>(),
        vec![(0, 'a'), (10, 'b'), (15, 'x'), (20, 'c'), (30, 'd')]
    );
}

#[derive(Debug, PartialEq, Eq)]
struct Run {
    end: i32,
    value: char,
}

#[test]
fn btreemap_cursor_predecessor_mutation_matches_gap_model() {
    let mut map = BTreeMap::from([
        (0, Run { end: 8, value: 'a' }),
        (
            10,
            Run {
                end: 19,
                value: 'b',
            },
        ),
        (
            20,
            Run {
                end: 29,
                value: 'c',
            },
        ),
    ]);
    let mut cursor = map.lower_bound_mut(Bound::Included(&10));
    cursor.peek_prev().unwrap().1.end = 9;
    assert_eq!(
        cursor
            .peek_prev()
            .map(|(key, run)| (*key, run.end, run.value)),
        Some((0, 9, 'a'))
    );
    assert_eq!(
        cursor
            .peek_next()
            .map(|(key, run)| (*key, run.end, run.value)),
        Some((10, 19, 'b'))
    );

    let removed = cursor.remove_next().unwrap();
    assert_eq!((removed.0, removed.1.end, removed.1.value), (10, 19, 'b'));
    assert_eq!(
        cursor
            .peek_prev()
            .map(|(key, run)| (*key, run.end, run.value)),
        Some((0, 9, 'a'))
    );
    assert_eq!(
        cursor
            .peek_next()
            .map(|(key, run)| (*key, run.end, run.value)),
        Some((20, 29, 'c'))
    );
}

#[test]
fn btreemap_cursor_mutation_sequence_preserves_expected_gap() {
    let mut map = BTreeMap::from([(0, 'a'), (10, 'b'), (20, 'c'), (30, 'd')]);
    let mut cursor = map.lower_bound_mut(Bound::Included(&10));
    assert_eq!(cursor.peek_prev().map(|(key, _)| *key), Some(0));
    assert_eq!(cursor.peek_next().map(|(key, _)| *key), Some(10));

    *cursor.peek_prev().unwrap().1 = 'z';
    assert_eq!(
        cursor.peek_prev().map(|(key, value)| (*key, *value)),
        Some((0, 'z'))
    );
    assert_eq!(cursor.peek_next().map(|(key, _)| *key), Some(10));
    cursor.remove_next().unwrap();
    assert_eq!(
        cursor.peek_prev().map(|(key, value)| (*key, *value)),
        Some((0, 'z'))
    );
    assert_eq!(cursor.peek_next().map(|(key, _)| *key), Some(20));
    cursor.remove_next().unwrap();
    assert_eq!(cursor.peek_next().map(|(key, _)| *key), Some(30));
    cursor.insert_before(15, 'x').unwrap();
    assert_eq!(
        cursor.peek_prev().map(|(key, value)| (*key, *value)),
        Some((15, 'x'))
    );
    assert_eq!(cursor.peek_next().map(|(key, _)| *key), Some(30));
    drop(cursor);
    assert_eq!(
        map.into_iter().collect::<Vec<_>>(),
        vec![(0, 'z'), (15, 'x'), (30, 'd')]
    );
}
