#![feature(btree_cursors)]
#![deny(missing_docs)]

//! Start with [`OrderedMap`]. It is the complete abstract ordered-map
//! contract used by the Lean proofs. [`Cursor`] and [`CursorMut`] define the
//! cursor behavior. [`VecOrderedMap`] is the transparent reference
//! implementation. `BTreeMap` implements the same contract and is
//! differential-tested against the reference implementation.
//!
//! # What this crate is for
//!
//! RangeSetBlaze has two independent production implementations of the same
//! insertion and query algorithms: a stable baseline that looks up and
//! mutates one predecessor or successor at a time through `BTreeMap::range`
//! / `range_mut`, and a nightly-only algorithm
//! (`#![feature(btree_cursors)]`) that walks a single gap between entries
//! with a cursor. This crate pins down, as runnable and
//! differentially-tested Rust, the ordered-map contract both paths assume —
//! the fragment of `BTreeMap`'s observable behavior that RangeSetBlaze's
//! Lean proofs rely on.
//!
//! It does not prove `BTreeMap` correct and is not a model of the standard
//! library's internal tree; B-tree node layout, balancing, allocation, and
//! complexity are outside the model.
//!
//! # The sorted unique-key model
//!
//! An ordered map is a sequence of `(key, value)` pairs with strictly
//! increasing keys, so each key occurs at most once and every stored entry
//! occurs exactly once in the sequence. [`OrderedMap::ordered_entries`] is
//! that sequence, cloned. Every other operation is defined relative to it.
//!
//! # Ordinary ordered-map operations
//!
//! [`OrderedMap`] provides the predecessor/successor lookups and mutations
//! used by the *baseline* (non-cursor) production algorithm:
//! [`predecessor_le`](OrderedMap::predecessor_le),
//! [`predecessor_lt`](OrderedMap::predecessor_lt),
//! [`successor_ge`](OrderedMap::successor_ge),
//! [`successors_ge`](OrderedMap::successors_ge), plain
//! [`insert`](OrderedMap::insert)/[`remove`](OrderedMap::remove), and
//! neighbor-value mutation via
//! [`set_predecessor_value`](OrderedMap::set_predecessor_value) /
//! [`set_successor_value`](OrderedMap::set_successor_value).
//!
//! # The gap/cursor model
//!
//! [`lower_bound`](OrderedMap::lower_bound) and
//! [`lower_bound_mut`](OrderedMap::lower_bound_mut) return a [`Cursor`] /
//! [`CursorMut`] for the *cursor-based* production algorithm. A cursor does
//! not point *at* an entry; it sits in the gap between two adjacent entries
//! (or before the first entry / after the last):
//!
//! ```text
//! ... prev | next ...
//! ```
//!
//! `prev` is the entry immediately to the left of the gap (returned by
//! `peek_prev`); `next` is the entry immediately to the right (returned by
//! `peek_next`). Mutating cursor methods are defined by how they rewrite the
//! entries adjacent to the gap and where the gap ends up afterward.
//!
//! Both vocabularies exist because both production code paths are real and
//! independently exercised — this is not accidental duplication. They agree
//! by construction:
//!
//! ```
//! use ordered_map::{Cursor, OrderedMap, VecOrderedMap};
//!
//! let map = VecOrderedMap::from_entries([(0, "a"), (10, "b"), (20, "c")]);
//! for key in [-1, 0, 5, 10, 25] {
//!     let cursor = map.lower_bound(&key);
//!     assert_eq!(map.predecessor_lt(&key), cursor.peek_prev());
//!     assert_eq!(map.successor_ge(&key), cursor.peek_next());
//! }
//! ```
//!
//! # The Vec reference implementation
//!
//! [`VecOrderedMap`] is a simple, obviously-correct oracle backed by a
//! sorted `Vec`: every operation is a binary search or linear scan. It
//! exists to be read and trusted, not to be fast.
//!
//! # The BTreeMap implementation
//!
//! `std::collections::BTreeMap<K, V>` implements [`OrderedMap`] directly
//! (see its entry in the [`OrderedMap`] implementor list), including
//! `std::collections::btree_map::Cursor`/`CursorMut` implementing [`Cursor`]
//! / [`CursorMut`]. No adapter or wrapper type is needed: the traits are
//! local to this crate, so Rust's orphan rule permits implementing them
//! directly on the standard-library types.
//!
//! One naming caveat: `BTreeMap::lower_bound[_mut]` and
//! `btree_map::Cursor[Mut]::peek_prev`/`peek_next` are also *inherent*
//! methods on those standard-library types, with different signatures
//! (`Bound<&K>` instead of `&K`; borrowed instead of cloned observations).
//! Inherent methods always shadow trait methods of the same name in method
//! call syntax, so calling these through [`OrderedMap`] on a concrete
//! `BTreeMap`/`Cursor`/`CursorMut` value requires either a generic function
//! parameterized over the trait, or fully-qualified syntax such as
//! `OrderedMap::lower_bound(&map, &key)`. This is a call-site ergonomics
//! detail, not a coherence or compilation blocker:
//!
//! ```
//! use ordered_map::{Cursor, OrderedMap};
//! use std::collections::BTreeMap;
//!
//! let map: BTreeMap<i32, &str> = [(0, "a"), (10, "b"), (20, "c")].into();
//!
//! // `map.lower_bound(&15)` would not compile here: the inherent
//! // `BTreeMap::lower_bound` takes `Bound<&K>`, not `&K`. Naming the trait
//! // explicitly selects the `OrderedMap` method instead.
//! let cursor = OrderedMap::lower_bound(&map, &15);
//!
//! // Likewise, `cursor.peek_prev()` would resolve to the inherent
//! // `btree_map::Cursor::peek_prev`, which borrows instead of cloning.
//! assert_eq!(Cursor::peek_prev(&cursor), Some((10, "b")));
//! assert_eq!(Cursor::peek_next(&cursor), Some((20, "c")));
//! ```
//!
//! Every other trait method (`predecessor_le`, `predecessor_lt`,
//! `successor_ge`, `successors_ge`, `set_predecessor_value`,
//! `set_successor_value`, `ordered_entries`, `remove_next`,
//! `set_prev_value`) has no inherent-method collision and can be called
//! with ordinary method syntax on a concrete `BTreeMap`/cursor value.
//! `insert`/`remove` do have inherent counterparts, but with identical
//! signatures and behavior, so the shadowing is harmless.
//!
//! # What differential testing establishes
//!
//! `tests/ordered_map_differential.rs` asserts that [`VecOrderedMap`] and
//! `BTreeMap` agree on every [`OrderedMap`]/[`Cursor`]/[`CursorMut`]
//! operation, for exhaustive small maps, exhaustive short operation
//! sequences, and long deterministic randomized sequences. This
//! corroborates that the `BTreeMap` API shapes the baseline and cursor
//! algorithms use exhibit the semantics the Lean proofs assume; it is not a
//! proof of the standard library's implementation.
//!
//! # Outside scope
//!
//! Borrowing, lifetimes, allocation, balancing, and complexity are not part
//! of the contract: every [`OrderedMap`]/[`Cursor`]/[`CursorMut`] method
//! returns owned, cloned data. Unmodeled production APIs — `split_off`,
//! `entry`, `first`/`last` accessors, `clear`, `retain`, and arbitrary
//! cursor movement (`remove_prev`, `insert_after`) — are not part of the
//! trait because the currently proved insertion/query algorithms do not use
//! them.
//!
//! ## Semantics, not a cost model
//!
//! This crate models only observable *results*: which entries exist, their
//! order, and how a mutation transitions one map state to the next. It does
//! not claim to preserve the computational cost of the production
//! `BTreeMap` operations it names. In particular it does not model:
//!
//! - asymptotic complexity;
//! - iterator laziness;
//! - allocation cost;
//! - borrowing/lifetime cost;
//! - the number of tree searches performed;
//! - B-tree node layout or balancing;
//! - amortized iterator-step cost.
//!
//! [`successors_ge`](OrderedMap::successors_ge) is the sharpest example of
//! this distinction. In production Rust,
//!
//! ```rust,ignore
//! map.range(key..)
//! ```
//!
//! performs one ordered range seek and then yields entries lazily, one at a
//! time, as the caller walks forward; entries beyond whatever the caller
//! consumes are never touched. The abstract/reference operation
//!
//! ```rust,ignore
//! successors_ge(key)
//! ```
//!
//! instead returns the entire ascending suffix at once, as an owned `Vec`.
//! This intentionally preserves which entries are available, their order,
//! and the semantic prefix a caller may choose to consume — exactly the
//! information the proofs need — but it does **not** preserve lazy
//! iteration, allocation behavior, or the number/cost of iterator steps.
//!
//! Crucially, `successors_ge(key)` must **not** be read as repeated calls to
//! [`successor_ge`](OrderedMap::successor_ge). It corresponds to a single
//! `BTreeMap::range(key..)` call followed by ascending iteration to
//! completion, not to re-seeking the tree once per returned element.
//! Similarly, the cloned `(K, V)` pairs returned throughout this trait
//! abstract away `BTreeMap`'s borrowing and lifetime costs: production code
//! observes references into the tree, not owned copies.

use std::collections::BTreeMap;
use std::collections::btree_map;
use std::ops::Bound;

/// A read-only view of a single gap between adjacent entries, in ascending
/// key order.
///
/// A cursor never points *at* an entry; it sits in the gap `prev | next`
/// between two entries (or before the first entry / after the last).
/// `peek_prev` and `peek_next` observe the entries immediately adjacent to
/// that gap without moving it. See the [crate-level documentation](crate)
/// for the gap model.
pub trait Cursor<K, V> {
    /// Returns a clone of `prev`, the entry immediately to the left of the
    /// gap, or `None` if the gap is before the first entry.
    ///
    /// ```
    /// use ordered_map::{Cursor, OrderedMap};
    /// use std::collections::BTreeMap;
    ///
    /// let map: BTreeMap<i32, &str> = [(0, "a"), (10, "b"), (20, "c")].into();
    /// let cursor = OrderedMap::lower_bound(&map, &15);
    /// assert_eq!(Cursor::peek_prev(&cursor), Some((10, "b")));
    /// ```
    fn peek_prev(&self) -> Option<(K, V)>;

    /// Returns a clone of `next`, the entry immediately to the right of the
    /// gap, or `None` if the gap is after the last entry.
    ///
    /// ```
    /// use ordered_map::{Cursor, OrderedMap};
    /// use std::collections::BTreeMap;
    ///
    /// let map: BTreeMap<i32, &str> = [(0, "a"), (10, "b"), (20, "c")].into();
    /// let cursor = OrderedMap::lower_bound(&map, &15);
    /// assert_eq!(Cursor::peek_next(&cursor), Some((20, "c")));
    /// ```
    fn peek_next(&self) -> Option<(K, V)>;
}

/// Mutations available at a gap, used by the cursor-shaped RangeSetBlaze
/// algorithms (e.g. extending, splitting, and merging runs in place).
///
/// Every method is defined purely in terms of the gap `prev | next`: it
/// reads or rewrites the entries adjacent to the gap, and states exactly
/// where the gap ends up afterward. See the [crate-level
/// documentation](crate) for the gap model.
pub trait CursorMut<K, V> {
    /// Returns a clone of `prev`, the entry immediately to the left of the
    /// gap, or `None` if the gap is before the first entry. Does not move
    /// the gap or mutate the map.
    fn peek_prev(&mut self) -> Option<(K, V)>;

    /// Returns a clone of `next`, the entry immediately to the right of the
    /// gap, or `None` if the gap is after the last entry. Does not move
    /// the gap or mutate the map.
    fn peek_next(&mut self) -> Option<(K, V)>;

    /// Overwrites the value of `prev`, leaving its key and the gap
    /// position unchanged.
    ///
    /// Returns `true` if there was a `prev` entry to update. Returns
    /// `false`, without effect, if the gap is before the first entry.
    ///
    /// ```
    /// use ordered_map::{CursorMut, OrderedMap, VecOrderedMap};
    ///
    /// let mut map = VecOrderedMap::from_entries([(0, "a"), (20, "c")]);
    /// {
    ///     let mut cursor = map.lower_bound_mut(&10);
    ///     assert!(cursor.set_prev_value("a-updated"));
    ///     assert_eq!(cursor.peek_prev(), Some((0, "a-updated")));
    ///     assert_eq!(cursor.peek_next(), Some((20, "c")));
    /// }
    /// assert_eq!(map.ordered_entries(), vec![(0, "a-updated"), (20, "c")]);
    /// ```
    fn set_prev_value(&mut self, value: V) -> bool;

    /// Removes `next` and returns it.
    ///
    /// The gap does not move: the entry that used to follow `next` becomes
    /// the new `next`, and `prev` is unaffected. Returns `None`, without
    /// effect, if the gap is after the last entry.
    ///
    /// ```
    /// use ordered_map::{CursorMut, OrderedMap, VecOrderedMap};
    ///
    /// let mut map = VecOrderedMap::from_entries([(0, "a"), (10, "b"), (20, "c")]);
    /// {
    ///     let mut cursor = map.lower_bound_mut(&10);
    ///     assert_eq!(cursor.remove_next(), Some((10, "b")));
    ///     assert_eq!(cursor.peek_prev(), Some((0, "a")));
    ///     assert_eq!(cursor.peek_next(), Some((20, "c")));
    /// }
    /// assert_eq!(map.ordered_entries(), vec![(0, "a"), (20, "c")]);
    /// ```
    fn remove_next(&mut self) -> Option<(K, V)>;

    /// Inserts `(key, value)` immediately before `next`, then moves the gap
    /// to just after the newly inserted entry.
    ///
    /// Before: `prev | next`. After: `prev, (key, value) | next` — the new
    /// entry becomes `prev` and `next` is unchanged.
    ///
    /// # Panics
    ///
    /// The caller must supply a `key` strictly between the adjacent keys
    /// (greater than `prev`'s key, if any, and less than `next`'s key, if
    /// any). Implementations panic if this precondition is violated.
    ///
    /// ```
    /// use ordered_map::{CursorMut, OrderedMap, VecOrderedMap};
    ///
    /// let mut map = VecOrderedMap::from_entries([(0, "a"), (20, "c")]);
    /// {
    ///     let mut cursor = map.lower_bound_mut(&10);
    ///     assert_eq!(cursor.peek_prev(), Some((0, "a")));
    ///     assert_eq!(cursor.peek_next(), Some((20, "c")));
    ///     cursor.insert_before(10, "b");
    ///     // The gap has moved: the new entry is now `prev`, `next` is unchanged.
    ///     assert_eq!(cursor.peek_prev(), Some((10, "b")));
    ///     assert_eq!(cursor.peek_next(), Some((20, "c")));
    /// }
    /// assert_eq!(map.ordered_entries(), vec![(0, "a"), (10, "b"), (20, "c")]);
    /// ```
    fn insert_before(&mut self, key: K, value: V);
}

/// The implementation-independent ordered-map operations used by the
/// proofs: a collection of `(K, V)` pairs kept sorted by unique key.
///
/// `OrderedMap` models only the observable ordered-map behavior used by the
/// proved RangeSetBlaze algorithms. It deliberately does not attempt to
/// model or reproduce the full `BTreeMap::range`/`range_mut` iterator API —
/// no generic `RangeBounds`, no arbitrary bidirectional iteration, no
/// iterator state, no borrowing/lifetimes, no partial iteration, no mutable
/// iterator mechanics. RangeSetBlaze's production algorithms use only a
/// small, fixed set of `BTreeMap::range` shapes, always driven to
/// completion the same way (take the first/last result, or walk a suffix
/// from one end). So instead of a general iterator model, this trait gives
/// each of those shapes its own name — a direct semantic operation for
/// exactly the observation the proved code performs:
///
/// | `OrderedMap` operation | `BTreeMap` operation |
/// |---|---|
/// | [`predecessor_le`](Self::predecessor_le)`(k)` | `range(..=k).next_back()` |
/// | [`predecessor_lt`](Self::predecessor_lt)`(k)` | `range(..k).next_back()` |
/// | [`successor_ge`](Self::successor_ge)`(k)` | `range(k..).next()` |
/// | [`successors_ge`](Self::successors_ge)`(k)` | ascending iteration of `range(k..)` |
/// | [`lower_bound`](Self::lower_bound)`(k)` | `lower_bound(Included(k))` |
/// | [`lower_bound_mut`](Self::lower_bound_mut)`(k)` | `lower_bound_mut(Included(k))` |
///
/// None of `predecessor_le`, `predecessor_lt`, `successor_ge`, or
/// `successors_ge` are real `BTreeMap` methods — `BTreeMap` has no methods
/// by those names. They are this crate's names for the `range` expressions
/// in the table above; see each method's own documentation for the exact
/// expression it models. The table is orientation, not a substitute for the
/// per-method documentation below.
///
/// All operations return **cloned** entries; borrowing, allocation, and
/// complexity are outside the contract (see the [crate-level
/// documentation](crate)). [`VecOrderedMap`] and `BTreeMap` are the two
/// implementations in this crate; differential tests assert they agree on
/// every operation.
pub trait OrderedMap<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    /// A read-only cursor into this map. See [`Cursor`].
    type Cursor<'a>: Cursor<K, V>
    where
        Self: 'a,
        K: 'a,
        V: 'a;

    /// A mutable cursor into this map. See [`CursorMut`].
    type CursorMut<'a>: CursorMut<K, V>
    where
        Self: 'a,
        K: 'a,
        V: 'a;

    /// Returns every entry, cloned, in ascending key order.
    ///
    /// Keys are unique, so this is a complete, canonical snapshot of the
    /// map's contents.
    ///
    /// ```
    /// use ordered_map::{OrderedMap, VecOrderedMap};
    ///
    /// let map = VecOrderedMap::from_entries([(20, "b"), (10, "a")]);
    /// assert_eq!(map.ordered_entries(), vec![(10, "a"), (20, "b")]);
    /// ```
    fn ordered_entries(&self) -> Vec<(K, V)>;

    /// Returns the entry with the greatest key **less than or equal to**
    /// `key`, or `None` if every stored key is greater than `key`.
    ///
    /// Models `map.range(..=key).next_back()`, used directly by the
    /// baseline (non-cursor) production insertion path. (`BTreeMap` has no
    /// method literally named `predecessor_le`; this is this crate's name
    /// for that `range` expression.)
    ///
    /// ```
    /// use ordered_map::{OrderedMap, VecOrderedMap};
    ///
    /// let map = VecOrderedMap::from_entries([(10, "a"), (20, "b")]);
    /// assert_eq!(map.predecessor_le(&15), Some((10, "a")));
    /// assert_eq!(map.predecessor_le(&10), Some((10, "a")));
    /// assert_eq!(map.predecessor_le(&5), None);
    /// ```
    fn predecessor_le(&self, key: &K) -> Option<(K, V)>;

    /// Returns the entry with the greatest key **strictly less than**
    /// `key` — an entry whose key equals `key` is not returned — or `None`
    /// if no such entry exists.
    ///
    /// Models `map.range(..key).next_back()`; equivalently, in cursor form,
    /// `map.lower_bound(Bound::Included(key)).peek_prev()`. (`BTreeMap` has
    /// no method literally named `predecessor_lt`; this is this crate's
    /// name for those two equivalent expressions.)
    ///
    /// ```
    /// use ordered_map::{OrderedMap, VecOrderedMap};
    ///
    /// let map = VecOrderedMap::from_entries([(10, "a"), (20, "b")]);
    /// assert_eq!(map.predecessor_lt(&20), Some((10, "a")));
    /// assert_eq!(map.predecessor_lt(&10), None);
    /// ```
    fn predecessor_lt(&self, key: &K) -> Option<(K, V)>;

    /// Returns the entry with the least key **greater than or equal to**
    /// `key`, or `None` if every stored key is less than `key`.
    ///
    /// Models `map.range(key..).next()`, used directly by the baseline
    /// (non-cursor) production query and insertion paths; equivalently, in
    /// cursor form, `map.lower_bound(Bound::Included(key)).peek_next()`.
    /// (`BTreeMap` has no method literally named `successor_ge`; this is
    /// this crate's name for those two equivalent expressions.)
    ///
    /// ```
    /// use ordered_map::{OrderedMap, VecOrderedMap};
    ///
    /// let map = VecOrderedMap::from_entries([(10, "a"), (20, "b")]);
    /// assert_eq!(map.successor_ge(&15), Some((20, "b")));
    /// assert_eq!(map.successor_ge(&20), Some((20, "b")));
    /// assert_eq!(map.successor_ge(&25), None);
    /// ```
    fn successor_ge(&self, key: &K) -> Option<(K, V)>;

    /// Returns every entry with key ≥ `key`, ordered from least key to
    /// greatest (i.e. the ascending suffix starting at
    /// [`successor_ge`](Self::successor_ge)).
    ///
    /// Models ascending iteration of `map.range(key..)`. (`BTreeMap` has no
    /// method literally named `successors_ge`; this is this crate's name
    /// for that range expression.)
    ///
    /// Production (the baseline merge/delete paths) never drains this range
    /// unconditionally — it walks forward through however many touching or
    /// overlapping entries a mutation must absorb, a data-dependent prefix
    /// decided while scanning, not a fixed-length lookup. This method
    /// returns the whole ordered suffix rather than an iterator, so the
    /// proof/reference model has the relevant ordered data available
    /// without reproducing Rust's iterator/borrowing machinery; it is the
    /// caller's job to decide how much of the returned `Vec` to consume,
    /// matching how the production algorithm and its Lean model both work.
    ///
    /// This is a semantic model of one `BTreeMap::range(key..)` traversal,
    /// not a cost model: the reference API eagerly materializes the suffix
    /// instead of preserving the production iterator's laziness or
    /// complexity. See [Semantics, not a cost model](crate#semantics-not-a-cost-model)
    /// for the general distinction.
    ///
    /// ```
    /// use ordered_map::{OrderedMap, VecOrderedMap};
    ///
    /// let map = VecOrderedMap::from_entries([(0, "a"), (10, "b"), (20, "c")]);
    /// assert_eq!(map.successors_ge(&10), vec![(10, "b"), (20, "c")]);
    /// assert_eq!(map.successors_ge(&21), Vec::new());
    /// ```
    fn successors_ge(&self, key: &K) -> Vec<(K, V)>;

    /// Inserts `(key, value)`.
    ///
    /// If an entry with an equal key already existed, its value is
    /// replaced and the **old value** is returned; the previously stored
    /// key is retained rather than being overwritten by the new key
    /// (matching `BTreeMap::insert`). If no such entry existed, a new
    /// entry is inserted and `None` is returned.
    ///
    /// ```
    /// use ordered_map::{OrderedMap, VecOrderedMap};
    ///
    /// let mut map = VecOrderedMap::from_entries([(10, "a")]);
    /// assert_eq!(map.insert(20, "b"), None);
    /// assert_eq!(map.insert(10, "a-replacement"), Some("a"));
    /// assert_eq!(map.ordered_entries(), vec![(10, "a-replacement"), (20, "b")]);
    /// ```
    fn insert(&mut self, key: K, value: V) -> Option<V>;

    /// Removes the entry with the given key, if present, and returns its
    /// value.
    ///
    /// ```
    /// use ordered_map::{OrderedMap, VecOrderedMap};
    ///
    /// let mut map = VecOrderedMap::from_entries([(10, "a"), (20, "b")]);
    /// assert_eq!(map.remove(&10), Some("a"));
    /// assert_eq!(map.remove(&10), None);
    /// assert_eq!(map.ordered_entries(), vec![(20, "b")]);
    /// ```
    fn remove(&mut self, key: &K) -> Option<V>;

    /// Overwrites the value of the [`predecessor_le`](Self::predecessor_le)
    /// entry in place, leaving its key unchanged.
    ///
    /// Returns the entry's **previous** `(key, value)` pair, or `None`,
    /// without effect, if no predecessor exists. Models mutating the value
    /// found by `map.range_mut(..=key).next_back()`, used by the baseline
    /// production insertion and removal paths (e.g. growing a run's end in
    /// place) — the non-cursor counterpart of
    /// [`CursorMut::set_prev_value`].
    ///
    /// ```
    /// use ordered_map::{OrderedMap, VecOrderedMap};
    ///
    /// let mut map = VecOrderedMap::from_entries([(10, "a"), (20, "b")]);
    /// assert_eq!(map.set_predecessor_value(&15, "a-grown"), Some((10, "a")));
    /// assert_eq!(map.ordered_entries(), vec![(10, "a-grown"), (20, "b")]);
    /// assert_eq!(map.set_predecessor_value(&5, "unreachable"), None);
    /// ```
    fn set_predecessor_value(&mut self, key: &K, value: V) -> Option<(K, V)>;

    /// Overwrites the value of the [`successor_ge`](Self::successor_ge)
    /// entry in place, leaving its key unchanged.
    ///
    /// Returns the entry's **previous** `(key, value)` pair, or `None`,
    /// without effect, if no successor exists. Models mutating the value
    /// found by `map.range_mut(key..).next()`, used by the baseline
    /// production merge/delete path (e.g. shrinking a run's start in
    /// place).
    ///
    /// ```
    /// use ordered_map::{OrderedMap, VecOrderedMap};
    ///
    /// let mut map = VecOrderedMap::from_entries([(10, "a"), (20, "b")]);
    /// assert_eq!(map.set_successor_value(&15, "b-shrunk"), Some((20, "b")));
    /// assert_eq!(map.ordered_entries(), vec![(10, "a"), (20, "b-shrunk")]);
    /// assert_eq!(map.set_successor_value(&25, "unreachable"), None);
    /// ```
    fn set_successor_value(&mut self, key: &K, value: V) -> Option<(K, V)>;

    /// Returns a read-only cursor positioned at the gap immediately before
    /// the first entry with key ≥ `key` — equivalently, immediately after
    /// the last entry with key < `key`.
    ///
    /// `cursor.peek_next()` yields the same entry as
    /// [`successor_ge`](Self::successor_ge)`(key)`, and `cursor.peek_prev()`
    /// yields the same entry as
    /// [`predecessor_lt`](Self::predecessor_lt)`(key)`.
    ///
    /// ```
    /// use ordered_map::{Cursor, OrderedMap, VecOrderedMap};
    ///
    /// let map = VecOrderedMap::from_entries([(10, "a"), (30, "c")]);
    /// let cursor = map.lower_bound(&20);
    /// assert_eq!(cursor.peek_prev(), Some((10, "a")));
    /// assert_eq!(cursor.peek_next(), Some((30, "c")));
    /// ```
    fn lower_bound(&self, key: &K) -> Self::Cursor<'_>;

    /// The mutable counterpart of [`lower_bound`](Self::lower_bound): same
    /// gap placement, but the returned cursor also allows mutation through
    /// [`CursorMut`].
    fn lower_bound_mut(&mut self, key: &K) -> Self::CursorMut<'_>;
}

/// Reference implementation of [`OrderedMap`] backed by a sorted `Vec`.
///
/// `VecOrderedMap` implements [`OrderedMap`]. All inherited `OrderedMap`
/// operations are demonstrated below with runnable examples; see
/// [`OrderedMap`] for the abstract contract and `BTreeMap` correspondence.
///
/// Internally, this is a `Vec<(K, V)>` kept strictly sorted by key with no
/// duplicate keys. Every [`OrderedMap`] operation is implemented directly
/// against this `Vec` with binary search or a linear scan, trading
/// performance for an implementation simple enough to trust as an oracle.
/// Differential tests assert it agrees with `BTreeMap` on every operation.
///
/// # Examples
///
/// ## Ordered lookup
///
/// [`ordered_entries`](OrderedMap::ordered_entries),
/// [`predecessor_le`](OrderedMap::predecessor_le),
/// [`predecessor_lt`](OrderedMap::predecessor_lt),
/// [`successor_ge`](OrderedMap::successor_ge), and
/// [`successors_ge`](OrderedMap::successors_ge):
///
/// ```
/// use ordered_map::{OrderedMap, VecOrderedMap};
///
/// let map = VecOrderedMap::from_entries([(20, "c"), (0, "a"), (10, "b")]);
///
/// assert_eq!(map.ordered_entries(), vec![(0, "a"), (10, "b"), (20, "c")]);
///
/// assert_eq!(map.predecessor_le(&15), Some((10, "b")));
/// assert_eq!(map.predecessor_lt(&10), Some((0, "a")));
///
/// assert_eq!(map.successor_ge(&15), Some((20, "c")));
/// assert_eq!(map.successors_ge(&10), vec![(10, "b"), (20, "c")]);
/// ```
///
/// ## Mutation
///
/// [`insert`](OrderedMap::insert), [`remove`](OrderedMap::remove),
/// [`set_predecessor_value`](OrderedMap::set_predecessor_value), and
/// [`set_successor_value`](OrderedMap::set_successor_value):
///
/// ```
/// use ordered_map::{OrderedMap, VecOrderedMap};
///
/// let mut map = VecOrderedMap::from_entries([(10, "a"), (20, "b")]);
///
/// assert_eq!(map.insert(30, "c"), None);
/// assert_eq!(map.insert(10, "a-replaced"), Some("a"));
/// assert_eq!(map.remove(&30), Some("c"));
/// assert_eq!(map.ordered_entries(), vec![(10, "a-replaced"), (20, "b")]);
///
/// assert_eq!(map.set_predecessor_value(&15, "a-grown"), Some((10, "a-replaced")));
/// assert_eq!(map.set_successor_value(&15, "b-shrunk"), Some((20, "b")));
/// assert_eq!(map.ordered_entries(), vec![(10, "a-grown"), (20, "b-shrunk")]);
/// ```
///
/// ## Cursor construction
///
/// [`lower_bound`](OrderedMap::lower_bound) and
/// [`lower_bound_mut`](OrderedMap::lower_bound_mut) return a [`Cursor`] /
/// [`CursorMut`] positioned at the gap immediately before the first entry
/// with key ≥ the given key; see the [crate-level documentation](crate) for
/// the gap model.
///
/// ```
/// use ordered_map::{Cursor, CursorMut, OrderedMap, VecOrderedMap};
///
/// let mut map = VecOrderedMap::from_entries([(0, "a"), (20, "c")]);
///
/// {
///     let cursor = map.lower_bound(&10);
///     assert_eq!(cursor.peek_prev(), Some((0, "a")));
///     assert_eq!(cursor.peek_next(), Some((20, "c")));
/// }
///
/// let mut cursor_mut = map.lower_bound_mut(&10);
/// cursor_mut.insert_before(10, "b");
/// assert_eq!(cursor_mut.peek_prev(), Some((10, "b")));
/// ```
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct VecOrderedMap<K, V> {
    entries: Vec<(K, V)>,
}

impl<K: Ord, V> VecOrderedMap<K, V> {
    /// Creates an empty map.
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Builds a map from an arbitrary, possibly unsorted, possibly
    /// duplicate-keyed, iterator of entries.
    ///
    /// Entries are inserted one at a time using the same rule as
    /// [`OrderedMap::insert`]: an entry whose key matches one already
    /// inserted replaces that entry's *value* only, so the
    /// earliest-inserted key for each distinct key is the one retained.
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

/// A [`Cursor`] into a [`VecOrderedMap`].
///
/// This type's behavior is defined by [`Cursor`]; see its documentation for
/// the full contract and the gap model. The example below demonstrates the
/// concrete reference implementation.
///
/// ```
/// use ordered_map::{Cursor, OrderedMap, VecOrderedMap};
///
/// let map = VecOrderedMap::from_entries([(0, "a"), (10, "b"), (20, "c")]);
/// let cursor = map.lower_bound(&15);
/// assert_eq!(cursor.peek_prev(), Some((10, "b")));
/// assert_eq!(cursor.peek_next(), Some((20, "c")));
/// ```
pub struct VecCursor<'a, K, V> {
    entries: &'a [(K, V)],
    gap: usize,
}

impl<K: Clone, V: Clone> Cursor<K, V> for VecCursor<'_, K, V> {
    fn peek_prev(&self) -> Option<(K, V)> {
        self.gap
            .checked_sub(1)
            .map(|index| self.entries[index].clone())
    }

    fn peek_next(&self) -> Option<(K, V)> {
        self.entries.get(self.gap).cloned()
    }
}

/// A [`CursorMut`] into a [`VecOrderedMap`].
///
/// This type's behavior is defined by [`CursorMut`]; see its documentation
/// for the full contract and the gap model. The examples below demonstrate
/// the concrete reference implementation.
///
/// # Examples
///
/// ## Observing and updating `prev`
///
/// [`peek_prev`](CursorMut::peek_prev), [`peek_next`](CursorMut::peek_next),
/// and [`set_prev_value`](CursorMut::set_prev_value):
///
/// ```
/// use ordered_map::{CursorMut, OrderedMap, VecOrderedMap};
///
/// let mut map = VecOrderedMap::from_entries([(10, "a"), (20, "b")]);
/// let mut cursor = map.lower_bound_mut(&15);
///
/// // Gap before mutation: `(10, "a") | (20, "b")`.
/// assert_eq!(cursor.peek_prev(), Some((10, "a")));
/// assert_eq!(cursor.peek_next(), Some((20, "b")));
///
/// assert!(cursor.set_prev_value("a-updated"));
///
/// // The gap does not move; only `prev`'s value changed.
/// assert_eq!(cursor.peek_prev(), Some((10, "a-updated")));
/// assert_eq!(cursor.peek_next(), Some((20, "b")));
/// ```
///
/// ## Removing `next` and inserting before it
///
/// [`remove_next`](CursorMut::remove_next) and
/// [`insert_before`](CursorMut::insert_before):
///
/// ```
/// use ordered_map::{CursorMut, OrderedMap, VecOrderedMap};
///
/// let mut map = VecOrderedMap::from_entries([(0, "a"), (10, "b"), (20, "c")]);
/// let mut cursor = map.lower_bound_mut(&10);
///
/// // Gap before mutation: `(0, "a") | (10, "b"), (20, "c")`.
/// assert_eq!(cursor.remove_next(), Some((10, "b")));
///
/// // Removing `next` does not move the gap: the following entry becomes
/// // the new `next`. Gap is now: `(0, "a") | (20, "c")`.
/// assert_eq!(cursor.peek_prev(), Some((0, "a")));
/// assert_eq!(cursor.peek_next(), Some((20, "c")));
///
/// cursor.insert_before(10, "b-reinserted");
///
/// // `insert_before` moves the gap: the new entry becomes `prev`. Gap is
/// // now: `(0, "a"), (10, "b-reinserted") | (20, "c")`.
/// assert_eq!(cursor.peek_prev(), Some((10, "b-reinserted")));
/// assert_eq!(cursor.peek_next(), Some((20, "c")));
/// ```
pub struct VecCursorMut<'a, K, V> {
    entries: &'a mut Vec<(K, V)>,
    gap: usize,
}

impl<K: Ord + Clone, V: Clone> CursorMut<K, V> for VecCursorMut<'_, K, V> {
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

impl<K, V> OrderedMap<K, V> for VecOrderedMap<K, V>
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

    fn successors_ge(&self, key: &K) -> Vec<(K, V)> {
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

// `std::collections::BTreeMap` and its `btree_map::Cursor`/`CursorMut`
// implement `OrderedMap`/`Cursor`/`CursorMut` directly below. Because the
// traits are local to this crate, the orphan rule permits implementing them
// on these standard-library types without a wrapper. See the "The BTreeMap
// implementation" section of the crate-level documentation for the one
// call-site caveat this creates (inherent-method shadowing for
// `lower_bound`/`lower_bound_mut`/`peek_prev`/`peek_next`).

impl<K: Clone, V: Clone> Cursor<K, V> for btree_map::Cursor<'_, K, V> {
    fn peek_prev(&self) -> Option<(K, V)> {
        self.peek_prev().map(clone_entry)
    }

    fn peek_next(&self) -> Option<(K, V)> {
        self.peek_next().map(clone_entry)
    }
}

impl<K: Ord + Clone, V: Clone> CursorMut<K, V> for btree_map::CursorMut<'_, K, V> {
    fn peek_prev(&mut self) -> Option<(K, V)> {
        self.peek_prev()
            .map(|(key, value)| (key.clone(), value.clone()))
    }

    fn peek_next(&mut self) -> Option<(K, V)> {
        self.peek_next()
            .map(|(key, value)| (key.clone(), value.clone()))
    }

    fn set_prev_value(&mut self, value: V) -> bool {
        let Some((_, stored)) = self.peek_prev() else {
            return false;
        };
        *stored = value;
        true
    }

    fn remove_next(&mut self) -> Option<(K, V)> {
        self.remove_next()
    }

    fn insert_before(&mut self, key: K, value: V) {
        self.insert_before(key, value)
            .expect("key does not belong at cursor gap");
    }
}

impl<K, V> OrderedMap<K, V> for BTreeMap<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    type Cursor<'a>
        = btree_map::Cursor<'a, K, V>
    where
        K: 'a,
        V: 'a;
    type CursorMut<'a>
        = btree_map::CursorMut<'a, K, V>
    where
        K: 'a,
        V: 'a;

    fn ordered_entries(&self) -> Vec<(K, V)> {
        self.iter().map(clone_entry).collect()
    }

    fn predecessor_le(&self, key: &K) -> Option<(K, V)> {
        self.range(..=key).next_back().map(clone_entry)
    }

    fn predecessor_lt(&self, key: &K) -> Option<(K, V)> {
        self.range(..key).next_back().map(clone_entry)
    }

    fn successor_ge(&self, key: &K) -> Option<(K, V)> {
        self.range(key..).next().map(clone_entry)
    }

    fn successors_ge(&self, key: &K) -> Vec<(K, V)> {
        self.range(key..).map(clone_entry).collect()
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        BTreeMap::insert(self, key, value)
    }

    fn remove(&mut self, key: &K) -> Option<V> {
        BTreeMap::remove(self, key)
    }

    fn set_predecessor_value(&mut self, key: &K, value: V) -> Option<(K, V)> {
        let (stored_key, stored_value) = self.range_mut(..=key).next_back()?;
        let old = (stored_key.clone(), stored_value.clone());
        *stored_value = value;
        Some(old)
    }

    fn set_successor_value(&mut self, key: &K, value: V) -> Option<(K, V)> {
        let (stored_key, stored_value) = self.range_mut(key..).next()?;
        let old = (stored_key.clone(), stored_value.clone());
        *stored_value = value;
        Some(old)
    }

    fn lower_bound(&self, key: &K) -> Self::Cursor<'_> {
        BTreeMap::lower_bound(self, Bound::Included(key))
    }

    fn lower_bound_mut(&mut self, key: &K) -> Self::CursorMut<'_> {
        BTreeMap::lower_bound_mut(self, Bound::Included(key))
    }
}

fn clone_entry<K: Clone, V: Clone>((key, value): (&K, &V)) -> (K, V) {
    (key.clone(), value.clone())
}
