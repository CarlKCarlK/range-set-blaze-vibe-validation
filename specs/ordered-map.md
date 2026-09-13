# Ordered-map contract used by the RangeSetBlaze proofs

This document describes the current `ordered_map` Rust contract and its
relationship to the Lean proofs. For the public Rust API itself — every
method's exact signature, its precise `BTreeMap` correspondence, and runnable
examples — read the crate's rustdoc (`cargo doc --no-deps` in `rust-tests/`,
starting from the crate root and [`OrderedMap`]). This spec does not restate
that API documentation; it explains the proof/validation correspondence
around it.

[`OrderedMap`]: ../rust-tests/src/lib.rs

## Claim and boundary

This is an abstract ordered-map contract, not a proof of Rust's
`std::collections::BTreeMap`. The Lean development proves range-set and
range-map algorithms over sorted lists. The Rust auxiliary project (crate
`ordered_map`, in `rust-tests/`) supplies a visibly equivalent sorted-`Vec`
reference implementation (`VecOrderedMap`) and differential tests that
corroborate the behavior of the `BTreeMap` APIs used by the modeled
production algorithms.

The evidence chain is:

```text
Lean sorted-list semantics
        ↕ documented refinement
OrderedMap over VecOrderedMap (a sorted unique Vec)
        ↕ differential tests
OrderedMap over std::collections::BTreeMap
        ↕ direct API correspondence
modeled RangeSetBlaze production paths
```

This evidence does not verify the standard-library implementation, Rust's
borrow checker, or any complexity claim.

## Abstract state

An ordered map is observed as a sequence of `(key, value)` pairs satisfying:

1. keys are strictly increasing;
2. therefore each key occurs at most once;
3. every stored entry occurs exactly once in the sequence.

`VecOrderedMap<K, V>` in `rust-tests/src/lib.rs` is the executable reference.
It keeps this invariant by binary search and direct `Vec` insertion/removal.
`std::collections::BTreeMap<K, V>` implements the same `OrderedMap` trait
directly (no adapter or wrapper type). Trait results are cloned observations
so Rust reference types and lifetimes do not leak into the contract.

## Why the contract is narrow

The contract contains only the operations required by the modeled insertion,
query, and cached-length paths, named for the specific `BTreeMap::range`
expressions they stand in for rather than as a general iterator model. See
the crate-level and `OrderedMap` rustdoc for the full rationale and the
per-method `BTreeMap` correspondence table; it is not repeated here to avoid
two copies drifting apart.

Exact-key `BTreeMap::get`, `contains_key`, first/last entry APIs, entry APIs,
and split/pop/retain operations are not assumptions of the currently proved
insertion/query algorithms and are not part of this contract.

## Cursor gap

A lower-bound cursor is a gap splitting the ordered entries exactly as:

```text
entries = left ++ right
          left | right
               ^ gap
```

For `lower_bound(Included k)` and `lower_bound_mut(Included k)`:

- every key in `left` is `< k`;
- every key in `right` is `≥ k`;
- `peek_prev` is `left.last`;
- `peek_next` is `right.first`.

The mutable operations have these exact transitions:

- predecessor-value mutation replaces only `left.last.value`; the key and gap
  do not move;
- if `right = next :: rest`, `remove_next` returns `next`, changes the map to
  `left ++ rest`, and leaves the gap between `left` and `rest`;
- `insert_before(k, v)` requires `left.last.key < k < right.first.key` where
  neighbors exist. It changes the map to `left ++ [(k, v)] ++ right` and moves
  the gap after the inserted entry, so `peek_prev = (k, v)` and `peek_next`
  remains the former `right.first`.

`remove_prev`, `insert_after`, and arbitrary cursor movement are absent because
the modeled production paths do not use them.

## Lean correspondence

The existing Lean code supplies the corresponding sorted-list semantics at the
algorithm level; it does not define a generic ordered-map ADT or a standalone
theorem for every Rust trait method. No parallel generic map theory was added.

- `List (K × V)` is represented concretely by `List IntRange.NR` for sets and
  `List (Run Value)` for maps.
- strict key ordering follows from `List.Pairwise NR.before` or the stronger
  value-sensitive `Canonical = List.Pairwise Run.before` in `Basic.lean`;
- strict/non-strict `List.span` plus `getLast?` and `head?` instantiate
  predecessor, successor, and lower-bound placement;
- `Query.lean` proves strict and non-strict split contracts and proves both
  baseline and cursor queries correct;
- Algo C uses a non-strict predecessor split for set baseline insertion;
- CMap and DMap use a strict lower-bound split in pure list models of the
  production cursor insertion path; AlgoAMap separately proves reference
  overwrite semantics rather than mirroring the Rust baseline branch tree;
- Algo D/DMap define `CursorGap` as `left` and `right`, prove exact lower-bound
  decomposition, and model `peek_prev`, `peek_next`, right-head consumption,
  and the final effects of mutation through pure list reconstruction. Algo D
  has an explicit private `insertBefore`; DMap emits the equivalent list shape;
- CLen/CMapLen/DLen inherit those map-state semantics while separately proving
  cached cardinality updates.

This is the repository's option B integration: document the refinement mapping
from established algorithm-level list/cursor definitions to the contract.
Factoring another shared Lean module would duplicate stable private proof
vocabulary and cross the frozen Phase-4 boundary without eliminating an
unsupported assumption.

## What the differential tests establish

For every operation, tests compare returned observations and the entire ordered
entry sequence after mutation. They cover empty and singleton maps, all cursor
positions, exact keys and gaps, first/last removal, replacement, value mutation,
repeated changes, cursor mutation sequences, and the post-`insert_before` gap:
32 subsets of a five-key domain across seven query positions, all 7,776
length-five sequences drawn from three inserts and three removals, and 10,000
deterministic pseudo-random operation steps, plus a handful of focused direct
`BTreeMap` cursor regression tests kept from before the differential suite
existed.

See `specs/ordered-map-audit.md` for the production call-site inventory,
Rust-to-Lean correspondence, and the history of the crate's naming/API
cleanup pass.

## Outside the model

- B-tree node layout, balancing, allocation, internal algorithms, and runtime
  complexity;
- Rust borrowing, lifetime implementation, and iterator invalidation rules
  beyond the observed cursor sequence;
- unmodeled production APIs such as `split_off`, entry/pop, clear, retain, and
  first/last entry operations;
- the correspondence between generic bounded Rust `Integer` types and Lean's
  unbounded dense `Int` (notably checked successor/predecessor and `char`
  gaps);
- cached-length arithmetic itself, which has separate Lean proofs;
- a formal proof that `BTreeMap` refines this contract.

The precise claim is: Lean proves the algorithms assuming sorted-list ordered-map
semantics, and executable Rust differential tests corroborate that the used
`BTreeMap` APIs exhibit those semantics.
