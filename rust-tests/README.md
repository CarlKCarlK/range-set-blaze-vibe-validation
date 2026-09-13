# Ordered-map semantics

This auxiliary project documents and validates the observable
`std::collections::BTreeMap` behavior assumed by the modeled RangeSetBlaze
insertion and query paths. It contains an abstract semantic trait, a sorted-Vec
reference implementation, a thin `BTreeMap` adapter, differential tests, and
focused direct cursor tests.

It does not prove `BTreeMap` correct and is not a model of the standard
library's internal tree.

The confidence chain is:

```text
Lean sorted-list semantics
        ↕
sorted-Vec SemanticOrderedMap
        ↕ differential tests
BTreeMapAdapter
        ↕
modeled production API usage
```

The Lean model intentionally excludes internal B-tree nodes, rotations,
borrowing, ownership machinery, and related implementation details.

## Toolchain and API

The production crate uses the nightly-only `BTreeMap` cursor API with the
`btree_cursors` feature gate, selected by its
`cursor_nightly_experimental` Cargo feature. The API names exercised here are
ordered iteration and range direction, insertion/replacement, removal,
value-only mutation, `lower_bound`, `lower_bound_mut`, `peek_prev`,
`peek_next`, `remove_next`, and `insert_before`. The project pins
`nightly-2026-04-03` in `rust-toolchain.toml`.

## Correspondence

| Rust observation | Lean assumption | Match? |
| --- | --- | --- |
| `lower_bound_mut(Included(start))` puts the gap before the first key `>= start` | `lowerBoundGap`: `left` contains keys `< start`, `right` contains keys `>= start` | Yes |
| `peek_prev` is the greatest key in `left`; `peek_next` is the least key in `right` | `CursorGap.peekPrev` / `CursorGap.peekNext` | Yes |
| `remove_next` removes the right head and keeps the gap, so predecessor stays visible and next advances | `scanForward` consumes the right suffix | Yes |
| Mutating the value through `peek_prev` leaves cursor position unchanged | predecessor mutation replaces the last `left` entry | Yes |
| `insert_before` inserts at the gap and moves the gap after the inserted entry | `insertBefore` / emitted pending run is between finalized `left` and untouched `right` | Yes |

The differential tests compare every returned observation and the complete
ordered state after mutations. They include exhaustive small maps, exhaustive
short operation sequences, structured end/payload mutation, and deterministic
randomized sequences. The original direct cursor tests remain focused
regressions.

See `../specs/ordered-map-semantics.md` for the contract and
`../specs/ordered-map-semantics-audit.md` for the production inventory and
Rust-to-Lean correspondence.

## Running

```bash
cd rust-tests
cargo test
cargo fmt --check
cargo clippy --all-targets --all-features -- -D warnings
```
