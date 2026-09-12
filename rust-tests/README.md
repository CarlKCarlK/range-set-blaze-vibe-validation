# BTreeMap cursor semantics

This tiny auxiliary project documents and validates the `std::collections::BTreeMap`
cursor behavior assumed by the Lean `RangeSetBlaze/AlgoDMap.lean` model. It does
not test `BTreeMap` correctness, and it is not a second implementation of
RangeSetBlaze or a formal model of the standard library's internal tree.

The confidence chain is:

```text
Rust BTreeMap cursor API
        ↓
executable cursor-semantics tests
        ↓
Lean CursorGap abstraction
        ↓
AlgoDMap correctness proof
```

The Lean model intentionally excludes internal B-tree nodes, rotations,
borrowing, ownership machinery, and related implementation details.

## Toolchain and API

The production crate uses the nightly-only `BTreeMap` cursor API with the
`btree_cursors` feature gate, selected by its
`cursor_nightly_experimental` Cargo feature. The API names exercised here are
`lower_bound_mut`, `peek_prev`, `peek_next`, `remove_next`, and
`insert_before`. This project pins the `nightly` channel through
`rust-toolchain.toml`; record the exact `rustc --version` used when running it.

## Correspondence

| Rust observation | Lean assumption | Match? |
| --- | --- | --- |
| `lower_bound_mut(Included(start))` puts the gap before the first key `>= start` | `lowerBoundGap`: `left` contains keys `< start`, `right` contains keys `>= start` | Yes |
| `peek_prev` is the greatest key in `left`; `peek_next` is the least key in `right` | `CursorGap.peekPrev` / `CursorGap.peekNext` | Yes |
| `remove_next` removes the right head and keeps the gap, so predecessor stays visible and next advances | `scanForward` consumes the right suffix | Yes |
| Mutating the value through `peek_prev` leaves cursor position unchanged | predecessor mutation replaces the last `left` entry | Yes |
| `insert_before` inserts at the gap and moves the gap after the inserted entry | `insertBefore` / emitted pending run is between finalized `left` and untouched `right` | Yes |

The tests also cover the production-shaped sequence: position, inspect the
predecessor, mutate it locally, remove one or more successors, insert before
the gap, and inspect both sides immediately after every mutation.

## Running

```bash
cargo +nightly test --manifest-path rust-tests/Cargo.toml
cargo +nightly fmt --manifest-path rust-tests/Cargo.toml -- --check
cargo +nightly clippy --manifest-path rust-tests/Cargo.toml -- -D warnings
```
