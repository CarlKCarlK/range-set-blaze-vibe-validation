# ordered-map

Auxiliary Rust crate (`ordered_map`) that pins down, as runnable and
differentially-tested code, the fragment of `std::collections::BTreeMap`'s
observable behavior that the Lean `range-set-blaze-lean2` proofs assume.

Start with the generated rustdoc — `cargo doc --no-deps --open` — and read
the crate-level docs, then [`OrderedMap`](src/lib.rs). That is the complete
public API and its rationale, including why the crate exposes narrow
predecessor/successor operations instead of the full `BTreeMap::range`
iterator API, and the exact `BTreeMap` expression each one models.

This file only orients newcomers to the repository layout:

- [`src/lib.rs`](src/lib.rs) — the `OrderedMap`/`Cursor`/`CursorMut` traits,
  the `VecOrderedMap` reference implementation, and direct trait
  implementations on `std::collections::BTreeMap` and its cursor types.
- [`tests/ordered_map_differential.rs`](tests/ordered_map_differential.rs) —
  differential tests asserting `VecOrderedMap` and `BTreeMap` agree on every
  operation (exhaustive small maps, exhaustive short operation sequences,
  and long deterministic randomized sequences).
- [`tests/btreemap_cursor.rs`](tests/btreemap_cursor.rs) — focused direct
  `BTreeMap` cursor regression tests, retained from before the differential
  suite existed.

See `../specs/ordered-map.md` for the abstract contract and its
correspondence to the Lean proofs, and `../specs/ordered-map-audit.md` for
the production API inventory and validation history.

## Running

```bash
cd rust-tests
cargo test
cargo test --doc
cargo fmt --check
cargo clippy --all-targets --all-features -- -D warnings
cargo doc --no-deps
```
