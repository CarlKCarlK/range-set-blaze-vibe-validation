# Ordered-map semantics audit

## Starting state

- Lean repository: `/home/carlk/programs/range-set-blaze-lean2`
- starting HEAD: `bf13433dd42fe3c5df4ee266bda85684f07aae99`
- starting worktree: clean
- production reference: `/home/carlk/programs/range-set-blaze`
- production HEAD: `67467ad0945a957a25afd263d3bf1bc0507122b9`
- production branch: `map-insert-cursor`
- production worktree observed clean
- auxiliary project: `rust-tests`, extended in place
- no commit created

The auxiliary `rust-toolchain.toml` initially used an invalid top-level string
form and could not be parsed by Cargo. It was corrected to the standard
`[toolchain] channel = "nightly-2026-04-03"` form before validation. The dated
toolchain makes the unstable cursor API validation reproducible.

## Complete in-scope production inventory

The scope is every `BTreeMap` operation used by the production paths already
modeled in Lean: set/map baseline and cursor `range_or_gap_at`, set/map baseline
and cursor insertion, their forward merge/delete helpers, and cached-length
variants insofar as they use the same mutations.

| API and exact production locations | Class | Required semantic property | Lean location | Before this task | Added validation |
|---|---|---|---|---|---|
| `range(..=key).next_back()`: `set.rs:766`; `map.rs:1146`; query calls `set.rs:469`, `map.rs:921` | range | greatest key `≤ key` | Algo C predecessor split; Query non-strict split | production tests | exhaustive differential predecessor tests |
| `range(key..).next()`: `set.rs:473,479`; `map.rs:925,931` | range | least key `≥ key` | Query suffix `head?` | production query tests | exhaustive differential successor tests |
| `range_mut(..=key).rev()` and repeated `next`: `set.rs:1122`; `map.rs:1503` | mutable range | descending predecessors, mutable selected value, second predecessor where used | Algo C set non-strict split; CMap/DMap predecessor effects via strict cursor-shaped splits | production insertion tests | descending-range and mutation differential tests |
| `range_mut(start..)`: `set.rs:800`; `map.rs:1158` | mutable range | ascending suffix from least key `≥ start`; selected values mutable | Algo C/CMap pure forward scans model resulting list semantics | production insertion tests | ascending-suffix and mutation differential tests |
| `insert`: modeled insertion paths `set.rs:1253`; `map.rs:1213,1622,1624,1647,1704,1949` | ordinary mutation | new insertion, existing-key replacement, previous value, unique sorted keys | Algo C/CMap list insertion/residual reconstruction | production tests | targeted, exhaustive-sequence, randomized differential tests |
| `remove`: modeled deletion paths `set.rs:824`; `map.rs:1191,1199,1204` | ordinary mutation | exact removed value; other entries unchanged; ordering preserved | Algo C/CMap absorbed suffix/residual reconstruction | production tests | targeted, exhaustive-sequence, randomized differential tests |
| mutation through range/cursor references: `set.rs:1130-1134,1204-1210`; `map.rs:1540-1543,1584-1587,1670-1672,1851-1888` | value mutation | selected value/end changes; key, order, cursor position unchanged | C/CMap/D/DMap prove the equivalent final state by pure list reconstruction | production tests; one auxiliary test | scalar and structured end/payload mutation differential tests |
| `lower_bound(Included(key))`: `set.rs:490`; `map.rs:942` | immutable cursor | exact `< key` / `≥ key` gap | Query strict split | production cursor query tests | exhaustive immutable-cursor differential tests |
| `lower_bound_mut(Included(start))`: `set.rs:1193`; `map.rs:1833` | mutable cursor | exact `< start` / `≥ start` gap | Algo D/DMap `lowerBoundGap` | direct auxiliary and production tests | full-state differential tests at all edge positions |
| `peek_prev`: query `set.rs:492`, `map.rs:944`; insertion `set.rs:1176,1196,1205`; `map.rs:1782,1842,1852,1868` | cursor | greatest entry in left side | D/DMap `left.getLast?` | direct auxiliary and production tests | differential gap observations after every mutation |
| `peek_next`: query `set.rs:496,505`, `map.rs:948,960`; insertion `set.rs:1155,1219`; `map.rs:1742` | cursor | least entry in right side | D/DMap `right.head?` | direct auxiliary and production tests | differential gap observations after every mutation |
| `remove_next`: `set.rs:1165`; `map.rs:1772` | mutable cursor | remove/return right head; gap remains at same split | D/DMap forward recursion | direct auxiliary and production tests | differential return, full state, and gap tests |
| `insert_before`: `set.rs:1230`; `map.rs:1723` | mutable cursor | ordered insertion; gap moves after inserted entry | Algo D `insertBefore`; DMap reconstruction | direct auxiliary and production tests | five boundary/gap differential cases |
| `iter`: state/cardinality consumers including `set.rs:1063,1398`; `map.rs:1475,2301` | iterator | all entries once, increasing key order | list order; `rangesToSet`, `runsToFunction`, cardinality | production iteration tests | compared after every differential mutation |

The map baseline's second call to the reversed predecessor iterator is why the
contract retains `predecessor_lt`/descending predecessors even though the set
algorithm needs only the greatest predecessor.

## Classified out-of-scope production APIs

The inventory also found APIs that are real RangeSetBlaze behavior but are not
consumed by an existing Lean insertion/query proof:

- `first_key_value`, `last_key_value`, `first_entry`, `last_entry`, and
  `remove_entry` in first/last/pop paths;
- `get`/`get_mut` and entry APIs in unmodeled utility paths;
- `split_off` in set/map splitting;
- removal-path predecessor mutation and residual reinsertion at `set.rs:957,
  977,980` and `map.rs:1357,1384`;
- `clear`, `is_empty`, `len`, and `retain`;
- consuming iteration and unrelated collection conversions.

They are explicitly excluded rather than silently treated as validated.
`remove_prev` and `insert_after` do not occur in the production code and are
also excluded.

## ADT and implementations

`rust-tests/src/lib.rs` defines:

- `SemanticOrderedMap<K, V>`: ordinary and range-derived semantic operations;
- `SemanticCursor<K, V>`: immutable adjacent-entry observations;
- `SemanticCursorMut<K, V>`: mutable adjacent-entry observations and the used
  cursor mutations;
- `VecOrderedMap<K, V>` and index-based `VecCursor`/`VecCursorMut`;
- `BTreeMapAdapter<K, V>` and thin standard-library cursor adapters.

The trait uses cloned values deliberately. No contract statement depends on
concrete standard-library reference, iterator, cursor, borrowing, or lifetime
types. The Vec cursor stores `gap: usize`, with `entries[..gap]` and
`entries[gap..]` directly realizing the semantic split.

## Test matrix

| Suite | Coverage |
|---|---|
| `btreemap_cursor_semantics.rs` (5 retained tests) | direct lower bound, `remove_next`, `insert_before`, predecessor mutation, combined mutation sequence |
| `vec_reference_contract_has_explicit_expected_results` | independent expected results for sorting/uniqueness, bounds, replacement/removal, and cursor transitions |
| `exhaustive_small_maps_match_all_order_observations` | 32 small map shapes × 7 query positions; ordered state, predecessor/successor, descending/ascending ranges, immutable cursor neighbors |
| `insert_replace_remove_and_value_mutation_match` | new insert, replacement return, predecessor/successor value-only mutation, absent boundaries, repeated removal |
| `structured_end_and_payload_mutation_match` | Vec/BTree agreement when the stored value contains both a mutable range end and payload |
| `mutable_cursor_operations_match_gap_semantics` | explicit empty/singleton cases plus 8 multi-entry positions; predecessor mutation, `remove_next`, post-state and gap |
| `insert_before_moves_the_gap_after_the_inserted_entry` | before first, three interior gaps, after last, and two consecutive inserts for pending plus right residual; exact post-insert cursor location |
| `exhaustive_short_insert_remove_sequences_match` | 7,776 length-five sequences; 38,880 state transitions |
| `deterministic_randomized_operation_sequences_match` | 10,000 mixed ordinary/range/cursor steps with full-state comparison after each step |

No external randomized-test dependency was added; the randomized suite uses a
fixed local generator and is exactly reproducible.

## Lean semantic layer and correspondence

The chosen integration is option B: existing list/cursor definitions provide
the corresponding algorithm-level semantics. Lean does not expose a generic
ADT or standalone theorem for every trait method. This avoids a speculative
generic module and respects the Phase-4 freeze on proof contracts and bodies.

| Production call | ADT operation | Vec implementation | BTreeMap adapter | Lean theorem/model | Consumer |
|---|---|---|---|---|---|
| `range(..=key).next_back()` | `predecessor_le` | partition after keys `≤ key`, previous index | inclusive range + `next_back` | Query `nonstrictSplit_spec`; Algo C non-strict span + `getLast?` | baseline queries; Algo C set insertion |
| repeated reverse predecessor range | descending predecessors / `predecessor_lt` | reverse filtered prefix | `range_mut(..=key).rev()` | predecessor ordering is represented in CMap/DMap strict cursor-shaped models, not an exact Lean baseline iterator model | baseline map insertion |
| `range(key..).next()` | `successor_ge` | first index with key `≥ key` | range + `next` | Query split suffix `head?` | baseline queries |
| `range_mut(start..)` | ascending suffix | filtered suffix | mutable range iterator | Algo C/CMap forward scans model the resulting list state | baseline merge/delete |
| `insert` | insert/replace | binary-search replace or indexed insert | `BTreeMap::insert` | list insertion/residual reconstruction | set/map insertion |
| `remove` | remove exact key | binary-search indexed removal | `BTreeMap::remove` | suffix consumption/reconstruction | baseline merge/delete |
| `lower_bound[ _mut ](Included key)` | lower-bound gap | `partition_point(< key)` | std lower bound | Query `strictSplit_spec`; D `lowerBoundGap_spec`; DMap `lowerBoundGap_decomposition` | cursor query/insertion |
| `peek_prev` | left last | `entries[gap-1]` | std cursor | `CursorGap.peekPrev = left.getLast?` | D/DMap predecessor branches |
| `peek_next` | right first | `entries[gap]` | std cursor | `CursorGap.peekNext = right.head?` | D/DMap forward branches |
| mutate neighbor | replace neighbor value | indexed assignment | assignment through cursor/range result | equivalent final state via functional range/run reconstruction | C/CMap/D/DMap |
| `remove_next` | consume right head | `Vec::remove(gap)` | std cursor removal | recursive scan over right tail | D/DMap forward scan |
| `insert_before` | insert at gap, advance gap | insert at index then `gap += 1` | std cursor insertion | Algo D `CursorGap.insertBefore`; equivalent DMap list output | fresh cursor insertion |
| `iter` | `ordered_entries` | cloned Vec | BTreeMap iterator | canonical ordered list | all list semantics/length models |

Important Lean foundations already present include `NR.before` and ordering
lemmas in `Basic.lean`, `Run.before`/`Canonical`, `rangesToSet`,
`runsToFunction`, Query's strict/nonstrict split specifications, Algo D's
`lowerBoundGap_spec`, and Algo DMap's `lowerBoundGap_decomposition`. Existing
scan/reconstruction correctness theorems establish the mutation semantics at
the algorithm level. No public Lean theorem or executable definition changed.

## Unsupported assumptions and limitations

No unsupported ordered-map assumption remains within the inventoried modeled
paths. Each primitive is executable-reference validated against `BTreeMap`;
the Lean side proves the corresponding query or final insertion-state semantics
over sorted lists. The latter is sometimes an algorithm-level reconstruction,
not a standalone operational theorem for the individual primitive.

Two adjacent limitations are intentionally not claimed away:

1. Lean uses dense, unbounded `Int`; the generic Rust `Integer` carrier has
   bounds, checked successor/predecessor, and possible holes such as `char`.
2. Production split/pop/retain/entry behavior has no current Lean algorithm
   model and therefore was not pulled into this ADT.

Neither is an implicit ordered-map assumption of the proved paths.

## Cleanup passes

1. Local: kept the original focused cursor tests, removed no coverage, used one
   shared cloning helper, and kept direct Vec operations visible.
2. Cross-layer: aligned names with predecessor/successor and cursor-gap concepts
   already used by Lean without imitating Lean syntax or Rust lifetimes.
3. Simplification: avoided GAT return-reference complexity by returning cloned
   observations; no dependency or bespoke random framework was introduced.

## Verification and metrics

### Metrics

- Rust trait/reference/adapter LOC added: 435 physical lines;
- differential/reference test LOC added: 343 physical lines;
- total new Rust semantic-layer and test LOC: 778 physical lines;
- existing focused test LOC: net reduction of 5 physical lines from
  clippy-only simplification, with all 5 tests retained;
- abstract operations: 10 ordinary/range operations and 7 cursor-gap concepts;
- relevant standard-library API shapes exercised: 15, including iterator/range
  direction, ordinary mutation, immutable/mutable lower bounds, and four cursor
  methods;
- targeted test functions: 13 total (5 retained direct tests, 8 new suites);
- exhaustive cases: 32 map shapes × 7 bounds plus 7,776 operation sequences
  comprising 38,880 transitions;
- randomized cases: 10,000 deterministic transitions;
- Lean semantic lemmas added: 0, because existing proofs already establish the
  corresponding algorithm-level sorted-list semantics;
- existing local Lean assumptions eliminated: 0; they were mapped and made
  explicit rather than refactored across the Phase-4 boundary;
- unsupported ordered-map assumptions in modeled paths: 0;
- Lean metric delta: zero; no `.lean` source changed.

These are separate signals, not a composite score.

### Commands and results

- `cargo fmt --check`: passed;
- `cargo test`: passed, 13 integration tests plus library/doc-test targets;
- `cargo clippy --all-targets --all-features -- -D warnings`: passed;
- pinned compiler: `rustc 1.96.0-nightly (55e86c996 2026-04-02)` via
  `nightly-2026-04-03`;
- direct Lean compilation: `AlgoD.lean`, `AlgoDMap.lean`, and `Query.lean`
  passed with no warnings;
- `lake env lean RangeSetBlaze.lean`: passed with no warnings;
- `lake build`: passed (1,892 jobs; expected `Main.lean` evaluation output);
- v3 metric regression suite: 6 tests passed;
- active repository-owned Lean forbidden-token scan: no `sorry`, `admit`,
  source `axiom`, `unsafe`, `implemented_by`, or `sorryAx`;
- axiom inventory: 15 representative Algo C/D, map, Len, query, and canonical
  theorems retain only `propext`, `Classical.choice`, and/or `Quot.sound`; none
  depends on `sorryAx`;
- `git diff --check`: passed;
- production Rust repository: inspected and independently tested by the
  inventory pass; not modified;
- no commit created.

The final architectural assessment is that the ADT surface is minimal for the
modeled paths, the Vec code is a direct executable reading of the contract, the
adapter exercises the actual standard-library API shapes, and the existing
Lean sorted-list proofs provide the required formal side of the boundary.
