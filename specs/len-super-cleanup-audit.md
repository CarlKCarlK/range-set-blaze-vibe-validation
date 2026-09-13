# Len super-cleanup audit

Date: 2026-09-12

## Scope and baseline

This cleanup covers CLen, DLen, CMapLen, and DMapLen at baseline commit
`177f88a03396def093a66fdce805b44491e8d520`. The working tree was clean at
the baseline. No Rust source was read for modification or changed, and no
commit, tag, or push was made.

Metrics use `scripts/phase0_metrics.py` collector/schema v3. The collector
SHA-256 is
`a07fc3573ed0134219b1d539c2684d717707ab7360a8e0ba97602ef95549e048`.
The before and after machine-readable results are
`/tmp/len-super-cleanup-before-v3.json` and
`/tmp/len-super-cleanup-after-v3.json`. The baseline Lean-source manifest is
`6d6d150c0cd30f2935915a18829282feebe64e02abdfc69450926d706c6885f7`;
the final manifest is
`469febe84dd384d17553cdf7d8c63b74c5dd18caf9d629dd63bcdae0e8df7a18`.

The Nat architecture was not revisited. Semantic cardinality, public caches,
and private caches remain `Nat`.

## Pass 1: individual cleanup

### CLen

- The endpoint and cached-base theorems for `deleteExtraCLenLoop` were proved
  together. They traversed the same executable recursion and both are consumed
  by the fresh and predecessor-extension cardinality proofs.
- `finishDeleteExtraCLen_preserves_endpoints_and_cached_base` now returns the
  endpoint and cache facts together. Its callers no longer reopen
  `finishDeleteExtraCLen` merely to recover unchanged scan fields.
- The selected-predecessor decomposition now uses
  `List.dropLast_append_getLast?` directly. The separate nonempty proof,
  dependent `getLast`, and equality transport disappeared.
- A `List.span` result is reconstructed by applying `congrArg` once to its pair
  equation, rather than extracting its fields and rebuilding the take/drop
  decomposition.
- An unused `hlastSpan` fact and ineffective trailing namespace opens were
  removed.

### DLen

- DLen now spells both executable right-tail additions with
  `IntRange.rightExtensionCardinality`, the same semantic operation already
  used by CLen and the map variants. This is definitionally the former
  interval-cardinality expression; branch structure and data are unchanged.
- The predecessor decomposition uses `List.dropLast_append_getLast?`
  directly.
- Endpoint preservation remains separate: unlike cache preservation, it needs
  the semantic lower-bound premise. Combining it would burden the fresh path
  with an irrelevant hypothesis.

### CMapLen and DMapLen

- Six private residual-cardinality wrappers were deleted. The two
  `rightResidualAfter_cardinality` declarations were dead; the four remaining
  wrappers had one use each and merely specialized the stable `IntRange`
  split theorems from `Basic.lean`.
- The four clients now apply
  `cardinality_eq_left_residual_add_tail` or
  `cardinality_eq_left_add_middle_add_right` directly with focused `simpa`.
- All eight local non-underflow witnesses were retained. They expose four
  distinct reachable cache decompositions per map scan/dispatcher rather than
  accidental arithmetic boilerplate.

Pass 1 removed seven private proof declarations: one net CLen scan helper and
the six map residual wrappers. It removed one duplicate induction immediately;
the remaining scan-recursion consolidation was completed in Pass 2 after the
four local shapes had been compared. Exact intermediate LOC snapshots were not
retained; the reproducible baseline-to-final section metrics are reported
below, while these declaration and induction deltas are exact from the diff.

Rejected in this pass:

- Inlining the exact fresh-insertion correspondence theorem: it is a useful
  boundary between cached bookkeeping and Algo C representation equality.
- Combining DLen endpoint preservation with cache preservation: their natural
  assumptions differ.
- Removing named cache decompositions such as `hlengthParts`, `htrimCache`,
  and `hafterRemoval`: those facts explain why `Nat.sub` is safe.

## Pass 2: cross-algorithm cleanup

### Shared mathematics

One shared semantic theorem was added:

- `RangeMapBlaze.Run.cardinality_eq_add_right_extension` lifts the existing NR
  theorem to value-carrying runs. It is used by both map algorithms, twice in
  each file, and hides only the value-irrelevant projection from a run to its
  range.

`rangesCardinality` and `runsCardinality` are now expressed as `List.sum` over
mapped cardinalities. Their append theorems are direct library applications.
This removed two definitionally identical append inductions without adding a
generic cardinality framework.

### Recursive scan contracts

- CLen's exact representation correspondence, endpoint preservation, and
  cached-base invariant are now one theorem and one induction over
  `deleteExtraCLenLoop`.
- DLen's exact representation correspondence and cached-base invariant are
  now one theorem and one induction over `absorbSuccessorsDLen`.
- No recursion was shared between different algorithms. CLen and DLen retain
  their own executable predicates and result representations; CMapLen and
  DMapLen retain their distinct exact-cover and `unchanged` mechanics.

Pass 2 removed two further private scan helpers, two Len-section inductions,
and two shared-cardinality append inductions. It added one public shared lemma.
Together with Pass 1, private proof declarations fell by nine and induction
sites fell by five repository-wide.

Rejected in this pass:

- A generic “removed piece is bounded by cache” lemma. Each stronger local
  cache equality already yields the inequality in one focused step; a helper
  would hide the source of non-underflow.
- Shared cursor/scan state, `countPendingIfFresh`, residual constructors,
  classifiers, or `unchanged` state. These are control flow, not shared
  mathematics.
- Cross-file unification of CLen/DLen or CMapLen/DMapLen branch proofs. Their
  similarity is production correspondence, not a common mathematical
  recursion.

## Pass 3: stronger-inference cleanup

The meaningful inference jumps were:

- direct `List.dropLast_append_getLast?` use from an existing `getLast? = some`
  fact;
- direct reconstruction of a span by applying a function to the span pair
  equation;
- direct use of `not_lt.mp` at CMapLen and DMapLen nonempty boundaries instead
  of invoking arithmetic automation;
- direct projection/application of the new run cardinality theorem with
  inferred value types;
- direct consumption of the joint CLen finish contract instead of unfolding
  the definition and splitting its cache-only branch again;
- inlining DMapLen's one-use public `hraw` transport into a focused `simpa`.

The pass also removed one unused intermediate fact, one unused local binding,
and two ineffective trailing opens. It did not change the declaration or
induction counts established by Pass 2.

Rejected in this pass:

- Replacing the DMapLen classifier analysis with a new result structure or
  one-use helper. Its residual equalities are local control-flow evidence, and
  packaging them would relocate rather than remove complexity.
- Broad `simp_all`, tactic compression, or deletion of semantic named
  decompositions merely to reduce lexical counts.
- Removing explicit predicate/list arguments from fragile take/drop-while
  uses, where the arguments improve error localization.

## Measurement limitation

The source passes were performed and compiled in the required order, but the
v3 collector was not run at the two intermediate pass boundaries. Because the
work is one uncommitted aggregate diff and several joint-contract edits share
hunks, exact intermediate physical/active/tactic snapshots cannot now be
reconstructed reproducibly without inventing checkpoint source states.

Accordingly, the tables below give exact, reproducible baseline and final
metrics. The pass sections above give exact declaration/induction changes by
pass, but this audit does **not** claim per-pass LOC or tactic snapshots. This
is an unmet measurement-process requirement, not a proof or verification
failure.

## Metrics

The following section slices begin at each cached-length section marker and
continue to the end of its module. Counts are comment-aware v3 lexical
metrics. They are independent review signals, not a composite score.

| Metric | CLen before | CLen after | DLen before | DLen after | CMapLen before | CMapLen after | DMapLen before | DMapLen after |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Physical LOC | 580 | 534 | 495 | 483 | 517 | 481 | 603 | 569 |
| Active-code LOC | 507 | 467 | 442 | 432 | 455 | 428 | 540 | 515 |
| Private proof declarations/lemmas | 9 | 7 | 8 | 7 | 6 | 3 | 6 | 3 |
| `induction` | 3 | 1 | 3 | 2 | 1 | 1 | 1 | 1 |
| `cases` | 0 | 0 | 6 | 6 | 6 | 6 | 12 | 12 |
| `by_cases` | 12 | 10 | 10 | 9 | 18 | 18 | 10 | 10 |
| `have` | 55 | 45 | 39 | 38 | 41 | 41 | 44 | 43 |
| `rw` | 23 | 21 | 18 | 18 | 11 | 11 | 8 | 8 |
| `show` | 6 | 6 | 0 | 0 | 0 | 0 | 0 | 0 |
| `simp` | 49 | 44 | 37 | 35 | 66 | 66 | 49 | 49 |
| `simpa` | 27 | 24 | 27 | 25 | 28 | 25 | 33 | 30 |
| `omega` | 8 | 8 | 7 | 6 | 18 | 16 | 16 | 14 |

Whole-file metrics:

| File | Physical before | Physical after | Active before | Active after | Private proofs before | Private proofs after | `induction` before | `induction` after | `have` before | `have` after | `rw` before | `rw` after |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `AlgoC.lean` | 1375 | 1329 | 1164 | 1124 | 19 | 17 | 4 | 2 | 177 | 167 | 59 | 57 |
| `AlgoD.lean` | 942 | 930 | 808 | 798 | 13 | 12 | 4 | 3 | 82 | 81 | 40 | 40 |
| `AlgoCMap.lean` | 1456 | 1420 | 1316 | 1289 | 19 | 16 | 6 | 6 | 168 | 168 | 24 | 24 |
| `AlgoDMap.lean` | 1920 | 1886 | 1789 | 1764 | 25 | 22 | 7 | 7 | 217 | 216 | 30 | 30 |

Additional whole-file tactic counts:

| File | `cases` before/after | `by_cases` before/after | `show` before/after | `simp` before/after | `simpa` before/after | `omega` before/after |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `AlgoC.lean` | 4 / 4 | 16 / 14 | 9 / 9 | 83 / 78 | 53 / 50 | 12 / 12 |
| `AlgoD.lean` | 7 / 7 | 13 / 12 | 1 / 1 | 58 / 56 | 40 / 38 | 7 / 6 |
| `AlgoCMap.lean` | 6 / 6 | 51 / 51 | 2 / 2 | 160 / 160 | 82 / 79 | 51 / 49 |
| `AlgoDMap.lean` | 19 / 19 | 52 / 52 | 7 / 7 | 145 / 145 | 111 / 108 | 61 / 59 |

Repository totals:

| Metric | Before | After | Delta |
| --- | ---: | ---: | ---: |
| Physical LOC | 7575 | 7455 | -120 |
| Active-code LOC | 6607 | 6510 | -97 |
| Private proof declarations | 95 | 86 | -9 |
| `induction` | 33 | 28 | -5 |
| `cases` | 60 | 60 | 0 |
| `by_cases` | 152 | 149 | -3 |
| `have` | 799 | 787 | -12 |
| `rw` | 190 | 188 | -2 |
| `show` | 35 | 35 | 0 |
| `simp` | 574 | 565 | -9 |
| `simpa` | 334 | 323 | -11 |
| `omega` | 187 | 182 | -5 |

## Arithmetic and recursion endpoint

- Explicit non-underflow witnesses: CLen 1, DLen 1, CMapLen 4, DMapLen 4.
- Nat/Int conversions in all four Len sections: 0.
- Len-section recursive proof sites: 8 before, 5 after.
- Recursive proofs unified: three duplicate within-algorithm scan traversals
  were eliminated (two in CLen, one in DLen). No recursive proof was unified
  across algorithms.
- Shared lemmas added: 1 (`Run.cardinality_eq_add_right_extension`).
- Private proof helpers removed: 9 net.

What remains deliberately algorithm-specific:

- CLen's strict/non-strict span boundaries and Algo C exact list
  correspondence;
- DLen's cursor gap, mergeability classifier, predecessor/successor access,
  and lower-bound-dependent endpoint theorem;
- CMapLen's unguarded exact-cover reachability premise;
- DMapLen's guarded exact-cover/`unchanged` state and predecessor classifier;
- all four executable branch trees and their residual/scan constructors.

## Verification

All requested checks passed with no Lean warnings:

- `lake env lean RangeSetBlaze/AlgoC.lean`
- `lake env lean RangeSetBlaze/AlgoD.lean`
- `lake env lean RangeSetBlaze/AlgoCMap.lean`
- `lake env lean RangeSetBlaze/AlgoDMap.lean`
- `lake env lean RangeSetBlaze.lean`
- `lake build` — 1,886 jobs; only the expected `Main.lean` `#eval`
  informational output
- v3 metric regression tests — 6 passed
- `git diff --check`

Intermediate compilation also passed:

- after each Pass 1 individual cleanup, its affected module was compiled
  directly before moving to the next module;
- after Pass 2 shared-cardinality and joint-contract changes, `Basic.lean` and
  all four affected algorithm modules compiled directly;
- after Pass 3, all four modules compiled directly before the final suite.

The active repository-owned Lean-source scan found no `sorry`, `admit`, source
`axiom`, `unsafe`, `implemented_by`, or `sorryAx`.

All twelve public Len theorem inventories are identical and clean:

| Public theorem | Axioms |
| --- | --- |
| `RangeSetBlaze.internalAddCLen_setResult` | `[propext, Classical.choice, Quot.sound]` |
| `RangeSetBlaze.internalAddCLen_cachedLength` | `[propext, Classical.choice, Quot.sound]` |
| `RangeSetBlaze.internalAddCLen_toSet` | `[propext, Classical.choice, Quot.sound]` |
| `RangeSetBlaze.internalAddDLen_setResult` | `[propext, Classical.choice, Quot.sound]` |
| `RangeSetBlaze.internalAddDLen_cachedLength` | `[propext, Classical.choice, Quot.sound]` |
| `RangeSetBlaze.internalAddDLen_toSet` | `[propext, Classical.choice, Quot.sound]` |
| `RangeMapBlaze.internalAddCMapLen_mapResult` | `[propext, Classical.choice, Quot.sound]` |
| `RangeMapBlaze.internalAddCMapLen_cachedLength` | `[propext, Classical.choice, Quot.sound]` |
| `RangeMapBlaze.internalAddCMapLen_toFunction` | `[propext, Classical.choice, Quot.sound]` |
| `RangeMapBlaze.internalAddDMapLen_mapResult` | `[propext, Classical.choice, Quot.sound]` |
| `RangeMapBlaze.internalAddDMapLen_cachedLength` | `[propext, Classical.choice, Quot.sound]` |
| `RangeMapBlaze.internalAddDMapLen_toFunction` | `[propext, Classical.choice, Quot.sound]` |

No theorem depends on `sorryAx`.

## Final assessment

The four Len proofs now look structurally settled. Their stable mathematics is
shared at the interval, nonempty-range, run, and list-cardinality layers. Their
remaining scan invariants and branch decompositions correspond to genuinely
different production-shaped algorithms. Further compression would most likely
hide local subtraction evidence or turn cursor/scan control flow into a broad
proof framework.

Suggested commit message:

`Unify and simplify cached-length proofs`
