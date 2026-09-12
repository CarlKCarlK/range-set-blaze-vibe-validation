# Set-length proof API audit

Date: 2026-09-12

## 1. Starting state

The cleanup started at commit
`97ca6e1a952d48c89337aeca631dcb2d7f0e7fb6` (`Prove DLen cached-length
correctness`) on `main`, synchronized with `origin/main`. `git status
--short --branch` reported only `## main...origin/main`; the worktree was
clean. The starting tree was
`d9376ca71e7cca7ceafa90f402ff129599568a6f`.

The v3 starting source manifest was
`a8bc49338a393b53f67b6a7326517ee7c278bcc5e6ada41550c8f756cc71d672`.
No Rust source was changed or needed for this cleanup.

## 2. CLen architecture and helper inventory

CLen remains list/scan shaped. It mirrors Algo C's strict/non-strict start
splits, predecessor choice, forward deletion scan, and list reconstruction.
The cache proof follows the represented cardinality of the untouched prefix,
the affected suffix, and the growing current range.

The `Callers` column names direct semantic clients rather than incidental
unfolding or documentation references. `Strength/transport` records whether a
statement exceeds what its clients need or mainly moves propositions.

| Declaration | Classification | Callers / use | Mathematics versus executable structure | Strength/transport |
| --- | --- | --- | --- | --- |
| `CLenResult` | reconstruction/plumbing | public result of `internalAddCLen`; CLen only | public packaging | exact |
| `CLenRawResult` | reconstruction/plumbing | CLen branch helpers and wrapper; CLen only | proof-free local result | exact |
| `ForwardCLenResult` | branch-local bookkeeping | CLen scan and finish helpers; CLen only | executable scan state | exact |
| `deleteExtraCLenLoop` | branch-local bookkeeping | finish and correspondence/cache proofs; CLen only | Algo C scan/update sequencing | exact; retained |
| `deleteExtraCLenLoop_corresponds` | Algo C representation correspondence | raw list correspondence and finish-related unfolding; CLen only | exact executable correspondence | exact; not weakened to `toSet` |
| `finishDeleteExtraCLen` | branch-local bookkeeping | fresh and predecessor paths; CLen only | Rust-ordered cache update | exact; retained |
| `freshInsertCLen` | branch-local bookkeeping | raw dispatcher and two proofs; CLen only | Algo C insertion path | exact; retained |
| `extendPredecessorCLen` | branch-local bookkeeping | raw dispatcher and two proofs; CLen only | Algo C predecessor path | exact; retained |
| `internalAddCLenRaw` | branch-local bookkeeping | public wrapper and top-level proofs; CLen only | full Algo CLen control flow | exact; retained |
| `deleteExtraCLenLoop_preserves_endpoints` | branch-local bookkeeping | fresh and predecessor cardinality proofs; CLen only | semantic scan invariant tied to this scan | both conjuncts used |
| `deleteExtraCLenLoop_preserves_cached_base` | branch-local bookkeeping | finish-cache theorem; CLen only | semantic cache invariant tied to this recursion | one direct client, but it is the non-underflow boundary |
| `finishDeleteExtraCLen_preserves_cached_base` | branch-local bookkeeping | fresh and predecessor cardinality proofs; CLen only | cache effect of the executable finish step | narrowed during cleanup; no correspondence projections remain |
| `freshInsertCLen_preserves_cardinality` | branch-local bookkeeping | top-level cache proof's fresh branches; CLen only | branch result cardinality | canonicality and gap premises removed because unused |
| `extendPredecessorCLen_preserves_cardinality` | branch-local bookkeeping | top-level cache proof's extension branch; CLen only | branch result cardinality | canonicality and no-gap premises removed because unused |
| `freshInsertCLen_ranges_eq_internalAdd2NRs` | Algo C representation correspondence | raw correspondence; CLen only | exact strict-boundary list equality | exact; retained |
| `internalAddCLenRaw_corresponds` | Algo C representation correspondence | wrapper construction and public equality; CLen only | exact whole-algorithm range-list equality | exact; retained |
| `internalAddCLenRaw_preserves_cardinality` | reconstruction/plumbing | public cached-length theorem; CLen only | top-level branch composition | one public projection; appropriate private boundary |
| `internalAddCLen` | reconstruction/plumbing | public API | executable wrapper | exact |
| three `internalAddCLen_*` theorems | public guarantees | public API | exact representation, cache correctness, and inherited set semantics | minimal public surface |

The former local `extensionCardinality`, `rangesCardinality_append`,
`cardinality_extend_right`, and `cardinality_eq_add_extension` declarations
were the stable-mathematics exceptions and were removed or replaced by the
shared vocabulary described below.

## 3. DLen architecture and helper inventory

DLen remains cursor-gap shaped. It keeps its strict lower-bound cursor split,
predecessor/successor observations, `pendingWasStored` distinction, forward
absorption, and reconstruction local.

| Declaration | Classification | Callers / use | Mathematics versus executable structure | Strength/transport |
| --- | --- | --- | --- | --- |
| `DLenResult` | reconstruction/plumbing | public result of `internalAddDLen`; DLen only | public packaging | exact |
| `DLenRawResult` | reconstruction/plumbing | DLen branch helpers and wrapper; DLen only | proof-free local result | exact |
| `DLenScanResult` | cursor-specific bookkeeping | DLen scan and finish helpers; DLen only | cursor scan state | exact |
| `mkDLenNR` | reconstruction/plumbing | local executable construction and proof simplification; DLen only | representation constructor | local to avoid publishing scaffolding |
| `absorbSuccessorsDLen` | cursor-specific bookkeeping | finish and scan proofs; DLen only | cursor removal sequence | exact; retained |
| `finishDLenScan` | cursor-specific bookkeeping | fresh/predecessor paths and correspondence; DLen only | `pendingWasStored` update ordering | exact; retained |
| `freshInsertDLen` | cursor-specific bookkeeping | raw dispatcher and proofs; DLen only | cursor insertion path | exact; retained |
| `extendPredecessorDLen` | cursor-specific bookkeeping | raw dispatcher and proofs; DLen only | cursor predecessor mutation model | exact; retained |
| `internalAddDLenRaw` | cursor-specific bookkeeping | wrapper and top-level proofs; DLen only | full DLen control flow | exact; retained |
| `absorbSuccessorsDLen_corresponds` | Algo D representation correspondence | finish correspondence; DLen only | exact scan-output equality | one direct client, stable correspondence boundary |
| `finishDLenScan_corresponds` | Algo D representation correspondence | raw correspondence; DLen only | exact scan-output equality after cache-only finish | both projections used |
| `internalAddDLenRaw_corresponds` | Algo D representation correspondence | wrapper construction and public equality; DLen only | exact whole-algorithm range-list equality | exact; retained |
| `absorbSuccessorsDLen_preserves_cached_base` | cursor-specific bookkeeping | fresh and predecessor cardinality proofs; DLen only | exact signed cache invariant for this recursion | reused by both branches |
| `absorbSuccessorsDLen_preserves_endpoints` | cursor-specific bookkeeping | predecessor cardinality proof; DLen only | scan endpoint invariant | one client; needed for final extension math |
| `freshInsertDLen_preserves_cardinality` | cursor-specific bookkeeping | top-level fresh branches; DLen only | branch result cardinality | exact |
| `extendPredecessorDLen_preserves_cardinality` | cursor-specific bookkeeping | top-level predecessor branch; DLen only | branch result cardinality | all decomposition/boundary premises used |
| `internalAddDLenRaw_preserves_cardinality` | reconstruction/plumbing | public cached-length theorem; DLen only | top-level branch composition | one public projection; appropriate private boundary |
| `internalAddDLen` | reconstruction/plumbing | public API | executable wrapper | exact |
| three `internalAddDLen_*` theorems | public guarantees | public API | exact representation, cache correctness, and inherited set semantics | minimal public surface |

The former local `rangesCardinality_append_dlen`, `ofNat_cardinality_nr`, and
`ofNat_extension_cardinality` declarations were redundant stable arithmetic.
They were removed.

No dead executable helper was found in either length implementation. Remaining
one-direct-client private theorems sit at real operation or public-projection
boundaries; removing them would inline distinct proof stages rather than remove
reasoning.

## 4. Shared cardinality vocabulary

The common vocabulary is now:

- `IntRange.cardinality`: inclusive interval cardinality;
- `IntRange.rightExtensionCardinality oldEnd newEnd`: the translated tail
  `[oldEnd, newEnd - 1]` used by production cache updates;
- `NR.cardinality_eq_add_right_extension`: replacing a nonempty interval by a
  same-start interval with a larger end adds exactly that right tail;
- `RangeSetBlaze.rangesCardinality`: represented list cardinality;
- `RangeSetBlaze.rangesCardinality_append`: cardinality additivity across a
  list decomposition;
- `RangeSetBlaze.cardinality`: the record-level represented cardinality.

This vocabulary lets both proofs discuss represented cardinality, affected
ranges, swallowed ranges, and right extension without translating immediately
to endpoint subtraction.

## 5. Shared lemmas extracted

The following shared declarations now live in `Basic.lean`:

1. `IntRange.rightExtensionCardinality` replaces CLen's private
   `extensionCardinality` and names the expression already used directly by
   DLen.
2. `NR.cardinality_eq_add_right_extension` replaces CLen's two overlapping
   right-extension lemmas and DLen's pair of `Int.ofNat` endpoint formulas.
   It is used by both algorithms.
3. `RangeSetBlaze.rangesCardinality_append` replaces the definitionally
   identical private append theorems in CLen and DLen.

This is genuine removal rather than movement: two local append inductions
became one shared induction, while two CLen proofs and two DLen cast formulas
became one domain theorem. Repository-wide active LOC and induction counts
fell despite adding the shared API.

## 6. Things deliberately left local

The following similarities were reviewed and not shared:

- `deleteExtraCLenLoop` versus `absorbSuccessorsDLen`: different executable
  predicates and different Algo C/Algo D representation correspondence;
- the CLen and DLen scan correspondence inductions: each targets a different
  underlying algorithm;
- scan cache invariants: CLen uses `Nat` and must justify truncated
  subtraction, while DLen uses exact `Int` subtraction and cursor-local bases;
- endpoint-preservation theorems: their scan constructors and lower-bound
  assumptions differ;
- fresh/predecessor branch theorems: list-span evidence and cursor-gap evidence
  are different executable proof structure;
- `mkNR` and `mkDLenNR`: sharing would publish a proof constructor merely to
  remove a small local spelling difference;
- `pendingWasStored`, cursor peeks/mutation, predecessor reuse, and branch
  classifiers: all are intentionally D-specific;
- Algo C's strict/non-strict split bridge and exact list reconstruction: all
  are intentionally C-specific.

No generic length-algorithm framework was introduced.

## 7. Nat subtraction and non-underflow

There is one executable `Nat.sub` site in the audited implementations:
`deleteExtraCLenLoop` subtracts `next.val.cardinality` when it swallows the
head of `pending`. (A second textual occurrence appears when that recursive
call is instantiated in the endpoint proof; it is the same operation.)

`deleteExtraCLenLoop_preserves_cached_base` carries the exact invariant

```text
cachedLength = base + rangesCardinality pending.
```

In the merge branch, `pending = next :: tail`, so

```text
cachedLength = base + next.cardinality + rangesCardinality tail.
```

The proof now names the consequence
`hremoved : next.val.cardinality ≤ cachedLength` before using
`Nat.sub_eq_iff_eq_add`. Thus the recursive cache is exactly
`base + rangesCardinality tail`; correctness does not rely on truncated
subtraction.

DLen has no `Nat.sub`. Its cache is a mathematical `Int`, and its only removal
site subtracts `Int.ofNat next.val.cardinality`. The invariant
`absorbSuccessorsDLen_preserves_cached_base` proves the exact analogous
equation. At reachable fresh/predecessor callers, `base` is a sum of
`Int.ofNat` cardinalities, so the cache before removal is nonnegative and
contains the removed contribution. Integer subtraction is non-truncating, and
the equation proves it leaves precisely the untouched base and suffix rather
than a negative or silently clamped cache.

The Lean model does not prove bit-level bounds for every production `SafeLen`;
that bounded-type refinement remains outside both current algorithms.

## 8. Public API review

The algorithm public surfaces remain:

- result type;
- `internalAddCLen` / `internalAddDLen`;
- exact `*_setResult` correspondence;
- `*_cachedLength` correctness;
- inherited `*_toSet` semantics.

Both exact correspondence theorems still state equality of the complete
`RangeSetBlaze` result with Algo C or Algo D, respectively. Neither was
weakened to equality of `toSet`.

The DLen cached-length conclusion now writes the coercion explicitly:

```lean
(internalAddDLen s cachedLength r).cachedLength =
  Int.ofNat (internalAddDLen s cachedLength r).setResult.cardinality
```

This makes its semantic parallel with the Nat-valued CLen theorem visible in
source. It makes explicit what Lean previously inserted by coercion, so the
elaborated proposition is unchanged.

The only new public declarations are the three stable Basic cardinality
declarations listed in section 5. Internal bookkeeping remains private.

## 9. Naming changes

- private `extensionCardinality` moved to shared
  `IntRange.rightExtensionCardinality`;
- private `cardinality_eq_add_extension` and `cardinality_extend_right` were
  replaced by `NR.cardinality_eq_add_right_extension`;
- private `rangesCardinality_append` and
  `rangesCardinality_append_dlen` were replaced by shared
  `RangeSetBlaze.rangesCardinality_append`;
- `finishDeleteExtraCLen_spec` was narrowed and renamed
  `finishDeleteExtraCLen_preserves_cached_base`.

Executable names preserving Rust/Algo C/Algo D correspondence were retained.
No `helper`, `aux`, or remaining length-local `_spec` proof name was introduced.

## 10. Complexity removed versus moved

Removed reasoning:

- one duplicate append induction repository-wide;
- three private CLen proof declarations and three private DLen proof
  declarations;
- DLen's repeated conversion of inclusive cardinalities to endpoint
  subtraction and back;
- unused correspondence projections from the CLen finish theorem;
- unused canonicality/no-gap premises and the associated top-level CLen
  proposition transport;
- nine CLen and four DLen local `omega` occurrences in the isolated length
  sections.

Moved reasoning:

- the single right-extension cardinality proof and single append proof now
  live in `Basic.lean`, adding 27 active lines there.

The remaining separate scan inductions prove different dimensions of different
executables. Combining them would enlarge induction state and couple exact
representation correspondence to cache arithmetic, so they were retained.

## 11. Metrics

All values use `scripts/phase0_metrics.py` schema/collector v3. CLen and DLen
rows are reproducible slices beginning at their module-section markers; the
file and repository rows are the collector's ordinary outputs. Counts are a
dashboard, not a composite score.

### Isolated length sections

| Metric | CLen before | CLen after | DLen before | DLen after |
| --- | ---: | ---: | ---: | ---: |
| Physical LOC | 685 | 581 | 552 | 504 |
| Active LOC | 601 | 508 | 498 | 453 |
| Definitions | 7 | 6 | 7 | 7 |
| Public theorems | 3 | 3 | 3 | 3 |
| Private theorems/lemmas | 12 | 9 | 11 | 8 |
| `induction` | 4 | 3 | 4 | 3 |
| `cases` | 1 | 0 | 6 | 6 |
| `by_cases` | 12 | 12 | 10 | 10 |
| `have` | 70 | 55 | 54 | 39 |
| `rw` | 33 | 24 | 21 | 19 |
| `simp` | 55 | 49 | 42 | 41 |
| `simpa` | 31 | 27 | 32 | 27 |
| `omega` | 17 | 8 | 10 | 6 |
| `linarith` | 0 | 0 | 0 | 0 |

Qualitative one-direct-client proof boundaries after cleanup are three in CLen
and four in DLen; each is an operation invariant, exact-correspondence
projection, or public theorem boundary, not proposition-only transport.
Duplicate append recursions fell from two to zero; one shared Basic induction
remains. The algorithm-specific scan recursions remain separate.

### Files and repository

| Metric | Before | After |
| --- | ---: | ---: |
| Algo C physical / active LOC | 1,501 / 1,277 | 1,397 / 1,184 |
| Algo D physical / active LOC | 1,002 / 867 | 954 / 822 |
| Basic physical / active LOC | 621 / 446 | 655 / 473 |
| Repository physical LOC | 6,730 | 6,612 |
| Repository active LOC | 5,892 | 5,781 |
| Repository definitions/abbreviations | 100 | 100 |
| Repository public lemmas/theorems | 53 | 55 |
| Repository private lemmas/theorems | 94 | 88 |
| Repository `induction` / `cases` / `by_cases` | 31 / 48 / 126 | 30 / 47 / 126 |
| Repository `have` / `rw` | 789 / 166 | 763 / 159 |
| Repository `simp` / `simpa` | 464 / 298 | 461 / 289 |
| Repository `omega` / `linarith` | 138 / 4 | 130 / 4 |

The final source manifest is
`bd1fc4036f83380d5455b3712f898fa8ddea76a59a859e14b1d2786bf6706e4d`.

## 12. Readiness for CMapLen

The shared append and right-extension facts are directly reusable if CMapLen's
cache counts represented keys. CMapLen will additionally need cardinality
facts for predecessor residuals and overwritten/removed run pieces. Those
facts should be extracted only after CMapLen states the concrete mathematics;
the set-length cleanup does not justify adding them speculatively.

## 13. Readiness for DMapLen

DMapLen can reuse the same cardinality vocabulary, but its cursor ownership,
value-sensitive coalescing, residual runs, and mutation order should remain
local. A likely genuine gap is a cardinality decomposition theorem for the
specific left/right residuals produced by map overwrite. No current CLen/DLen
statement justifies creating that theorem yet.

## 14. Remaining cleanup opportunities

- A bounded refinement from mathematical `Nat`/`Int` cache correctness to each
  Rust `SafeLen` representation would strengthen machine-level correspondence,
  but is not a set-length proof cleanup.
- If a later algorithm needs equality of cardinalities from equal canonical
  representations, a canonical uniqueness/cardinality bridge may become
  useful. It has no second current consumer.
- The remaining scan correspondence, endpoint, and cache inductions should be
  reconsidered only if a concrete new client needs the same combined contract.

No remaining set-length API inconsistency blocks map-length work.

## 15. Verification

- direct compilation of `RangeSetBlaze/AlgoC.lean`: passed, zero warnings;
- direct compilation of `RangeSetBlaze/AlgoD.lean`: passed, zero warnings;
- direct compilation of `RangeSetBlaze.lean`: passed, zero warnings;
- full `lake build`: passed, zero warnings (the executable's expected `#eval`
  output was informational);
- v3 metric regression tests: 6 passed;
- `git diff --check`: passed;
- forbidden Lean-source scan: no `sorry`, `sorryAx`, `admit`, source `axiom`,
  `unsafe`, or `implemented_by`;
- all six requested public theorems depend on exactly `propext`,
  `Classical.choice`, and `Quot.sound`.

No files were staged, committed, pushed, or tagged.
