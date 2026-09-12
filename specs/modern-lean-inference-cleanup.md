# Modern Lean and inference cleanup

Date: 2026-09-12

## 1. Starting state

The pass started from clean `main`, synchronized with `origin/main`, at commit
`a64e3600dd195b59c9b5cada1bd432993d4f01ea` (`Share cardinality proofs across
CLen and DLen`) and tree `0e27c983cf85e684379c4979c9ee2c4c50332f31`.
The v3 baseline source manifest was
`bd1fc4036f83380d5455b3712f898fa8ddea76a59a859e14b1d2786bf6706e4d`.

The worktree was clean before inventory. Running the metric collector caused
Python to refresh its tracked bytecode cache; that generated change was
restored and is not part of this pass. No changes were staged, committed,
pushed, or tagged.

Three Luna tasks ran in parallel with the proof review:

- a complete v3 baseline and mechanical-token inventory;
- a project/Mathlib/Std/Batteries lemma search;
- a one-use-helper, explicit-argument, and proposition-transport audit.

The inventory identified the largest concentrations in Algo C, Algo DMap,
Algo CMap, Algo B, Algo D, and Algo AMap. The library search confirmed that
the repository already uses the relevant split, last-element, append,
pairwise, residual-list, cardinality, cast, and min/max vocabulary. It found no
external theorem that should replace the map scan contracts or the
representation-specific strict-suffix proofs.

## 2. Candidate inventory

The most frequent baseline proof signals were 763 `have`, 159 `rw`, 126
`by_cases`, 47 `cases`, and 30 `induction` occurrences. The largest per-module
`have` counts were Algo C 178, Algo DMap 173, Algo CMap 127, Algo B 102, Algo D
84, and Algo AMap 42.

The audit found 42 one-use private proof declarations. Most state genuine
semantic contracts: residual denotation, scan preservation, ordering, or
cached-cardinality behavior. Five were pure local evaluation or
cross-boundary transport and were removable. Repeated patterns included 47
`List.pairwise_append` uses, 35 `getLast?` uses, 53 `dropLast` uses, 45
qualified `List.span` uses, and duplicated map residual/scan families.

## 3. Ranked opportunities

### A. High-value inference jumps

1. Replace the manual four-way endpoint proof of
   `IntRange.mergeRange_toSet_of_noGap` with interval-membership
   simplification and focused Presburger arithmetic.
2. Consume the complete result of `List.pairwise_append` once in Algo B rather
   than reconstructing three cross-boundary facts in one-use lemmas.
3. Project Algo A's existing dependent `insert` contract directly in
   `internalAddA_toSet` instead of rebuilding its record and set view through
   several intermediate equalities.
4. Delete Algo C's two one-use scan-evaluation wrappers and simplify the
   recursive step at the actual use sites.
5. Reuse a single pairwise decomposition in Algo D's predecessor-reuse proof.
6. Let Algo B infer the dependent split arguments already determined by its
   witness and shorten the final union reconstruction.

### B. Medium-value cleanup

- Simplify `NR.disjoint_of_before`, `NR.mergeable_glue_left`,
  `NR.glue_sets`, `NR.before_glue`, and `NR.before_trans` using direct theorem
  application or narrowly scoped `omega`.
- Destructure Algo AMap's recursive coalescing contract in one step.
- Avoid repeating the same `rangesCardinality_cons` rewrite in CLen's natural
  subtraction proof.

### C. Deliberately skipped cosmetic changes

- Converting the two-line CLen/DLen public result projections to `simpa` did
  not elaborate cleanly through proof-bearing structure equality and would
  not remove mathematical reasoning.
- Replacing DLen's named `Int.ofNat` addition fact with a broad simplifier call
  made coercion normalization less predictable; the explicit fact was kept.
- Changing isolated `exact`/`rw` syntax, or adding large `simp` contexts to
  save one line, was rejected.

## 4. Implemented inference jumps

Seven high-value jumps were implemented:

1. `mergeRange_toSet_of_noGap` now exposes membership with `simp only` and
   closes the coherent endpoint problem with `omega`; the manual min/max case
   tree disappeared.
2. Algo A's correctness theorem now destructures the existing insertion
   result once and applies its set projection directly.
3. Algo B obtains prefix, suffix, and cross-boundary ordering facts from one
   pairwise append decomposition, eliminating three local proof interfaces.
4. Algo B's correctness theorem now reuses `buildSplit_sets` and the split
   equation directly, with associative-commutative normalization confined to
   the final union equality.
5. Algo C performs its two scan equations directly at their callers; their
   one-use simp wrappers disappeared.
6. Algo D decomposes the source pairwise proof once, then reuses the left,
   right, and predecessor boundary projections.
7. The shared NR endpoint helpers now use direct theorem application and
   focused arithmetic rather than reconstructing min/max and interval facts.

The pass also removed nine named theorem arguments in Algo B where the split
witness and expected result determine them, and removed one explicit
`show NR.startsBefore ...` transport in Algo C. Algo AMap now obtains both
recursive contract fields at once. CLen performs one cardinality rewrite
instead of two in its subtraction branch.

## 5. Helpers removed

Exactly five private proof helpers were removed:

- `split_before_before_touch`
- `split_before_before_after`
- `split_touch_before_after`
- `deleteExtraNRs_loop_cons_merge`
- `deleteExtraNRs_loop_cons_noMerge`

The first three duplicated projections already returned by
`List.pairwise_append`. The last two only restated one evaluation step of
`deleteExtraNRs_loop` and each had one caller.

## 6. Library and shared theorems reused

No new import was needed. The main substitutions were:

- Lean/Std `List.pairwise_append`, now used once to supply all Algo B and Algo
  D ordering projections instead of local transport lemmas;
- core `lt_min`, now applied directly by `NR.before_glue`;
- the existing project theorem `IntRange.mergeRange_toSet_of_noGap`, now
  applied definitionally by `NR.glue_sets` without explicit endpoint/value
  arguments;
- the existing project theorem
  `NR.mergeable_of_startsBefore_of_not_before`, now applied without a
  proposition-shaping `show` term;
- existing `rangesToSet_append`, split equations, and the Algo A insertion
  contract in the shortened public correctness proofs.

The library search also considered `List.getLast?_eq_some_iff`,
`List.dropLast_append_getLast?`, `List.mem_takeWhile_imp`, the take/drop-while
append theorems, `List.filterMap_append`, `Option.toList` simp theorems,
`Nat.sub_eq_iff_eq_add`, and the standard cast/min/max facts. Current uses were
retained when these theorems would only move representation details or make a
one-use proof less readable.

## 7. Places intentionally left explicit

- CMap and DMap keep separate scan, residual, exact-cover, and lower-bound
  contracts. Their executable states and result shapes differ, and the prior
  audits correctly identify them as semantic boundaries rather than duplicate
  transport.
- Algo C's span, predecessor, and joint order/union contracts remain explicit.
  They mirror the proof sketch's split/scan invariant and are not accidental
  scaffolding.
- CLen and DLen retain named natural-subtraction and integer-cast facts at the
  points where underflow or coercion is mathematically relevant.
- Explicit predicate/list arguments on several take/drop-while theorems remain
  because they improve error localization around dependent splits.
- The map merge and residual proofs keep branch-local interval facts. Replacing
  them with broad `simp_all` or large-context `omega` calls was shorter but
  less explanatory.
- Regression, root exports, `Main`, Algo CMap, and Algo DMap had no
  high-confidence inference cleanup worth changing.

## 8. Module-by-module effects

| Module | Physical LOC | Active LOC | Main effect |
| --- | ---: | ---: | --- |
| Basic | 655 → 569 | 473 → 387 | Direct interval/ordering inference; no API changes |
| Algo A | 156 → 136 | 138 → 121 | Direct use of the private insertion contract |
| Algo B | 585 → 489 | 533 → 443 | Three helpers removed; one pairwise decomposition reused |
| Algo C / CLen | 1,397 → 1,375 | 1,184 → 1,164 | Two scan wrappers removed; small CLen rewrite cleanup |
| Algo D / DLen | 954 → 951 | 822 → 819 | One source pairwise decomposition reused |
| Algo AMap | 437 → 435 | 389 → 387 | Recursive joint contract destructured once |
| Algo CMap | 940 → 940 | 862 → 862 | Inspected; intentionally unchanged |
| Algo DMap | 1,318 → 1,318 | 1,250 → 1,250 | Inspected; intentionally unchanged |
| AlgoCLen compatibility module | 3 → 3 | 1 → 1 | Import-only; unchanged |
| Regression/root/Main | unchanged | unchanged | No proof scaffolding candidates |

No executable definition body changed. No public theorem was renamed, moved,
added, or removed.

## 9. V3 metrics before and after

The baseline was collected from exact git ref `HEAD`; the endpoint was
collected from the working tree with the same v3 collector, whose SHA-256 is
`a07fc3573ed0134219b1d539c2684d717707ab7360a8e0ba97602ef95549e048`.
The endpoint Lean-source manifest is
`2fb3e5de9cfc9416c89ee0c87c19f620f2e7434529a141c3948e2776e6647af0`.

| Repository metric | Before | After | Delta |
| --- | ---: | ---: | ---: |
| Physical LOC | 6,612 | 6,383 | -229 |
| Nonblank LOC | 6,224 | 6,000 | -224 |
| Comment-only LOC | 443 | 437 | -6 |
| Active-code LOC | 5,781 | 5,563 | -218 |
| Definitions/abbreviations | 100 | 100 | 0 |
| Lemma/theorem declarations | 143 | 138 | -5 |
| Public lemma/theorem declarations | 55 | 55 | 0 |
| Private lemma/theorem declarations | 88 | 83 | -5 |
| `induction` | 30 | 30 | 0 |
| `cases` | 47 | 42 | -5 |
| `by_cases` | 126 | 124 | -2 |
| `have` | 763 | 714 | -49 |
| `show` | 21 | 20 | -1 |
| `suffices` | 0 | 0 | 0 |
| `rw` | 159 | 158 | -1 |
| `simp` | 461 | 455 | -6 |
| `simpa` | 289 | 273 | -16 |
| `omega` | 130 | 134 | +4 |
| `linarith` | 4 | 1 | -3 |
| `grind` | 0 | 0 | 0 |
| `pairwise_append` | 47 | 40 | -7 |
| `List.span` / `takeWhile` / `dropWhile` | 45 / 43 / 15 | 45 / 43 / 15 | 0 / 0 / 0 |
| `getLast?` / `dropLast` / `Sublist` | 35 / 53 / 2 | 35 / 53 / 2 | 0 / 0 / 0 |

The increases in focused `omega` calls correspond to deletion of manual
endpoint case analysis. They are not a composite quality score. Active proof
text, branching, plumbing, and private transport declarations all decreased;
no complexity was moved into a new module or declaration.

## 10. Verification

- Direct compilation passed for every touched module: Basic, Algo A, Algo B,
  Algo C, Algo D, and Algo AMap.
- Direct root compilation of `RangeSetBlaze.lean` passed.
- Full `lake build` passed all 1,886 jobs with zero warnings.
- All six v3 metric regression tests passed.
- `git diff --check` passed.
- The active Lean-source scan found no `sorry`, `sorryAx`, `admit`, source
  `axiom`, `unsafe`, or `implemented_by`.
- The source diff contains no changed executable definition body.
- The major set, map, CLen, and DLen correctness endpoints depend exactly on
  `propext`, `Classical.choice`, and `Quot.sound`.

## 11. Remaining candidates and CMapLen readiness

The remaining high token counts in Algo CMap and Algo DMap reflect their
branch-rich executable scan states and semantic overwrite contracts. A future
cleanup should be triggered by a concrete new shared result shape, not by the
counts alone. Algo C's remaining span vocabulary likewise follows the frozen
production-shaped architecture.

The repository is ready for CMapLen. The shared cardinality vocabulary is in
place, CLen/DLen arithmetic was reviewed, set and map correctness endpoints
remain stable, and this pass exposed no missing shared theorem or architectural
problem that should block cached map length work.

Suggested commit message:

`Modernize Lean proof inference across range algorithms`

Alternative split messages, if separate commits are preferred:

- `Simplify shared interval and Algo A proofs`
- `Remove redundant Algo B and Algo C proof helpers`
- `Reuse pairwise inference in Algo D and Algo AMap`

### Recommendation A: Modern Lean/inference cleanup is complete; start CMapLen
