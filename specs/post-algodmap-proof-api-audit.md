# Post-AlgoDMap proof API audit

Date: 2026-09-12

## Starting state

The cleanup started at `50a50d9dc2d5f2e7745798c6a2114639d052c648` on branch
`main`. The worktree was clean. AlgoDMap was already complete: its public
surface was `internalAddDMap` and `internalAddDMap_toFunction`, with the
cursor model and all proof scaffolding private. The executable definitions
were not changed by this cleanup. Existing Rust/CI work was outside scope and
was preserved.

The v3 collector was used for both measurements. The starting AlgoDMap was
1,326 physical LOC and 1,256 active LOC; the repository was 5,475 physical
and 4,785 active LOC.

## Local AlgoDMap cleanup

The completed scan invariant was retained as one joint recursion:
`scanForward_preserves_canonical_and_overwrite` proves canonicality and exact
overwrite denotation together. `scanForward_preserves_left_boundary` remains
separate because it is a cross-boundary ordering invariant, not a second
denotational result. Combining it would mix list ordering with pointwise map
semantics and make the induction less readable.

Two unused private executable helpers were removed:

- `insertBefore`
- `replaceStoredPredecessor`

The following private proof declarations were renamed to describe their
mathematical contracts:

| Former declaration | Final declaration |
| --- | --- |
| `strict_start_split_suffix_lower_bound` | `strictStartSuffix_lowerBound` |
| `lowerBoundGap_spec` | `lowerBoundGap_decomposition` |
| `cursor_predecessor_mutation_spec` | `predecessorTrim_preserves_toFunction` |
| `exactCover_toFunction` | `sameValueExactCover_toFunction` |
| `prepend_left_of_overwrite` | `prependLeft_preserves_overwrite` |
| `mergePredecessor_toFunction` | `predecessorMerge_preserves_overwrite` |
| `predecessor_split_toFunction` | `predecessorSplit_preserves_overwrite` |
| `trimPredecessor_toFunction` | `predecessorTrim_preserves_overwrite` |
| `insertAtGap_preserves_canonical_and_overwrite` | `gapInsertion_preserves_canonical_and_overwrite` |

The no-gap contract for predecessor trimming was preserved. The classifier's
actual-overlap fact remains local to the executable branch proof; it was not
turned into a stronger or public mutation theorem.

## Helper inventory and complexity review

The 19 private proof declarations fall into these groups:

- stable domain mathematics: merge, exact cover, covered-run deletion, right
  residual denotation, predecessor residual denotation, and overwrite
  reconstruction;
- cursor-local semantic invariants: scan denotation/canonicality, scan left
  boundary, unchanged-result facts, and gap insertion;
- representation/list plumbing: gap decomposition and strict suffix lower
  bound;
- proposition transport: the lower-bound and below-boundary function facts.

No helper was promoted to the public API. The two dead list constructors were
the only declarations with no callers. The repeated `Run.before` construction
inside scan branches carries genuinely different boundary hypotheses, so a
generic wrapper would have moved proof detail rather than removed it.

## Complexity removed versus moved

The cleanup removed dead definitions and their list plumbing. It did not move
proof complexity into Basic. It did not reduce induction, branching,
intermediate facts, or automation: those counts are unchanged. This is an
intentional readability cleanup, not LOC golf.

## Cross-algorithm findings

AlgoAMap, AlgoCMap, and AlgoDMap already share the Basic vocabulary `Run`,
`Run.before`, `Canonical`, `runsToFunction`, `overwrite`, and append
reconstruction. CMap and DMap have similar semantic lemmas for merge, exact
cover, covered deletion, and right residuals, but their local executable
operations and scan states differ. A shared theorem would need parameters or
projections for those private definitions and would preserve essentially the
same case reasoning.

The predecessor residual theorems also differ in result shape and control
flow: AMap uses filter-map residual lists, CMap uses a conditional suffix, and
DMap uses explicit cursor actions and residual options. No Basic theorem was
added. The strict-start suffix theorem is similarly duplicated only at the
labeled-run/list representation boundary; the existing unlabeled `NR` fact in
Basic cannot be reused without span/map adapters. That would move mechanics,
not remove them.

Basic.lean already owns the stable shared layer: interval/run semantics,
canonical ordering, denotation, append reconstruction, overwrite locality,
mergeability, and generic boundary facts. Cursor gaps, scan state, classifier
details, and mutation sequencing correctly remain algorithm-local.

## Intentionally local theorem families

The following were considered but deliberately not shared:

- forward scan recursions, because CMap and DMap have different executable
  state and stopping conditions;
- preserved-left-boundary recursions, because each is coupled to its scan's
  output representation;
- predecessor split/trim/merge contracts, because their list result shapes
  are different;
- strict suffix lower-bound proofs, because the labeled-run span theorem and
  the `NR` theorem do not share a useful direct interface;
- cursor predecessor lookup, reconstruction, and exact-start fast paths.

No cached-length work or global canonical-representation uniqueness work was
performed.

## Public API review and naming

The public AlgoDMap API is unchanged and remains appropriately small. Private
names now use `preserves_*`, `decomposition`, `predecessor`, `residual`, and
`boundary` vocabulary. The executable names retain their Rust-corresponding
cursor/scan terminology. Module organization remains the intentional flat
`AlgoX` / `AlgoXMap` layout.

The API choices preserve future uniqueness work: canonicality and denotation
remain explicit separate components of list-level contracts, while no
algorithm-specific cursor state leaks into Basic.

## Metrics

### AlgoDMap local cleanup

| Metric | Before | After |
| --- | ---: | ---: |
| Physical LOC | 1,326 | 1,318 |
| Active LOC | 1,256 | 1,250 |
| Blank LOC | 44 | 42 |
| Comment-only LOC | 26 | 26 |
| Definitions/abbrevs | 14 | 12 |
| Lemma/theorem declarations | 20 | 20 |
| Private lemma/theorem declarations | 19 | 19 |
| `induction` / `cases` / `by_cases` | 6 / 7 / 42 | 6 / 7 / 42 |
| `have` / `rw` | 173 / 22 | 173 / 22 |
| `simp` / `simpa` | 96 / 78 | 96 / 78 |
| `omega` / `linarith` | 45 / 0 | 45 / 0 |
| Recursive scan proofs | 6 induction sites overall | 6 induction sites overall |
| One-use helpers | qualitative review only | qualitative review only |
| Proof-plumbing helpers | none removed beyond dead defs | none newly added |

### Whole repository

Only AlgoDMap changed, so cross-algorithm source metrics are unchanged.

| Metric | Before | After |
| --- | ---: | ---: |
| Physical LOC | 5,475 | 5,467 |
| Active LOC | 4,785 | 4,779 |
| Blank LOC | 332 | 330 |
| Comment-only LOC | 358 | 358 |
| Definitions/abbrevs | 85 | 83 |
| Lemma/theorem declarations | 104 | 104 |
| Private lemma/theorem declarations | 69 | 69 |
| `induction` / `cases` / `by_cases` | 23 / 41 / 104 | 23 / 41 / 104 |
| `have` / `rw` | 665 / 112 | 665 / 112 |
| `simp` / `simpa` | 361 / 235 | 361 / 235 |
| `omega` / `linarith` | 111 / 4 | 111 / 4 |

The metric artifacts were generated with `scripts/phase0_metrics.py` v3;
the before/after JSON snapshots were kept in `/tmp` during this session.

## Verification

- `lake build`: passed, zero warnings.
- `lake env lean RangeSetBlaze/AlgoDMap.lean`: passed.
- v3 metric regression tests: 6 passed.
- `git diff --check`: passed.
- forbidden-source scan for active `sorry`, `admit`, `axiom`, `unsafe`,
  `implemented_by`, and `sorryAx`: no matches.
- correctness endpoint axioms for AlgoC, AlgoAMap, AlgoCMap, and AlgoDMap:
  exactly `propext`, `Classical.choice`, and `Quot.sound` in each case.

## Remaining opportunities and recommendation

1. Keep the current local scan proofs stable while adding any new algorithm;
   compare its semantic contracts against CMap/DMap before extracting.
2. Consider a focused generic residual theorem only if a third map algorithm
   produces the same result shape; current two-way similarity is insufficient.
3. Design global canonical uniqueness after the final representation API is
   settled.
4. Add cached length in its own dedicated pass after the API stabilizes.

The next project should be cached-length work. The present cleanup exposed no
architectural problem and no proof-API inconsistency that justifies delaying
it.
