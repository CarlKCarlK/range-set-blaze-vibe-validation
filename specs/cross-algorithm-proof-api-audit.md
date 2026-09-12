# Cross-algorithm proof API audit

Date: 2026-09-11

This audit compares the proof-facing API for set Algo A and Algo C, map
AlgoAMap and AlgoCMap, and the stable concepts likely to matter to a future
cursor-based AlgoDMap. It does not implement AlgoDMap or add cached lengths.

## Starting point and algorithm inventory

The audit began from a clean `main` at
`3c6600fcec0e2ee28df67a2b83461882c2c9f51d` (`Clean up and document AlgoCMap
correctness proof`).

- Set Algo A is a direct fold over canonical range insertion. Its public
  endpoint is `RangeSetBlaze.ofListA_eq`.
- Set Algo C separates around the insertion point, merges a forward run, and
  reconstructs the represented set. Its public endpoint is
  `RangeSetBlaze.ofListC_eq`.
- AlgoAMap is a list-oriented reference algorithm using predecessor residuals,
  insertion, coalescing, and overwrite semantics. Its public endpoint is
  `RangeMapBlaze.ofListAMap_eq`.
- AlgoCMap implements the Rust-shaped predecessor classification and forward
  scan over runs. Its public endpoint is `RangeMapBlaze.ofListCMap_eq`.
- The anticipated AlgoDMap is the mutable cursor form of the map operation. It
  should reuse the domain vocabulary, but its cursor ownership and mutation
  invariants should remain local until there is executable Lean code to prove.

Algo B, set Algo D, and regression code were changed only where the shared
`RangeSetBlaze` record field required migration.

## Shared semantic vocabulary

The stable vocabulary is:

| Role | Set representation | Map representation | Classification |
| --- | --- | --- | --- |
| Atomic object | `NR` | `Run` | Analogous, legitimately different |
| Strict separation | `NR.before` | `Run.disjointBefore` | Same ordering idea; map also needs value-sensitive canonicality |
| Canonical sequence | `Pairwise NR.before` | `Pairwise Run.before` | Same API word, different relation |
| Denotation | `rangesToSet` / `RangeSetBlaze.toSet` | `runsToFunction` / `RangeMapBlaze.toFunction` | Parallel naming style |
| Combination | `NR.mergeable`, `NR.glue` | equal-valued touching and run coalescing | Analogous, mathematically different |
| Update semantics | union | overwrite | Intentionally different |
| Reconstruction | set append/union facts | `runsToFunction_append` and locality facts | Parallel theorem family |
| Boundary reasoning | predecessor/suffix ordering and containment | predecessor/suffix ordering and residual cuts | Partly shared shape, different payload |
| Forward processing | merge/delete-extra normalization | value-sensitive overwrite scan | Similar control flow, not one theorem |

`NR.before` and `Run.before` should not be collapsed. For ranges, canonicality
requires a genuine gap. For runs, disjoint touching runs are canonical when
their values differ, while equal-valued touching runs must coalesce. Likewise,
set union and map overwrite are not cosmetic variants of one semantic
operation.

## Module ownership

`Basic.lean` has the right responsibility. It owns domain and reusable
representation facts: integer ranges, `NR`, `Run`, the two blaze records,
denotations, canonical relations, append laws, overwrite laws, stable ordering
and containment lemmas, and small glue/boundary facts.

Algorithm modules should continue to own scans, predecessor preparation,
algorithm-specific residual constructors, local decomposition witnesses,
normalization loops, and their preservation contracts. No module split is
justified: moving these helpers would expose control-flow proof structure as a
domain API.

One possible future gap is a shared theorem family for predecessor overlap
residuals. AlgoAMap and AlgoCMap currently package different preconditions and
result shapes, and a cursor implementation may add a third shape. Extraction
should wait until AlgoDMap supplies a genuine second use of exactly the same
mathematical statement.

## Public API review

Before and after, the library has 42 public and 52 private lemmas/theorems.
The count is unchanged; the improvement is vocabulary rather than surface-area
growth.

- The public record invariant `RangeSetBlaze.ok` is now
  `RangeSetBlaze.canonical`. This is a breaking, deliberate domain rename.
- The four major correctness endpoints remain public and qualified by their
  namespaces. They were not added as unqualified root exports because that is
  an export-policy choice, not a proof-architecture requirement.
- Public low-call-count facts in `Basic.lean` were retained when they name
  stable mathematical concepts: range emptiness/denotation, ordering,
  mergeability/glue, containment, run ordering, and map support. Their present
  caller count is not a reason to hide a coherent domain theorem.
- Algorithm preservation contracts remain private. Their names are semantic,
  but their statements expose the proof structure of one executable algorithm.

The call-site inventory found 16 public declarations with at most one local
algorithm consumer. Four are final correctness endpoints and twelve are stable
domain facts; none is accidental public scaffolding. There were no dead
top-level declarations and no one-use helper whose sole purpose was proposition
transport.

## Naming changes

| Old | New | Reason |
| --- | --- | --- |
| `RangeSetBlaze.ok` | `RangeSetBlaze.canonical` | Names the library-wide record invariant |
| `coalesceRuns_spec` | `coalesceRuns_preserves_canonical_and_function` | States both preserved properties |
| `scanForward_spec` | `scanForward_preserves_canonical_and_function` | Makes the forward-scan contract discoverable |
| `internalAddCMapRuns_spec` | `internalAddCMapRuns_preserves_canonical_and_overwrite` | Names the algorithm's two proof obligations |
| `merge_step_sets` | `mergeForward_toSet` | Replaces proof-mechanical wording with denotational meaning |
| `strictStartSuffix_lower_bound` | `strict_start_split_suffix_lower_bound` | Aligns with the existing strict-start split vocabulary |
| local `ok`/`hok` names | `canonical`/`hcanonical` forms | Keeps proof prose and record vocabulary aligned |

`deleteExtraNRs_loop`, `internalAdd2NRs`, and similar set Algo C executable
names were retained. They preserve useful correspondence with the production
algorithm, and renaming them would not make the theorem map materially clearer.
The theorems surrounding executable helpers may still use semantic names.

The historical AlgoCMap milestone document was left historical. The current
human-readable proof sketch was updated to the current theorem map.

No declaration was removed, privatized, moved, or newly exported. That is an
intentional audit result: the low-use public items are reusable mathematics,
whereas the algorithm-specific scaffolding was already private.

## Shared theorem families

The inventory identifies eight cross-module bridge families:

1. strict-start split suffix lower bounds;
2. containment of ordered earlier ranges;
3. `NR.before` transitivity and endpoint consequences;
4. mergeability and glue laws;
5. run ordering and canonicality;
6. range/run denotation and append reconstruction;
7. function overwrite, empty overwrite, and locality;
8. final fold induction from a single-update semantic theorem.

These bridges are already in `Basic.lean` when their statements are independent
of an algorithm. The two strict-start suffix declarations—one over `NR`, one
over projected `Run` bounds—remain separate because a generic abstraction
would require span/projection machinery used nowhere else.

## Intentionally local theorem families

- Algo C's delete-extra loop, merge-forward decomposition, and reconstruction;
- AlgoAMap's left/right residual construction and trim/insert/coalesce stages;
- AlgoCMap's predecessor action classification, replacement, forward scan, and
  left-boundary proof;
- the separate canonicality and semantic inductions over `scanForward`.

The last pair is the only duplicate recursion over exactly the same executable
operation. Combining it would couple two already-readable invariants and
increase induction hypotheses and branch state; it was therefore left alone.
Across algorithms, superficially similar recursive proofs operate on different
relations and denotations and are shared control flow rather than shared
mathematics.

## Ranked cleanup opportunities

| Rank | Declarations / algorithms | Decision and benefit | Reduction / risk | AlgoDMap value |
| ---: | --- | --- | --- | --- |
| 1 | `RangeSetBlaze.ok`, all set algorithms | **Implemented:** rename to `canonical`; establishes precise record vocabulary | Vocabulary only; low risk | High |
| 2 | AlgoAMap/AlgoCMap `_spec` preservation contracts | **Implemented:** semantic theorem names expose the proof architecture | No proof reduction; low risk | High |
| 3 | Algo C `merge_step_sets` | **Implemented:** name and orient it as `mergeForward_toSet` | Two caller simplifications; low risk | Low |
| 4 | Basic/AlgoCMap strict-start suffix names | **Implemented:** normalize vocabulary while retaining distinct statements | Vocabulary only; low risk | Medium |
| 5 | AlgoCMap scan canonicality and left-boundary inductions | **Deferred:** consider combining only if cursor proof needs a joint invariant | Possible one traversal; medium/high risk | Medium |
| 6 | AlgoAMap/AlgoCMap predecessor residual facts | **Deferred:** extract only after an identical AlgoDMap statement appears | Potential small reuse; medium risk | High |
| 7 | `NR` and `Run` suffix lower-bound lemmas | **Deferred:** generic span abstraction costs more than two short theorems | Likely negative reduction; medium risk | Low/medium |
| 8 | Four final correctness theorem root exports | **Deferred:** decide with public import/export policy | No proof reduction; low risk | Low |
| 9 | Public zero/one-use facts in `Basic.lean` | **Rejected:** keep stable mathematical concepts public | Hiding saves no proof; medium API cost | Medium |
| 10 | Historical executable names and forced set/map residual symmetry | **Rejected:** production correspondence and mathematical differences dominate cosmetic consistency | Broad churn; high risk | Low |

## AlgoDMap readiness

Already supported:

- `Run`, value-sensitive `Run.before`, and `Run.disjointBefore`;
- canonical prefix/suffix vocabulary;
- `runsToFunction`, append reconstruction, locality, and overwrite semantics;
- range and run boundary reasoning;
- a semantic model for residuals and forward normalization demonstrated by
  AlgoAMap and AlgoCMap.

The one obvious candidate gap is a representation-neutral residual theorem for
splitting an overlapped predecessor. It should not be added yet because the two
current algorithms do not share one result representation and the cursor proof
may prefer a mutation-local statement.

Cursor ownership, current-position validity, mutation preservation, cached
length, and iterator restoration are speculative or cursor-specific. They
belong in AlgoDMap until repeated use proves otherwise.

## Metrics

The v3 collector and regression tests were used. Tactic counts are lexical
counts from that collector.

### Repository

| Metric | Before | After |
| --- | ---: | ---: |
| Physical Lean LOC | 4,139 | 4,150 |
| Active Lean LOC | 3,519 | 3,530 |
| Definitions (`def` + `abbrev`) | 72 | 72 |
| Public lemmas/theorems | 42 | 42 |
| Private lemmas/theorems | 52 | 52 |
| Compiler warnings | 0 | 0 |

The eleven-line increase is wrapping required by longer semantic names, not
new proof structure. Declaration and tactic counts did not increase.

### Algorithms

| Module | Active LOC before/after | `induction` | `cases` | `by_cases` | `have` | `rw` | `simp` | `simpa` | `omega` | `linarith` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| AlgoA | 138 / 138 | 0 | 0 | 1 | 17 | 1 | 8 | 10 | 0 | 0 |
| AlgoC | 679 / 679 | 1 | 4 | 4 | 123 | 36 | 36 | 27 | 4 | 0 |
| AlgoAMap | 388 / 389 | 3 | 4 | 15 | 42 | 8 | 33 | 6 | 27 | 0 |
| AlgoCMap | 852 / 862 | 5 | 0 | 33 | 127 | 13 | 94 | 54 | 33 | 0 |

### API architecture

| Metric | Before | After | Interpretation |
| --- | ---: | ---: | --- |
| Shared concepts with multiple/inconsistent names | 2 | 0 | canonical invariant and strict-start suffix vocabulary normalized |
| Generic `_spec` proof contracts in audited algorithms | 3 | 0 | semantic preservation names used |
| Public declarations with at most one local consumer | 16 | 16 | 4 endpoints plus 12 retained domain facts |
| One-use proof-plumbing helpers | 0 | 0 | none found after semantic classification |
| Duplicate recursive proofs over the same operation | 1 pair | 1 pair | intentionally separate AlgoCMap invariants |
| Cross-module bridge theorem families | 8 | 8 | already owned at the appropriate shared level |
| Local aliases for shared vocabulary | 0 | 0 | no alias layer needed for the breaking rename |

## Proof-sketch consistency and deferred work

The current set and map sketches now use `canonical` for the record invariant,
and the current AlgoCMap theorem map names the properties proved by each scan
contract. Both sketches expose the same high-level sequence—canonical prefix,
predecessor treatment, forward processing, suffix boundary, and denotational
reconstruction—while retaining union versus overwrite and gap versus
value-sensitive touching distinctions.

Deferred work is deliberately narrow: revisit residual theorem ownership when
AlgoDMap provides an actual second statement; decide root re-exports under a
separate public import policy; and combine AlgoCMap recursive invariants only if
the cursor proof demonstrates a concrete simplification. None blocks beginning
AlgoDMap.
