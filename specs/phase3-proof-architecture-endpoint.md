# Phase 3 proof-architecture endpoint

This report freezes the Phase 3 endpoint for Algo C and records the boundary
for subsequent stabilization, documentation, validation, and transfer work.
It is not authorization for another proof-compression campaign.

## Source identity

- Endpoint commit: `ddd1b4949e9e310a657378d9d09214e3044ae4ab`
- Commit date: 2026-09-10 13:16:00 -07:00
- Commit subject: `Remove redundant loLE ordering adapter`
- Endpoint tree: `5c891c0e25455d35864f037d02af6511b2ed1037`
- Branch state when frozen: `main`, synchronized with `origin/main`
- Lean: 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`
- Toolchain: `leanprover/lean4:v4.33.1`
- Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`
- Metrics: collector/schema v3 from `scripts/phase0_metrics.py`
- Collector SHA-256: `a07fc3573ed0134219b1d539c2684d717707ab7360a8e0ba97602ef95549e048`
- Endpoint Lean-source manifest SHA-256: `81dcb5eda698a4cb4e296daa4587adc0aee875b45e9bf5d6aeb5b1a7ca177c76`

The Phase 0 comparison source is commit
`5bcfce5517024171625cc781636f1c67a7eab470`, tree
`81e52f3e7656cc882fa04aeeeeed812cd4cb84f8`. Historical values below were
reconstructed with the same v3 collector used for the endpoint.

## Verification and protected surface

At the endpoint, `RangeSetBlaze.internalAddC_toSet` depends on exactly:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` dependency. The Phase 4 documentation pass must preserve
that dependency set.

The principal protected theorem statement is:

```lean
theorem internalAddC_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAddC s r).toSet = s.toSet ∪ r.toSet
```

The supporting public theorem surface at the endpoint consists of the
set-preservation projection for the merge loop, the optional-last bridge, the
two safe-insertion correctness theorems, and the extend-predecessor correctness
theorem. Documentation work must not change their statements.

The protected executable definitions are:

- `deleteExtraNRs_loop`
- `deleteExtraNRs`
- `internalAdd2NRs`
- `internalAdd2_safe`
- `internalAdd2_safe_from_le`
- `internalAddC_extendPrev_safe`
- `internalAddC`

The five definitions in the original executable algorithm footprint have the
following exact source-span SHA-256 values at the endpoint commit. The hashes
cover the declaration bodies, before this report's documentation-only edits.

| Definition | Endpoint source lines | SHA-256 |
|---|---:|---|
| `deleteExtraNRs_loop` | 28–41 | `88769c35828d781d4d90ede37534c4eb016362dd1783329946af1fa8fa72e3b7` |
| `deleteExtraNRs` | 122–136 | `9ab2d9bb823ace5ef4de005d77f1700a7af5f81551ba5cfb55f2ac413995e271` |
| `internalAdd2NRs` | 138–145 | `c2d940bcfc42c895ac68c386f79356e1d6f189db2c13dfa2badb1ff9fde740e0` |
| `internalAddC_extendPrev_safe` | 755–775 | `f1280997e85cadf432485c703afaae6f1ef30176f9f5b376e6c44818eba21ce7` |
| `internalAddC` | 776–828 | `2fdd61a4eb785a82f3c0ce3f0d97f2f15fda29eceb74a1c9c6252520e4c72e78` |

Their protected algorithm footprint is:

1. Empty input ranges return the original range set.
2. `internalAddC` locates the last range with `nr.lo ≤ start`.
3. No predecessor or a predecessor separated by a gap uses the insertion path.
4. An input covered by the predecessor leaves the range set unchanged.
5. A touching or overlapping predecessor is extended through the input.
6. The scan merges touching or overlapping following ranges and stops at the
   first true gap; it keeps the current lower endpoint and takes the maximum
   upper endpoint.
7. The returned representation remains `List.Pairwise NR.before` and represents
   exactly the old set union the input interval.

## Exact v3 metrics

### Algo C endpoint dashboard

| Category | Metric | Value |
|---|---|---:|
| Size | Physical LOC | 969 |
| Size | Nonblank LOC | 908 |
| Size | Blank LOC | 61 |
| Size | Comment-only LOC | 80 |
| Size | Active-code LOC | 828 |
| Branching | `cases` | 6 |
| Branching | `by_cases` | 6 |
| Branching | `induction` | 3 |
| Plumbing | `have` | 151 |
| Plumbing | `show` | 3 |
| Plumbing | `suffices` | 0 |
| Plumbing | `rw` | 45 |
| Automation | `simp` | 53 |
| Automation | `simpa` | 25 |
| Automation | `omega` | 4 |
| Automation | `linarith` | 0 |
| Automation | `grind` | 0 |
| Representation | qualified `List.span` | 22 |
| Representation | `takeWhile` | 24 |
| Representation | `dropWhile` | 7 |
| Representation | `getLast?` | 8 |
| Representation | `dropLast` | 5 |
| Representation | `pairwise_append` | 6 |
| Representation | `Sublist` | 2 |

Algo C has 10 definitions/abbreviations and 23 lemma/theorem declarations:
17 private and 6 syntactically public, under the v3 dashboard rules.

### Repository endpoint dashboard

Repository-owned Lean sources total 2,456 physical LOC, 2,108 active-code
LOC, 52 definitions/abbreviations, and 68 lemma/theorem declarations. Of the
lemma/theorem declarations, 21 are private and 47 syntactically public.

Repository-wide headline counts are `cases` 34, `by_cases` 13, `induction` 10,
`have` 374, `show` 3, `suffices` 0, and `rw` 47. These are separate dashboard
signals, not a composite complexity score.

### Phase 0 comparison

| Algo C metric | Phase 0 | Phase 3 | Reduction |
|---|---:|---:|---:|
| Physical LOC | 3,320 | 969 | 70.9% |
| Active-code LOC | 1,983 | 828 | 58.2% |
| Private lemma/theorem declarations | 36 | 17 | 52.8% |
| `cases` | 56 | 6 | 89.3% |
| `by_cases` | 17 | 6 | 64.7% |
| `induction` | 23 | 3 | 87.0% |
| `have` | 471 | 151 | 67.9% |
| `rw` | 172 | 45 | 73.8% |
| qualified `List.span` | 44 | 22 | 50.0% |
| `takeWhile` | 81 | 24 | 70.4% |
| `dropWhile` | 66 | 7 | 89.4% |
| `getLast?` | 7 | 8 | increase of 1 |
| `dropLast` | 10 | 5 | 50.0% |

The reductions span active code, visible branching, proof plumbing, and list
representation vocabulary. They should not be interpreted as an optimization
objective by themselves. In particular, predecessor lookup is a genuine
algorithm boundary, so the additional `getLast?` occurrence is not evidence of
regression.

## Proof architecture

### Merge scan

`deleteExtraNRs_loop` scans forward from a current range. It merges a pending
range when there is no integer gap, updates the upper endpoint with `max`, and
recurses; otherwise it returns the current range and untouched suffix.

`deleteExtraNRs_loop_preserves_order_lower_bound_and_union` is the single
semantic contract for this scan. From the pending-list ordering and lower-bound
assumptions it establishes:

- ordered output;
- preservation of the lower-bound invariant;
- exact preservation of `current.toSet ∪ pending.toSet`.

The unified contract deliberately replaces separate inductive proofs of those
three correctness dimensions. `deleteExtraNRs_loop_sets` is a set-only
projection retained at the public theorem boundary.

### Separate insertion

`internalAdd2NRs` splits the list at `nr.lo < start`, puts the new nonempty
range between the prefix and suffix, and invokes the delete/merge logic.

`internalAdd2NRs_preserves_order_and_union` proves in one contract that the
output remains `List.Pairwise NR.before` and represents the original list set
union the inserted interval. `internalAdd2_safe` packages the ordered list as a
`RangeSetBlaze`; its correctness theorem projects the set guarantee.

### Extend predecessor

`internalAddC_extendPrev_safe` removes the selected predecessor from the
prefix, extends its upper endpoint through the input, merges forward, and
reassembles the list.

`extend_predecessor_preserves_order_and_union` shares the span decomposition,
predecessor decomposition, prefix/suffix ordering, and loop result between the
wrapper's invariant proof and its set-correctness proof. It establishes ordered
output and exact union together.

### Top-level insertion

`internalAddC` preserves the production-shaped branch story:

1. empty input: return `s`;
2. no predecessor: insert separately;
3. separated predecessor: insert separately;
4. covered input: return `s`;
5. extending input: extend the predecessor and merge forward.

`internalAddC_toSet` mirrors those branches. The insertion and extension
branches dispatch to semantic correctness theorems. The covered branch uses a
local subset argument showing that an interval bounded by a stored predecessor
adds no new elements.

## Why both `< start` and `≤ start` are intentional

`internalAddC` uses `nr.lo ≤ start` because it is locating a predecessor. A
stored range beginning exactly at the input start must be considered: it may
cover the input or be the range that must be extended.

`internalAdd2NRs` uses `nr.lo < start` because it is identifying the untouched
prefix before an insertion. The inserted range itself begins at `start`; a
range at that boundary must not be treated as part of the untouched prefix.

The predicates are therefore not globally equivalent.
`nonstrict_start_gap_implies_strict_start_gap` bridges only the gap branch. If
the last range of the non-strict prefix ends with a strict gap before `start`,
then nonemptiness gives its lower endpoint at most its upper endpoint and hence
strictly below `start`. `Pairwise NR.before` ordering propagates the conclusion
to every earlier prefix range. Consequently the non-strict prefix contains no
range beginning exactly at `start`, and it supplies the strict-prefix gap
evidence required by the insertion helper.

## Production Rust correspondence

The comparison used local Rust repository `/home/carlk/programs/range-set-blaze`
at commit `aec75cd6d58ba8898c7393f456027123b85adbf5`. That checkout had unrelated
working-tree changes, but its diff did not modify `delete_extra`, `internal_add`,
or `internal_add2`; the audited insertion regions matched the committed source.

| Production Rust | Lean Algo C | Correspondence |
|---|---|---|
| `internal_add`: reject `end < start` | `internalAddC`: empty branch | Same branch semantics. |
| `range_mut(..=start).rev().next()` | `List.span (nr.lo ≤ start)` plus prefix `getLast?` | Same non-strict predecessor lookup. |
| no predecessor | `getLast? = none` | Both use separate insertion. |
| predecessor successor strictly below `start` | separated-predecessor branch | Both use separate insertion. |
| `end ≤ end_before` | covered branch | Both leave the set unchanged. |
| `end_before < end` | extend-predecessor branch | Both preserve the predecessor start and extend its end. |
| `internal_add2`: map insertion followed by `delete_extra` | `internalAdd2NRs` followed by `deleteExtraNRs` | Same insert-then-merge shape. |
| `delete_extra`: `map_while`, update maximum end, delete merged keys | `deleteExtraNRs_loop`: recursive merge scan | Both merge forward and stop at the first non-touching range. |

Rust mutates a `BTreeMap`, deletes absorbed keys, and updates cached length.
Lean rebuilds a list and proves `Pairwise NR.before` plus set equality; cached
length is outside the model. Rust also separates the overflow-safe successor
test because `T` is bounded, while Lean uses unbounded `Int` arithmetic.

Lean's recursive loop tests against the accumulated current upper endpoint;
the Rust loop retains the original insertion/extension end in its predicate
while accumulating `end_new`. These agree on a valid sorted-disjoint input:
after the first merge, the stored-range invariant prevents a later range from
becoming newly touching solely through a chain of already-adjacent stored
ranges. Lean's loop contract is thus slightly more general, but not a change in
the behavior reached through `internalAddC`.

No suspicious algorithmic drift was found. The data/control-flow shape and
branch semantics correspond at the intended abstraction level.

## Algo B and Algo C: shared-proof discovery

This comparison is read-only. Algo B partitions the entire list into before,
touching, and after blocks and glues the touching block; Algo C models the
production predecessor lookup and forward mutation path. Their executable
algorithms should remain distinct.

| Concept | Classification | Assessment |
|---|---|---|
| `NR.before`, its transitivity, and lower-endpoint consequence | Already shared/general | Defined or proved in `Basic`; both algorithms should continue to use it. |
| Last prefix element before every suffix element | Already shared/general | `NR.pairwise_before_prefix_last_suffix` captures the reusable boundary. |
| Nonempty-range endpoint validity | Already shared/general | Carried by `NR`; no additional helper is needed merely to restate it. |
| Touching/overlap union | Mostly already shared/general | `IntRange.mergeRange_toSet_of_overlap` and `NR.glue_sets` provide the symmetric domain fact. |
| Impossibility of a `before` cycle | Genuinely reusable candidate | Algo B still has a private `absurd_cycle`; a domain-level asymmetry or cycle theorem could serve both future algorithms, but extraction is not part of this pass. |
| Canonical set view of a list of ranges, including append and membership/subset facts | Genuinely reusable candidate | `Basic.listToSet`, `AlgoB.listSet`, and `AlgoC.algoCListSet` remain duplicate vocabulary. This is the clearest shared maintenance candidate. |
| An interval bounded inside a stored member contributes no new elements | Genuinely reusable candidate | Algo C proves this locally in the covered branch; the mathematical fact is representation-independent enough to reconsider when another consumer appears. |
| Ordered lower-preserving merge with upper endpoint `max` | Genuinely reusable candidate with limited current reuse | It matches cursor/map insertion vocabulary, but current code does not justify speculative extraction. |
| Strict/non-strict `List.span` conversion and suffix lower bound | Algo C-specific representation fact | These arise from Algo C's production-shaped predecessor/insertion boundaries. |
| `SplitWitness`, three-way partition, and `glueMany` block reconstruction | Algo B-specific fact | These describe Algo B's whole-list partition algorithm rather than common insertion mechanics. |
| Generic prefix/suffix `Pairwise` projections | Already provided by Mathlib/shared API | Prefer `List.pairwise_append` and the existing focused domain lemma over new local aliases. |

No implementation or proof API was changed as a result of this discovery.

## Remaining representation vocabulary

- `List.span`: necessary representation work in the executable strict and
  non-strict splits; theorem signatures intentionally expose those exact
  algorithm boundaries.
- `takeWhile` and `dropWhile`: mostly harmless local proof machinery used to
  project and reconstruct `span` results. The explicit conversion at the final
  extend call is a possible later presentation cleanup, not an architectural
  problem.
- `getLast?`: necessary predecessor selection matching the production lookup.
- `dropLast`: necessary list modeling of removing the predecessor before
  replacing it with its extension.
- `algoCListSet`: a compatibility/local proof bridge that duplicates the same
  fold in `Basic` and Algo B.
- `algoCListSet_eq_foldr`: a definitional bridge used to cross that duplicate
  vocabulary.

The two `algoCListSet` items are the clearest maintenance debt. A future,
narrow cleanup may establish one canonical list-of-ranges set view, but it must
measure repository-wide movement and should not reopen the operation-contract
architecture.

## Transferable proof-design guidance

- Prove a mutating operation's semantic correctness dimensions together when
  they share the same decomposition or recursive facts.
- Prefer one canonical domain relation over adapter vocabularies.
- Preserve useful split, predecessor, and pairwise evidence long enough for all
  consumers to reuse it.
- Distinguish a mathematical specification mismatch from a representation
  mismatch before introducing an abstraction.
- Isolate genuine mathematical bridges, such as the gap-conditioned conversion
  from a non-strict predecessor prefix to a strict insertion prefix.
- Reject witness or state packages that merely bundle the current proof state
  without representing a stable semantic object.
- Do not add helpers that internally reconstruct the same `List.span` evidence
  a caller already possesses.
- Treat LOC and token counts as independent review signals, not refactoring
  priorities or a composite score.
- Treat possible cursor-based `BTreeMap` insertion and `RangeMapBlaze` reuse as
  a design tie-breaker, not as justification for speculative proof API.

## Phase 4 boundary

Phase 4 is stabilization, documentation, validation, and transfer. Further
changes to proof bodies, operation contracts, or executable structure require a
new, narrowly justified maintenance task rather than continuation of the Phase
3 refactoring campaign.
