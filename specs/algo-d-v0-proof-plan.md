# Algo D v1: foundational cursor proofs

V1 validates the v0 architecture by proving the lower-bound split and the
central forward walk.  It also closes the two immediate containment lemmas,
leaving the two reconstruction branches and executable dispatcher for v2.

Algo D inserts one inclusive integer interval into a canonical range set.  A
**canonical** list contains nonempty ranges in increasing order, with at least
one missing integer between every pair.  In Lean this is
`List.Pairwise NR.before`; `a ≺ b` means that a genuine integer gap separates
`a` from `b`.

The **represented set**, written `toSet`, is the set of all integers covered
by the stored ranges.  Two ranges are **mergeable** when they overlap or touch,
so their union has no missing integer.  Their **glue** (or hull) is the smallest
inclusive range containing both.  During insertion the one range being grown
is the **accumulator**.  The range immediately left of the gap is the
**predecessor**, and the range immediately right is the **successor**.

This version models the proposed Rust `BTreeMap` cursor algorithm.  A
**cursor gap** is the position between two pieces of the canonical list:

```text
left                                        right
[1---3] [8---10] | [14---18] [25---30]
                 ^ cursor
```

For a search key `start = 12`, every range on the left begins below 12 and
every range on the right begins at or above 12.  Lean represents this with the
private pair of lists `CursorGap.left` and `CursorGap.right`; it does not model
B-tree nodes or build a reusable cursor library.

## Cursor operations

The production and model operations correspond as follows:

| Rust cursor operation | Lean list-gap operation |
|---|---|
| `lower_bound_mut(Included(start))` | one `List.span` at `lo < start` |
| `peek_prev()` | `left.getLast?` |
| `peek_next()` | `right.head?` |
| `remove_next()` | recurse on the tail of `right` |
| `insert_before(range)` | `left ++ range :: remainingRight` |
| extend stored predecessor | `left.dropLast ++ grown :: remainingRight` |

The final row is deliberately distinct from insertion: once the predecessor
is reused, Algo D replaces that stored predecessor and never inserts a second
accumulator.

Rust mutates the reused predecessor's endpoint before scanning successors and
may extend it again after the scan.  Algo D expresses the same operation
functionally: the reused range becomes the scan accumulator, and
reconstruction writes its final value back into the predecessor's position.
Both forms make the same successor-interaction decisions and produce the same
normalized range list; only their intermediate machine states differ.

## Control-flow examples

### Predecessor contains the input

```text
stored: [1---4]  [10----------------30] | [40---45]
input:                     [15---20]
cursor:                                  ^

result: unchanged
```

The last range on the left starts before the input, overlaps it, and reaches
at least as far right.  The input is a subset of that stored range.

### Reuse and extend the predecessor

```text
stored: [1---4]  [10---13] | [18---20] [30---35]
input:                 [12-------18]

grow predecessor: [10---------18]
remove_next:       [18---20] is absorbed
stop:                              [30---35] has a genuine gap

result: [1---4]  [10----------20]  [30---35]
```

The accumulator is already physically represented by the predecessor.  Its
lower endpoint never moves, so earlier ranges remain valid.  Each consumed
successor is replaced together with the accumulator by `NR.glue`.

### Exact-start containment is on the right

```text
stored: [1---4] | [10----------------30] [40---45]
input:            [10---20]
cursor:          ^
```

`lower_bound(10)` puts a stored range beginning at 10 on the right, not the
left.  Therefore predecessor containment alone is insufficient: Algo D must
also inspect `peek_next` before starting the fresh scan.

### Forward absorption

```text
completed left | accumulator | unexamined right
    [1---3]     |   [7----------18] | [10---12] [14---16] [18---20] [30---35]
                                      remove_next ^

    [1---3]     |   [7----------18] | [14---16] [18---20] [30---35]
    [1---3]     |   [7----------18] | [18---20] [30---35]
    [1---3]     |   [7------------20] | [30---35]
                                          ^ first genuine gap: stop
```

At every step, already absorbed ranges have been accounted for exactly once.
If the first unexamined range is mergeable, `NR.glue_sets` says the hull is
exactly the old accumulator union that range.  If `accumulator ≺ next`, the
canonical ordering of the suffix implies that every later range is farther
right, so the walk stops.

Because every right-side range starts no earlier than the accumulator, this
symmetric `NR.mergeable` test is equivalent to Rust's one-sided
`candidate.start ≤ pending_end + 1` test over Lean's unbounded integers.

## V1 contract status

The proof scaffold has seven semantic obligations plus one public projection:

1. `lowerBoundGap_spec` reconstructs the original list and establishes the
   strict-left/non-strict-right lower-bound facts.  This contract was retained
   unchanged: each field is used by reconstruction, and it does not speculate
   about cursor operations beyond the one split.
2. `absorbSuccessors_preserves_order_lower_bound_and_union` is the central
   forward-walk contract.  Its one induction proves canonical output,
   boundary preservation, and exact represented-set preservation together.
   This contract was also retained unchanged.  Reconstruction needs ordering
   of the accumulator and untouched suffix, their common lower bound for the
   left cross-boundary proof, and exact union semantics.
3. `predecessor_containment_preserves_union` is the proved subset argument for
   an input contained by the left predecessor.
4. `exactStart_successor_containment_preserves_union` is the proved analogous
   subset argument for the equal-start range on the right.
5. `predecessor_reuse_preserves_order_and_union` reconstructs the list after
   replacing the stored predecessor and consuming successors.
6. `fresh_accumulator_preserves_order_and_union` reconstructs the list after
   the forward walk and the one final `insert_before`.
7. `internalAddDNRs_preserves_order_and_union` follows the executable branches
   and composes the preceding obligations.

The completed `internalAddD_toSet` theorem handles the empty input and projects
exact union from the raw nonempty-range contract; it still depends on the
deferred dispatcher theorem.

### Final lower-bound split contract

The split reconstructs the source list exactly.  Every left range starts
strictly below the search key, and every right range starts at or above it.
The last-left-is-the-only-candidate fact is deliberately not another field:
canonical pairwise order plus
`NR.pairwise_before_prefix_last_suffix` derives it when reconstruction has an
actual predecessor.

The proof uses `List.span_eq_takeWhile_dropWhile`, the standard reconstruction
and prefix-membership facts, and one short traversal only for the fact that
all members of the ordered suffix lie beyond the first failed predicate.

### Final forward-walk invariant

At every recursive call, the accumulator still begins at the insertion start,
the unexamined suffix is canonical and starts no earlier than that boundary,
and the output represents exactly the accumulator union the suffix.  The
output list—final accumulator followed by untouched suffix—is canonical and
retains the same lower bound.

One induction suffices because all three conclusions advance through the same
recursive call.  On absorption, `NR.glue_sets` updates exact semantics while
the glue keeps the accumulator's lower endpoint.  On stopping,
non-mergeability and the lower-endpoint order imply `accumulator ≺ successor`;
`before_trans` carries that gap across every later range.  No raw endpoint
arithmetic is needed in the forward proof.

No v0 fields were removed or weakened.  Review showed that the output-wide
lower bound is precisely what the fresh reconstruction branch will need to
order its untouched left prefix before both the final accumulator and every
remaining successor.

These are theorem-sized mathematical facts, not placeholders inside the
algorithm.  The executable functions themselves contain no `sorry`.

## Shared proof API

Algo D reuses the existing vocabulary directly:

- `NR.before` describes a genuine gap; `RangeSetBlaze.before_trans` and
  `NR.before_asymm` provide its ordering laws.
- `NR.mergeable` is the overlap-or-touch predicate used by the forward test.
- `NR.glue` builds the accumulated hull and `NR.glue_sets` proves its exact
  set meaning.
- `NR.before_glue` and `NR.glue_before` preserve external gap boundaries.
- `NR.mergeable_glue_left` records monotonic mergeability under growth.
- `NR.pairwise_before_prefix_last_suffix` isolates the only possible
  interacting range on the left.
- `rangesToSet`, `rangesToSet_append`, and
  `rangeToSet_subset_rangesToSet_of_mem` provide list-level set semantics.

No new synonym for gap, mergeability, hull, or represented list set is
introduced.

Algo C and D share predecessor containment, mergeability, first-gap stopping,
one forward induction, and exact union semantics.  D-specific facts are the
strict lower-bound cursor gap, `peek_prev` versus `peek_next`, the equal-start
right-side case, predecessor reuse, repeated `remove_next`, and the absence of
`insert_before` on the stored-accumulator path.

## V1 remaining `sorry` inventory

Three `sorry`s remain:

1. `predecessor_reuse_preserves_order_and_union`;
2. `fresh_accumulator_preserves_order_and_union`;
3. `internalAddDNRs_preserves_order_and_union`.

The central `absorbSuccessors` proof has exactly one induction and two explicit
cases: absorb the first successor or stop at the first genuine gap.  The
lower-bound split has a separate short list induction for propagation from the
first failed split predicate through the ordered suffix.  Neither
reconstruction theorem should need another recursive proof.

For v2, the two reconstruction theorems still deserve a contract review.  They
currently mention the concrete private gap operations; that is appropriate
for validating cursor behavior, but their hypotheses may be tightened once
the proved lower-bound contract is applied at their call sites.  The central
scan's output-wide lower bound should now be treated as validated rather than
reopened without evidence from reconstruction.

No uniqueness theorem for canonical range representations currently exists.
If one is later added to the shared API, canonicality plus `toSet` equality
should make `internalAddD s r = internalAddC s r` a short validation theorem.
This plan records that opportunity but does not construct an extensional-equality
proof.

## Scope and operational claim

The Lean specification proves only canonical representation and
`old.toSet ∪ inserted.toSet`.  Rust's cached cardinality update is a separate
refinement property and is intentionally absent.

For a production map with `r` stored ranges and `k` absorbed ranges, the design
performs one logarithmic lower-bound search followed by constant predecessor
work and a single forward visit to each absorbed range: `O(log r + k)`.  The
list model preserves that control-flow shape but does not formalize cost.

The module includes twelve `native_decide` regression examples comparing Algo
D's concrete output ranges with Algo C for empty input/set, insertion on both
sides, both containment paths, separate insertion with zero/one/many merges,
and predecessor extension with zero/one/many successor merges.

## V0 baseline metrics

Metrics are recorded as separate signals, never as a composite score:

- executable core: 62 active LOC, counted across `CursorGap`, seven private
  operations/helpers, and public `internalAddD`, excluding comments, proof
  declarations, and test helpers;
- whole `AlgoD.lean` module under collector/schema v3: 275 physical LOC, 160
  active-code LOC, 80 comment-only LOC, and 35 blank LOC;
- definitions: eleven in the whole module—eight algorithm definitions and
  three private test helpers—plus the private `CursorGap` structure;
- theorem/lemma declarations: eight (seven private, one public);
- proof holes: seven;
- inductions implemented: zero; inductions intentionally planned: one;
- executable regression examples: twelve;
- shared API declarations reused or named by the proof plan: thirteen;
- proposed shared theorem not yet added: uniqueness of canonical range lists
  from equality of their represented sets.

The repository's v3 metric collector supplies the reproducible whole-file and
repository LOC/token dashboard after implementation.

## V1 metrics

Under the same collector/schema v3, `AlgoD.lean` now has 351 physical LOC,
237 active-code LOC, 79 comment-only LOC, and 35 blank LOC.  It still has
eight theorem/lemma declarations.  The remaining proof-hole count is three.

The whole-file lexical dashboard reports two `induction`, zero `cases`, three
`by_cases`, eleven `have`, ten `rw`, eleven `simp`, four `simpa`, and one
`omega`.  One induction belongs to the lower-bound suffix fact and one to the
central forward walk.  The forward theorem itself occupies 55 active lines
including its statement (45 for the proof body), with one `induction`, one
explicit mergeability `by_cases`, and no endpoint-arithmetic tactic.
