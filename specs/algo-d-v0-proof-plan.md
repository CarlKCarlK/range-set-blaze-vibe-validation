# Algo D v0: cursor-gap model and proof plan

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

## Proposed contracts

The proof scaffold has seven deferred semantic obligations plus one completed
public projection:

1. `lowerBoundGap_spec` reconstructs the original list and establishes the
   strict-left/non-strict-right lower-bound facts.
2. `absorbSuccessors_preserves_order_lower_bound_and_union` is the central
   forward-walk contract.  One induction should prove canonical output,
   boundary preservation, and exact represented-set preservation together.
3. `predecessor_containment_preserves_union` is the subset argument for an
   input contained by the left predecessor.
4. `exactStart_successor_containment_preserves_union` is the analogous subset
   argument for the equal-start range on the right.
5. `predecessor_reuse_preserves_order_and_union` reconstructs the list after
   replacing the stored predecessor and consuming successors.
6. `fresh_accumulator_preserves_order_and_union` reconstructs the list after
   the forward walk and the one final `insert_before`.
7. `internalAddDNRs_preserves_order_and_union` follows the executable branches
   and composes the preceding obligations.

The completed `internalAddD_toSet` theorem handles the empty input and projects
exact union from the raw nonempty-range contract.

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

## Current `sorry` inventory

There are seven `sorry`s, one in each deferred contract listed above.  The expected
induction count is one: the combined `absorbSuccessors` proof.  The split and
branch theorems should use list decomposition, pairwise-order projections, and
set algebra without separate recursive proofs.

Two interfaces deserve review while filling v1:

- The central scan contract exposes a lower bound for every output range.  If
  reconstruction only needs the accumulated head's unchanged lower endpoint
  plus its gap before the returned suffix, a more focused boundary conclusion
  may read better.
- The two reconstruction theorems currently mention the concrete private gap
  operations.  This is appropriate for validating cursor behavior, but their
  hypotheses may be tightened once the lower-bound proof supplies a convenient
  predecessor decomposition.

No uniqueness theorem for canonical range representations currently exists.
If one is later added to the shared API, canonicality plus `toSet` equality
should make `internalAddD s r = internalAddC s r` a short validation theorem.
V0 records that opportunity but does not construct an extensional-equality
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

## V0 metrics

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
