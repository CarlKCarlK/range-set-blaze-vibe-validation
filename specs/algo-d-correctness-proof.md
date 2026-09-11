# Algo D correctness proof

Algo D is the completed Lean model and proof of cursor-shaped range insertion.
It inserts one inclusive integer interval into a canonical `RangeSetBlaze` and
proves both normalized output and exact represented-set semantics.

## Cursor-gap model

The model represents the position of a mutable map cursor as one split of the
canonical range list:

```text
left | right
     ^
   cursor
```

Every range on `left` starts strictly below the insertion start; every range
on `right` starts at or above it. `CursorGap` is private to Algo D. It models
only the insertion algorithm's observable cursor operations, not B-tree nodes
or a reusable cursor framework.

## Rust-to-Lean correspondence

| Production Rust operation | Lean model |
|---|---|
| `lower_bound_mut` | one strict lower-bound split |
| `peek_prev` | `left.getLast?` |
| `peek_next` | `right.head?` |
| `remove_next` | consume `right.head` |
| reused predecessor mutation | functional accumulator plus reconstruction |
| `insert_before` | insert the accumulator between `left` and remaining `right` |

Rust mutates a reused predecessor before and during the forward scan. Lean
carries the same growing range functionally and reconstructs it once in the
predecessor's original position. This intentional representation difference
does not change successor decisions or the normalized result.

## Algorithm branches

The executable dispatcher follows five high-level cases:

1. An empty or reversed input interval is a no-op.
2. If the predecessor contains the input, the result is unchanged.
3. If the predecessor touches or overlaps and must grow, reuse it, extend it,
   and absorb mergeable successors.
4. If an exact-start successor contains the input, the result is unchanged.
5. Otherwise, start with a fresh accumulator, absorb mergeable successors,
   and insert it at the cursor gap.

The exact-start check is separate because the strict lower-bound split places
a stored range beginning at the insertion start on `right`.

## Central forward invariant

During the successor scan, the left side is already finalized. The accumulator
represents the inserted range together with every successor absorbed so far,
while the remaining right side is untouched. The scan consumes a mergeable
head and grows the accumulator, or stops at the first genuine integer gap.
Canonical ordering then guarantees that every later range is also beyond that
gap.

`absorbSuccessors_preserves_order_lower_bound_and_union` proves ordering,
boundary information, and exact union together in one induction. Combining
the three facts avoids separate traversals and lets both reconstruction paths
reuse the same semantic contract.

## Correctness result

The public theorem is:

```lean
theorem internalAddD_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAddD s r).toSet = s.toSet ∪ r.toSet
```

The `RangeSetBlaze` returned by `internalAddD` also carries the canonical
`List.Pairwise NR.before` representation invariant. Thus the proof establishes
normalized ranges and exact set union for every input interval.

## Proof architecture

- `lowerBoundGap_spec` reconstructs the source and proves the strict-left and
  non-strict-right boundary facts.
- `absorbSuccessors_preserves_order_lower_bound_and_union` is the single
  forward-scan induction.
- The shared range-containment lemma from `Basic` proves that either unchanged
  branch adds no new elements.
- The predecessor-reuse and fresh-accumulator lemmas reconstruct canonical
  output and exact union.
- `internalAddDNRs_preserves_order_and_union` follows the executable branches.
- `internalAddD_toSet` handles empty input and exposes the public result.

## Scope limitations

This proof intentionally includes:

- no cached `len` proof;
- no complexity proof;
- no formal model of Rust `BTreeMap` cursor internals;
- no formal Rust-to-Lean refinement theorem.

The production algorithm is intended to take `O(log r + k)` time for `r`
stored ranges and `k` absorbed ranges: one lower-bound search followed by a
forward cursor walk. That claim is correspondence documentation, not a theorem
about the Lean list model.

## Proof soundness and status

The elaborated public theorem depends only on:

```text
[propext, Classical.choice, Quot.sound]
```

It has no `sorryAx` dependency. Algo D contains zero `sorry`s and all proof
obligations are complete.

Concrete regression examples include direct expected-range assertions as well
as comparisons with Algo C. Canonical-representation uniqueness from equal
`toSet` values remains possible future shared infrastructure; it is not needed
for Algo D's correctness theorem.
