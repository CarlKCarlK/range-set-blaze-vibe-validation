# Why Algo C insertion is correct

Algo C inserts one inclusive integer interval into a stored collection of
inclusive integer intervals. This article explains why the result contains
exactly the old integers together with the inserted integers, and why the
stored intervals remain in the required form.

The argument starts with examples. Names used by the Lean development appear
only after the underlying idea has been shown in ordinary language.

## 1. First example: the inserted interval is already present

Suppose the stored ranges are

```text
stored ranges:
[1---5]    [10------------30]    [40---50]

insert:
                 [15---20]
```

The interval `[15, 20]` adds no integers. Every integer from 15 through 20 is
already in `[10, 30]`, so the correct result is the original list:

```text
[1---5]    [10------------30]    [40---50]
```

The algorithm finds the relevant stored range by looking for the last one
whose lower endpoint is at most the new lower endpoint, 15. Here that range is
`[10, 30]`. The range found by this lookup is called the **predecessor**. It
is the only stored range at or to the left of the new start that could overlap
the new interval or contain it.

The predecessor starts no later than the new interval and ends no earlier:

```text
10 ≤ 15 ≤ 20 ≤ 30.
```

It therefore contains the entire new interval. Returning the old ranges is
correct because taking the union with a subset changes nothing:

```text
old integers ∪ inserted integers = old integers.
```

Returning the old list also preserves the required stored form: every range
is still nonempty, and the ranges are still ordered, non-overlapping, and
separated by at least one missing integer. Nothing about the representation
has changed.

Together, these observations prove both obligations for the covered-insertion
case: the stored form is preserved, and the represented set is unchanged. No
merging work is needed.

### How Lean proves this example

The covered branch of `internalAddC_toSet` formalizes exactly the subset
argument above. After Lean has followed the algorithm's tests to this branch,
`prev` is `[10, 30]`, `r` is `[15, 20]`, and `h_covered` records the endpoint
comparison `20 ≤ 30`. The proof is:

```lean
rename_i prev h_last h_no_gap h_covered
have h_prev_props :=
  start_split_predecessor_le_and_mem s.ranges r.lo prev h_last
have h_r_covered : r.toSet ⊆ s.toSet := by
  simpa [RangeSetBlaze.toSet] using
    toSet_subset_rangesToSet_of_mem_of_bounds
      h_prev_props.2 h_prev_props.1 h_covered
show s.toSet = s.toSet ∪ r.toSet
rw [Set.union_eq_self_of_subset_right h_r_covered]
```

Here is how its pieces correspond to the ordinary argument.

The opening `rename_i` gives readable names to facts supplied by the branch
tests: `h_last` records the successful predecessor lookup, `h_no_gap` records
that there is no genuine gap before the input, and `h_covered` records the
upper-endpoint test. Each `have` names an intermediate proposition, and `⊆`
is ordinary set inclusion.

First, `start_split_predecessor_le_and_mem` extracts two facts from the
successful predecessor lookup `h_last`: `prev.lo ≤ r.lo`, which is `10 ≤ 15`
in the example, and `prev ∈ s.ranges`, which says that `[10, 30]` really is
one of the stored ranges.

Next, `h_r_subset_prev` proves that every integer in `[15, 20]` is in
`[10, 30]`. Lean chooses an arbitrary integer `x` with `intro x hx`.
Simplifying membership in an inclusive interval turns `hx` into the two
inequalities `15 ≤ x` and `x ≤ 20`. Transitivity combines them with
`10 ≤ 15` and `20 ≤ 30`, producing `10 ≤ x` and `x ≤ 30`. Expressions such
as `h_prev_props.1` and `hx.2` select the first or second fact from one of
these pairs.

The fact `h_prev_in_s` then lifts membership in the one stored range
`[10, 30]` to membership in the set represented by the whole list. Composing
the two subset proofs gives `h_r_covered : r.toSet ⊆ s.toSet`. The final
rewrite applies the set law that union with a subset changes nothing.

The theorem shown here states only the set equality. Canonical form needs no
new argument in this branch: the executable definition returns `s` itself,
whose `RangeSetBlaze` value already contains the proof that its ranges are in
canonical form. The hypothesis `h_no_gap` helped the algorithm reach the
covered branch, but the subset argument no longer needs it once the two
endpoint bounds and predecessor membership are available.

## 2. Second example: grow one interval and stop at a gap

Now consider an insertion that does add integers:

```text
stored ranges:
[1---5]    [10---12]    [16---18]              [30---40]

insert:
   [4----------------17]
```

The predecessor is `[1, 5]`. It overlaps the new interval, so the two can be
replaced by their smallest enclosing interval, `[1, 17]`. The next two stored
ranges are already contained in, or overlap, the interval being built.
Combining them leaves its right end at 17 and then moves it to 18.

The following stored range begins at 30. Integers 19 through 29 are missing,
so that range cannot be combined with `[1, 18]`:

```text
result:
[1-----------------18]                          [30---40]
```

It is safe to stop when `[30, 40]` is reached. The stored ranges are in
increasing order, and every still-later range lies even farther right. If
`[30, 40]` cannot combine with `[1, 18]`, no later range can combine with
it either.

This left-to-right examination of the ranges after the insertion point is
called the **forward scan**. During it, the one interval being built is called
the **current interval**. The ranges to its right that have not yet been
examined form the **pending suffix**; “suffix” here simply means the remaining
final part of the original list.

The example contains the entire idea behind the forward scan:

1. Combine the next range with the current interval if they overlap or touch.
2. Repeat with the next unexamined range.
3. At the first range separated by at least one missing integer, emit the
   current interval and retain that range and everything after it unchanged.

## 3. The required stored form

Each stored range is nonempty: `[lo, hi]` must satisfy `lo ≤ hi`. Stored
ranges also have at least one missing integer between consecutive entries.
For example, `[1, 5]` may be followed by `[7, 9]`, because 6 is missing,
but it may not be followed by `[6, 9]`, because those ranges touch and
should be combined.

A list satisfying these two rules is the **canonical representation** of the
set:

- every range is nonempty; and
- the ranges are ordered from left to right, do not overlap, and do not touch.

Its set meaning is simply the union of all integers in all its ranges. For
example, `[1, 5], [10, 12]` represents
`{1, 2, 3, 4, 5, 10, 11, 12}`.

For two nonempty ranges `a` and `b`, the proof writes

```text
a ≺ b    when    a.hi + 1 < b.lo.
```

This inequality says that at least one integer is missing between `a` and
`b`. We call this a **genuine gap**. It is stronger than saying only that
`a.lo < b.lo`.

Two ranges are **mergeable** when they overlap or touch. Their smallest
enclosing interval is called their **hull**:

```text
hull(a, b) = [min(a.lo, b.lo), max(a.hi, b.hi)].

genuine gap:  [1, 2]   3   [4, 6]    because 2 + 1 < 4
touching:     [1, 2][3, 5]            because 2 + 1 = 3
overlapping:  [1, 4]
                  [3, 6]
```

For mergeable ranges, the hull denotes exactly their union. Algo C only
combines a current interval with a range to its right, so the hull keeps the
current interval's lower endpoint and may increase only its upper endpoint.

The correctness claim now has two precise parts:

1. The output is again a canonical representation.
2. The output denotes exactly the old set union the inserted interval.

## 4. Why the forward scan works in general

Return to the shape already seen in the second example:

```text
current interval     first unexamined range     all later ranges
   [10---15]                [16---20]            [25---30] [40---45]
```

The first unexamined range is called `next`; the ranges after `next` are
called the `tail`. Thus a nonempty pending suffix has the form
`next | tail`.

There are only two cases.

### The next range overlaps or touches

If `next.lo ≤ current.hi + 1`, replace `current` and `next` by their hull
and continue with `tail`. This step preserves the represented set because
the hull of mergeable ranges represents exactly their union. It preserves the
needed ordering facts because `next` is to the right, so the hull keeps the
current interval's lower endpoint exactly; the remaining ranges also keep
their original order.

### There is a genuine gap before the next range

If `current.hi + 1 < next.lo`, the current interval is finished. Place it in
the output and keep `next` and `tail` unchanged. Every member of `tail`
lies after `next`, so it lies after the current interval as well. This proves
that stopping at the first genuine gap preserves the required stored form.

### Induction over the unexamined ranges

The general proof is induction on how many ranges remain unexamined.

If none remain, the algorithm emits the current interval. Its set meaning is
unchanged.

If at least one remains, the two endpoint comparisons above are exhaustive.
In the mergeable case, one range is consumed, its set is preserved by the hull
law, and the induction hypothesis applies to the shorter remainder. In the
genuine-gap case, the algorithm stops and the ordering argument above applies
to every retained range.

The induction maintains these facts:

- the unexamined ranges retain their original order and separation;
- the lower endpoint of the current interval stays fixed;
- every unexamined range begins at or to the right of that fixed lower
  endpoint; and
- the union of the current interval and all unexamined ranges never changes.

Consequently the forward scan returns ranges in canonical form, keeps the
needed lower endpoint fixed, and preserves the represented set exactly.

In the Lean development,
`deleteExtraNRs_loop_preserves_order_lower_bound_and_union` proves these
facts together. A **contract** is the collection of assumptions a component
accepts and conclusions it guarantees; this theorem is the forward scan's
contract. Its private callers project the ordering, boundary, and set facts
they need directly from that single result.

## 5. How an insertion reaches the forward scan

There are two ways to begin an insertion that changes the stored ranges. The
first places the new interval separately from everything to its left. The
second enlarges the predecessor. Both produce one current interval followed by
still-unexamined ranges, so both use the forward scan just proved.

### Insert separately from the left

Consider this example:

```text
stored ranges: [1, 5]    [10, 12]       [20, 30]
insert:                 [7, 9]

result:        [1, 5]    [7-----12]      [20, 30]
```

There is a genuine gap between `[1, 5]` and `[7, 9]`, because 6 is
missing. The new interval therefore stays separate from `[1, 5]`. It
touches `[10, 12]`, so the forward scan combines those two ranges.

The initial consecutive part of the old list that remains to the left is
called the **untouched prefix**; “prefix” means an initial part of a list. The
rest of the old list is the suffix. The point between those two parts is the
insertion **boundary**.

In the example the pieces are

```text
untouched prefix | new current interval | pending suffix
     [1, 5]      |        [7, 9]        | [10, 12], [20, 30].
```

The general proof follows the example:

1. Every range in the untouched prefix has a genuine gap before the new
   interval.
2. Every range in the pending suffix starts at or to the right of the new
   interval's lower endpoint.
3. The forward scan preserves that lower endpoint, so the untouched prefix can
   be put back without creating an overlap or a touching pair.
4. The old set was `prefix ∪ suffix`; the new set is
   `prefix ∪ (input ∪ suffix)`, which is exactly `old set ∪ input`.

This path also covers an empty old list and insertion before the first stored
range. In those cases the untouched prefix is empty. If the entire old list is
empty, the pending suffix is empty too, so the forward scan immediately emits
the input interval.

The Lean theorem `internalAdd2NRs_preserves_order_and_union` proves the
ordered output and exact union for this path.

### Enlarge the predecessor

The second example used this path. In general its pieces look like this:

```text
earlier stored ranges | predecessor | later stored ranges
                                  + input
                                  ───────►
earlier stored ranges | enlarged predecessor | later stored ranges
```

This path applies when the predecessor overlaps or touches the input and the
input reaches farther right. The enlarged interval keeps the predecessor's
lower endpoint and takes the larger upper endpoint. It therefore represents
exactly `predecessor ∪ input`.

The old predecessor is removed before its enlarged replacement is inserted;
otherwise both versions would appear in the result. Earlier stored ranges stay
separated from the replacement because its lower endpoint has not moved. Some
later ranges may now overlap or touch the replacement, which is exactly what
the forward scan handles.

The Lean theorem `extend_predecessor_preserves_order_and_union` proves the
ordered output and exact union for this path.

## 6. Why the two lower-endpoint tests differ

The examples have involved two related questions:

1. Which stored range might contain or overlap the input on its left?
2. Which stored ranges can remain untouched before a separate insertion?

The first question uses `lo ≤ start`. A stored range beginning exactly at
the input start must be considered, because it may contain the input or need
to be enlarged. The last range satisfying this test is the predecessor.

The second question uses `lo < start`. A stored range beginning exactly at
the input start must not be placed unchanged before the newly inserted range.

```text
stored lower endpoint:    lo < start    lo = start    lo > start
                          ──────────┬─────────────┬─────────────
predecessor lookup ≤:       left          left          right
separate insertion <:       left          right         right
```

The two splits are not generally identical. They agree where the separate
path needs them to agree: if the predecessor has a genuine gap before the
input, then

```text
predecessor.lo ≤ predecessor.hi < predecessor.hi + 1 < start.
```

Thus its lower endpoint is strictly below `start`; the same is true of every
earlier range. The theorem
`nonstrict_start_gap_implies_strict_start_gap` records precisely this
case-specific bridge. It does not claim that `< start` and `≤ start` are
equivalent in general.

## 7. The complete correctness argument

Algo C's decisions are now consequences of the preceding examples and rules:

1. If the input is empty (`stop < start`), it denotes no integers, so return
   the old ranges.
2. Otherwise find the predecessor, if one exists.
3. If there is no predecessor, insert separately and use the forward scan.
4. If there is a genuine gap after the predecessor, insert separately and use
   the forward scan.
5. If the predecessor contains the input, return the old ranges, as shown in
   the first example.
6. Otherwise the predecessor overlaps or touches the input and the input
   reaches farther right. Enlarge the predecessor and use the forward scan.

These cases are exhaustive. The predecessor either exists or does not. If it
exists, there is either a genuine gap or there is not. With no gap, its upper
endpoint either reaches the input's upper endpoint or falls short of it.

The unchanged cases preserve both the stored form and the represented set
immediately. The two changing cases establish the facts proved in Section 5
and then reuse the induction from Section 4. Therefore the final result is in
canonical form and denotes exactly

```text
old set ∪ input interval.
```

The public Lean theorem `internalAddC_toSet` states the set part:

```text
(internalAddC s r).toSet = s.toSet ∪ r.toSet.
```

The constructed result also carries Lean's proof that its stored ranges have
the required order and separation.

## Appendix: map to the Lean development

The correctness argument above does not require Lean knowledge. This appendix
only connects its concepts to declaration names in the source.

Lean uses `IntRange.NR` for an inclusive interval together with proof that it
is nonempty. It uses `NR.before` for the genuine-gap relation `≺`, and
`NR.glue` for the hull of two ranges. The expression
`List.Pairwise NR.before` says that each earlier stored range has a genuine
gap before every later stored range. Although the word `Pairwise` is library
terminology, its meaning here is just the canonical ordering rule already
explained in Section 3.

| Role in the human proof | Lean declaration |
|---|---|
| Nonempty inclusive interval | `IntRange.NR` |
| Genuine gap and canonical order | `NR.before` |
| Genuine gaps compose from left to right | `NR.before_trans` |
| A genuine gap implies increasing lower endpoints | `NR.before_lo_lt` |
| Overlap-or-touch test | `NR.mergeable`, `NR.mergeable_of_startsBefore_of_not_before` |
| Hull represents exactly the union | `NR.glue_sets` |
| A hull remains separated from outside ranges | `NR.before_glue`, `NR.glue_before` |
| Set denoted by a list of ranges | `rangesToSet` |
| Reconstructing the set meaning of appended list pieces | `rangesToSet_append` |
| An interval bounded by a stored range is contained in the represented set | `toSet_subset_rangesToSet_of_mem_of_bounds` |
| Separation between the last left range and all right ranges | `NR.pairwise_before_prefix_last_suffix` |
| Lower-endpoint fact for ranges after an insertion point | `NR.strict_start_split_suffix_lower_bound` |
| Forward-scan contract | `deleteExtraNRs_loop_preserves_order_lower_bound_and_union` |
| Separate-insertion contract | `internalAdd2NRs_preserves_order_and_union` |
| Bridge from the `≤ start` split to the `< start` split | `nonstrict_start_gap_implies_strict_start_gap` |
| Predecessor endpoint bound and membership in the old list | `start_split_predecessor_le_and_mem` |
| Predecessor-enlargement contract | `extend_predecessor_preserves_order_and_union` |
| Strict/non-strict insertion wrappers | `insertAtStrictStartGap`, `insertAtNonstrictStartGap` (private) |
| Extend-predecessor wrapper | `extendPredecessor` (private) |
| Public Algo C correctness theorem | `internalAddC_toSet` |

Some names reflect the executable list implementation rather than the
mathematics. In particular, `deleteExtraNRs` implements the forward scan, and
`internalAdd2NRs` implements separate insertion. The private wrappers package
raw lists together with proof that they have the required stored form.

Lean operations such as `List.span`, `takeWhile`, `dropWhile`,
`getLast?`, and `dropLast` implement splitting a list, selecting the
predecessor, and replacing it. They do not add new mathematical cases to the
argument. Likewise, theorem combinators and proof tactics are only mechanisms
used to assemble the facts proved above.
