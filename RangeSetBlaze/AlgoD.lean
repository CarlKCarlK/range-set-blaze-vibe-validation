import RangeSetBlaze.AlgoC

namespace RangeSetBlaze

open IntRange
open IntRange.NR
open scoped IntRange.NR

/-!
# Algo D: insertion through an abstract cursor gap

Algo D models the proposed Rust insertion based on the experimental
`BTreeMap` cursor API.  It intentionally models neither B-tree nodes nor the
cursor implementation.  A cursor is represented by `CursorGap`, a split of
the canonical range list:

```text
left ranges | right ranges
            ^ cursor
```

`lowerBoundGap start` performs the model's one search.  It puts ranges whose
lower endpoint is strictly below `start` on the left and ranges beginning at
or after `start` on the right.  Thus `left.getLast?` models `peek_prev`, the
head of `right` models `peek_next`, dropping that head models `remove_next`,
and appending immediately before `right` models `insert_before`.

The executable definition retains the Rust control-flow shape: reject an
empty input; inspect at most one predecessor; return when that predecessor
contains the input; otherwise reuse and extend it; separately check whether a
range at exactly the input start contains the input; scan the right side once;
and insert a fresh accumulator only on the path that did not reuse the
predecessor.

In Rust, when the predecessor is reused, its endpoint is mutated before the
successor scan and possibly again afterward.  Algo D models the same operation
functionally: it carries that range as the scan accumulator and writes the
final range during reconstruction.  The successor decisions and resulting
normalized ranges are identical.

The central proof theorem says that the forward scan preserves canonical
ordering, its lower-bound fact, and the exact represented union in one
induction.  The lower-bound split and both containment branches are proved as
well; the remaining obligations reconstruct the two cursor branches and
follow the executable dispatcher.  All executable definitions are complete.

For a production `BTreeMap` with `r` stored ranges and `k` absorbed ranges,
the intended cost is `O(log r + k)`: one lower-bound search, one predecessor
inspection, and one forward cursor walk with one visit per removed range.
This Lean list model specifies that access pattern but does not formally model
complexity.  It also intentionally omits Rust's cached cardinality field.  The
only correctness targets here are canonical ranges and exact `toSet` union.
-/

/-- The smallest useful model of a mutable map cursor: a gap between two list
pieces.  This is Algo-D-private rather than a speculative generic cursor API. -/
private structure CursorGap where
  left : List NR
  right : List NR

/-- The model's single lower-bound search. -/
private def lowerBoundGap (start : Int) (ranges : List NR) : CursorGap :=
  let split := List.span (fun nr => decide (nr.val.lo < start)) ranges
  { left := split.fst, right := split.snd }

/-- `peek_prev`: inspect the range immediately left of the gap. -/
private def CursorGap.peekPrev (gap : CursorGap) : Option NR :=
  gap.left.getLast?

/-- `peek_next`: inspect the range immediately right of the gap. -/
private def CursorGap.peekNext (gap : CursorGap) : Option NR :=
  gap.right.head?

/-- `insert_before`: after zero or more `remove_next` operations, materialize a
range immediately left of the gap's remaining right side. -/
private def CursorGap.insertBefore
    (gap : CursorGap) (nr : NR) (remainingRight : List NR) : List NR :=
  gap.left ++ nr :: remainingRight

/-- Remove and glue each mergeable first range on the right, stopping at the
first genuine gap.  Recursive descent through `tail` is repeated
`remove_next`; the returned suffix is the final right side of the cursor. -/
private def absorbSuccessors (current : NR) : List NR → NR × List NR
  | [] => (current, [])
  | next :: tail =>
      if _hmerge : NR.mergeable current next then
        absorbSuccessors (NR.glue current next) tail
      else
        (current, next :: tail)

/-- Replace the predecessor already stored on the left of the cursor.  Unlike
the fresh path, this reconstruction performs no `insertBefore` operation. -/
private def replaceStoredPredecessor
    (gap : CursorGap) (current : NR) (remainingRight : List NR) : List NR :=
  gap.left.dropLast ++ current :: remainingRight

/-- Proof-free list computation for Algo D.  Its only split is
`lowerBoundGap`; all later progress is a forward consumption of `gap.right`. -/
private def internalAddDNRs (ranges : List NR) (input : NR) : List NR :=
  let gap := lowerBoundGap input.val.lo ranges
  match gap.peekPrev with
  | some predecessor =>
      if _hmerge : NR.mergeable predecessor input then
        if input.val.hi ≤ predecessor.val.hi then
          -- The predecessor already contains the input.
          ranges
        else
          -- Reuse the physically stored predecessor and walk right once.
          let grown := NR.glue predecessor input
          let scanned := absorbSuccessors grown gap.right
          replaceStoredPredecessor gap scanned.fst scanned.snd
      else
        -- The predecessor is separated; inspect exact-start containment on
        -- the right before beginning the fresh-accumulator walk.
        match gap.peekNext with
        | some successor =>
            if successor.val.lo = input.val.lo ∧ input.val.hi ≤ successor.val.hi then
              ranges
            else
              let scanned := absorbSuccessors input gap.right
              gap.insertBefore scanned.fst scanned.snd
        | none =>
            let scanned := absorbSuccessors input gap.right
            gap.insertBefore scanned.fst scanned.snd
  | none =>
      -- With no predecessor, an equal-start containing range is necessarily
      -- the first range on the right.
      match gap.peekNext with
      | some successor =>
          if successor.val.lo = input.val.lo ∧ input.val.hi ≤ successor.val.hi then
            ranges
          else
            let scanned := absorbSuccessors input gap.right
            gap.insertBefore scanned.fst scanned.snd
      | none =>
          let scanned := absorbSuccessors input gap.right
          gap.insertBefore scanned.fst scanned.snd

/-! ## Proof architecture

Ordering, boundary information, and set semantics for `absorbSuccessors`
deliberately share one theorem and therefore one induction.
-/

/-- A lower-bound gap reconstructs the source, and its two sides satisfy the
strict/non-strict lower-endpoint boundary induced by the search key. -/
private theorem lowerBoundGap_spec
    (ranges : List NR) (start : Int)
    (hpw : List.Pairwise NR.before ranges) :
    let gap := lowerBoundGap start ranges
    ranges = gap.left ++ gap.right ∧
      (∀ nr ∈ gap.left, nr.val.lo < start) ∧
      (∀ nr ∈ gap.right, start ≤ nr.val.lo) := by
  dsimp [lowerBoundGap]
  rw [List.span_eq_takeWhile_dropWhile]
  change ranges = List.takeWhile _ ranges ++ List.dropWhile _ ranges ∧
    (∀ nr ∈ List.takeWhile _ ranges, nr.val.lo < start) ∧
    (∀ nr ∈ List.dropWhile _ ranges, start ≤ nr.val.lo)
  refine ⟨List.takeWhile_append_dropWhile.symm, ?_, ?_⟩
  · intro nr hmem
    have hsatisfies := List.mem_takeWhile_imp hmem
    simpa using hsatisfies
  · induction ranges with
    | nil => simp
    | cons first rest ih =>
        by_cases hfirst : first.val.lo < start
        · rw [List.dropWhile_cons_of_pos (by simp [hfirst])]
          exact ih hpw.tail
        · rw [List.dropWhile_cons_of_neg (by simp [hfirst])]
          intro nr hmem
          rw [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact not_lt.mp hfirst
          · exact le_trans (not_lt.mp hfirst)
              (NR.before_lo_lt (List.rel_of_pairwise_cons hpw hmem)).le

/-- The forward cursor walk preserves canonical order, the accumulator's
lower-bound interface, and the exact union in one semantic contract. -/
private theorem absorbSuccessors_preserves_order_lower_bound_and_union
    (start : Int) (current : NR) (right : List NR)
    (hcurrent : current.val.lo = start)
    (hright : List.Pairwise NR.before right)
    (hlower : ∀ nr ∈ right, start ≤ nr.val.lo) :
    let result := absorbSuccessors current right
    List.Pairwise NR.before (result.fst :: result.snd) ∧
      (∀ nr ∈ result.fst :: result.snd, start ≤ nr.val.lo) ∧
      rangesToSet (result.fst :: result.snd) =
        current.val.toSet ∪ rangesToSet right := by
  induction right generalizing current with
  | nil => simp [absorbSuccessors, hcurrent]
  | cons next tail ih =>
      by_cases hmerge : NR.mergeable current next
      · have hnext : start ≤ next.val.lo := hlower next (by simp)
        have horder : current.val.lo ≤ next.val.lo := by
          rw [hcurrent]
          exact hnext
        have hglueStart : (NR.glue current next).val.lo = start := by
          change min current.val.lo next.val.lo = start
          rw [min_eq_left horder, hcurrent]
        have htailLower : ∀ nr ∈ tail, start ≤ nr.val.lo := by
          intro nr hmem
          exact hlower nr (by simp [hmem])
        have hrec := ih (NR.glue current next) hglueStart hright.tail htailLower
        simpa [absorbSuccessors, hmerge, NR.glue_sets current next hmerge,
          Set.union_assoc] using hrec
      · have hnext : start ≤ next.val.lo := hlower next (by simp)
        have hcurrentBefore : current ≺ next := by
          by_contra hnotBefore
          exact hmerge (NR.mergeable_of_startsBefore_of_not_before
            (show current.val.lo ≤ next.val.lo by rw [hcurrent]; exact hnext)
            hnotBefore)
        have hcurrentBeforeTail : ∀ nr ∈ tail, current ≺ nr := by
          intro nr hmem
          exact before_trans hcurrentBefore
            (List.rel_of_pairwise_cons hright hmem)
        have hresult : absorbSuccessors current (next :: tail) =
            (current, next :: tail) := by
          simp [absorbSuccessors, hmerge]
        rw [hresult]
        dsimp only [Prod.fst, Prod.snd]
        refine ⟨?_, ?_, rfl⟩
        · apply List.pairwise_cons.mpr
          refine ⟨?_, hright⟩
          intro nr hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with heq | hmem
          · exact heq ▸ hcurrentBefore
          · exact hcurrentBeforeTail nr hmem
        · intro nr hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with heq | hmem
          · exact heq ▸ hcurrent.ge
          · exact hlower nr (by simpa using hmem)

/-- If the predecessor contains the input, adding the input changes neither
the represented set nor the already-canonical list. -/
private theorem predecessor_containment_preserves_union
    (ranges : List NR) (input predecessor : NR)
    (hmem : predecessor ∈ ranges)
    (hstart : predecessor.val.lo ≤ input.val.lo)
    (hend : input.val.hi ≤ predecessor.val.hi) :
    rangesToSet ranges = rangesToSet ranges ∪ input.val.toSet := by
  symm
  apply Set.union_eq_left.mpr
  refine Set.Subset.trans ?_
    (rangeToSet_subset_rangesToSet_of_mem hmem)
  intro x hx
  rw [IntRange.mem_toSet_iff] at hx ⊢
  exact ⟨le_trans hstart hx.1, le_trans hx.2 hend⟩

/-- A containing range with exactly the input start lives on the right of the
strict lower-bound gap and likewise makes insertion a semantic no-op. -/
private theorem exactStart_successor_containment_preserves_union
    (ranges : List NR) (input successor : NR)
    (hmem : successor ∈ ranges)
    (hstart : successor.val.lo = input.val.lo)
    (hend : input.val.hi ≤ successor.val.hi) :
    rangesToSet ranges = rangesToSet ranges ∪ input.val.toSet := by
  symm
  apply Set.union_eq_left.mpr
  refine Set.Subset.trans ?_
    (rangeToSet_subset_rangesToSet_of_mem hmem)
  intro x hx
  rw [IntRange.mem_toSet_iff] at hx ⊢
  exact ⟨hstart ▸ hx.1, le_trans hx.2 hend⟩

/-- Reusing a mergeable predecessor, replacing it by its glue with the input,
and absorbing the right prefix preserves both canonical form and exact union. -/
private theorem predecessor_reuse_preserves_order_and_union
    (ranges : List NR) (input predecessor : NR)
    (hpw : List.Pairwise NR.before ranges)
    (hprev : (lowerBoundGap input.val.lo ranges).peekPrev = some predecessor)
    (hmerge : NR.mergeable predecessor input)
    (hextend : predecessor.val.hi < input.val.hi) :
    let gap := lowerBoundGap input.val.lo ranges
    let grown := NR.glue predecessor input
    let scanned := absorbSuccessors grown gap.right
    let result := replaceStoredPredecessor gap scanned.fst scanned.snd
    List.Pairwise NR.before result ∧
      rangesToSet result = rangesToSet ranges ∪ input.val.toSet := by
  sorry

/-- With a genuine left boundary, scanning a fresh input accumulator and then
performing `insert_before` preserves canonical form and exact union. -/
private theorem fresh_accumulator_preserves_order_and_union
    (ranges : List NR) (input : NR)
    (hpw : List.Pairwise NR.before ranges)
    (hleft : ∀ predecessor,
      (lowerBoundGap input.val.lo ranges).peekPrev = some predecessor →
      predecessor ≺ input) :
    let gap := lowerBoundGap input.val.lo ranges
    let scanned := absorbSuccessors input gap.right
    let result := gap.insertBefore scanned.fst scanned.snd
    List.Pairwise NR.before result ∧
      rangesToSet result = rangesToSet ranges ∪ input.val.toSet := by
  sorry

/-- The raw cursor-shaped computation has the two properties needed to package
its output as a `RangeSetBlaze`.  Its eventual proof follows the executable
branches and composes the preceding semantic obligations. -/
private theorem internalAddDNRs_preserves_order_and_union
    (ranges : List NR) (input : NR)
    (hpw : List.Pairwise NR.before ranges) :
    List.Pairwise NR.before (internalAddDNRs ranges input) ∧
      rangesToSet (internalAddDNRs ranges input) =
        rangesToSet ranges ∪ input.val.toSet := by
  sorry

/-- Algo D insertion.  Empty intervals are no-ops; nonempty intervals execute
the cursor-shaped raw algorithm and package its canonical-list contract. -/
def internalAddD (s : RangeSetBlaze) (r : IntRange) : RangeSetBlaze :=
  if hempty : r.hi < r.lo then
    s
  else
    let input : NR := ⟨r, not_lt.mp hempty⟩
    let result := internalAddDNRs s.ranges input
    ⟨result, (internalAddDNRs_preserves_order_and_union s.ranges input s.ok).1⟩

/-- Algo D's set-level correctness target. -/
theorem internalAddD_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAddD s r).toSet = s.toSet ∪ r.toSet := by
  by_cases hempty : r.hi < r.lo
  · simp [internalAddD, hempty, IntRange.toSet_eq_empty_of_hi_lt_lo hempty]
  · let input : NR := ⟨r, not_lt.mp hempty⟩
    have hspec := internalAddDNRs_preserves_order_and_union s.ranges input s.ok
    simpa [internalAddD, hempty, RangeSetBlaze.toSet, input] using hspec.2

/-! ## Small executable regression examples

These examples compare Algo D's concrete range lists with Algo C.  Together
they cover the twelve control-flow situations listed in the v0 brief.
-/

private def testNR (lo hi : Int) (h : lo ≤ hi := by omega) : NR :=
  ⟨{ lo := lo, hi := hi }, h⟩

private def testSet (ranges : List NR)
    (ok : List.Pairwise NR.before ranges := by native_decide) : RangeSetBlaze :=
  ⟨ranges, ok⟩

private def sameAsC (s : RangeSetBlaze) (r : IntRange) : Bool :=
  (internalAddD s r).ranges == (internalAddC s r).ranges

example : sameAsC (testSet [testNR 10 12]) { lo := 5, hi := 4 } := by native_decide
example : sameAsC (testSet []) { lo := 5, hi := 7 } := by native_decide
example : sameAsC (testSet [testNR 10 12]) { lo := 1, hi := 3 } := by native_decide
example : sameAsC (testSet [testNR 10 12]) { lo := 20, hi := 22 } := by native_decide
example : sameAsC (testSet [testNR 1 5, testNR 10 20]) { lo := 12, hi := 15 } := by native_decide
example : sameAsC (testSet [testNR 10 20, testNR 30 35]) { lo := 10, hi := 15 } := by native_decide
example : sameAsC (testSet [testNR 1 3, testNR 10 12]) { lo := 5, hi := 7 } := by native_decide
example : sameAsC (testSet [testNR 10 12, testNR 20 22]) { lo := 7, hi := 9 } := by native_decide
example : sameAsC (testSet [testNR 10 12, testNR 14 16, testNR 18 20, testNR 30 35]) { lo := 7, hi := 18 } := by native_decide
example : sameAsC (testSet [testNR 1 5, testNR 10 12]) { lo := 4, hi := 7 } := by native_decide
example : sameAsC (testSet [testNR 1 5, testNR 8 10, testNR 20 22]) { lo := 4, hi := 7 } := by native_decide
example : sameAsC (testSet [testNR 1 5, testNR 8 10, testNR 13 15, testNR 30 35]) { lo := 4, hi := 13 } := by native_decide

end RangeSetBlaze
