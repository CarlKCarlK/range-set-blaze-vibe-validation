import RangeSetBlaze.AlgoC

namespace RangeSetBlaze

open IntRange
open IntRange.NR
open scoped IntRange.NR

/-!
# Algo D: proved insertion through an abstract cursor gap

Algo D is a fully proved executable model of the cursor-shaped Rust insertion
algorithm.  It represents the cursor by `CursorGap`, a split of the canonical
range list:

```text
left ranges | right ranges
            ^ cursor
```

`lowerBoundGap` models the one lower-bound search; the two list sides model
`peek_prev`, `peek_next`, `remove_next`, and `insert_before`.  The proof covers
both canonical normalized output ranges and exact `toSet` union semantics.

Rust mutates a reused predecessor incrementally.  Lean intentionally carries
that range as a functional accumulator and reconstructs it once after the
scan.  Cached `len` is outside the model.  Production complexity is intended
to be `O(log r + k)` for `r` stored and `k` absorbed ranges, but complexity is
not formally proved.
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

/-- Adding an input contained in a stored range changes neither the represented
set nor the already-canonical list. -/
private theorem contained_input_preserves_union
    (ranges : List NR) (input container : NR)
    (hmem : container ∈ ranges)
    (hstart : container.val.lo ≤ input.val.lo)
    (hend : input.val.hi ≤ container.val.hi) :
    rangesToSet ranges = rangesToSet ranges ∪ input.val.toSet := by
  symm
  apply Set.union_eq_left.mpr
  refine Set.Subset.trans ?_
    (rangeToSet_subset_rangesToSet_of_mem hmem)
  intro x hx
  rw [IntRange.mem_toSet_iff] at hx ⊢
  exact ⟨le_trans hstart hx.1, le_trans hx.2 hend⟩

/-- Reusing a mergeable predecessor, replacing it by its glue with the input,
and absorbing the right prefix preserves both canonical form and exact union. -/
private theorem predecessor_reuse_preserves_order_and_union
    (ranges : List NR) (input predecessor : NR)
    (hpw : List.Pairwise NR.before ranges)
    (hprev : (lowerBoundGap input.val.lo ranges).peekPrev = some predecessor)
    (hmerge : NR.mergeable predecessor input) :
    let gap := lowerBoundGap input.val.lo ranges
    let grown := NR.glue predecessor input
    let scanned := absorbSuccessors grown gap.right
    let result := replaceStoredPredecessor gap scanned.fst scanned.snd
    List.Pairwise NR.before result ∧
      rangesToSet result = rangesToSet ranges ∪ input.val.toSet := by
  dsimp
  have hgap := lowerBoundGap_spec ranges input.val.lo hpw
  rcases hgap with ⟨hsource, hleft, hright⟩
  let gap := lowerBoundGap input.val.lo ranges
  change ranges = gap.left ++ gap.right at hsource
  change (∀ nr ∈ gap.left, nr.val.lo < input.val.lo) at hleft
  change (∀ nr ∈ gap.right, input.val.lo ≤ nr.val.lo) at hright
  change gap.left.getLast? = some predecessor at hprev
  obtain ⟨pre, hprefix⟩ := (List.getLast?_eq_some_iff.mp hprev)
  have hleft_decomp : gap.left = pre ++ [predecessor] := hprefix
  have hpred_left : ∀ nr ∈ pre, nr ≺ predecessor := by
    intro nr hmem
    have hp : List.Pairwise NR.before gap.left :=
      (List.pairwise_append.mp (hsource ▸ hpw)).1
    rw [hleft_decomp] at hp
    exact (List.pairwise_append.mp hp).2.2 nr hmem predecessor (by simp)
  have hpred_lo : predecessor.val.lo < input.val.lo := by
    apply hleft
    rw [hleft_decomp]
    simp
  have hscan := absorbSuccessors_preserves_order_lower_bound_and_union
    predecessor.val.lo (NR.glue predecessor input) gap.right
    (by
      simp [NR.glue, IntRange.mergeRange, min_eq_left (le_of_lt hpred_lo)])
    (List.pairwise_append.mp (hsource ▸ hpw)).2.1
    (by
      intro nr hmem
      exact le_trans (le_of_lt hpred_lo) (hright nr hmem))
  have hprefix_pair : List.Pairwise NR.before pre := by
    have hp : List.Pairwise NR.before gap.left :=
      (List.pairwise_append.mp (hsource ▸ hpw)).1
    rw [hleft_decomp] at hp
    exact (List.pairwise_append.mp hp).1
  have hprefix_scan : ∀ p ∈ pre, ∀ nr ∈
      ((absorbSuccessors (NR.glue predecessor input) gap.right).fst ::
        (absorbSuccessors (NR.glue predecessor input) gap.right).snd),
      p ≺ nr := by
    intro p hp nr hn
    exact lt_of_lt_of_le (hpred_left p hp) (hscan.2.1 nr hn)
  have hpair : List.Pairwise NR.before
      (pre ++ (absorbSuccessors (NR.glue predecessor input) gap.right).fst ::
        (absorbSuccessors (NR.glue predecessor input) gap.right).snd) := by
    apply List.pairwise_append.mpr
    refine ⟨hprefix_pair, hscan.1, ?_⟩
    exact hprefix_scan
  have hsets : rangesToSet
      (pre ++ (absorbSuccessors (NR.glue predecessor input) gap.right).fst ::
        (absorbSuccessors (NR.glue predecessor input) gap.right).snd) =
      rangesToSet ranges ∪ input.val.toSet := by
    rw [rangesToSet_append, hscan.2.2]
    rw [NR.glue_sets predecessor input hmerge]
    have hsourceSet : rangesToSet ranges =
        rangesToSet pre ∪ predecessor.val.toSet ∪ rangesToSet gap.right := by
      rw [hsource, hleft_decomp, rangesToSet_append]
      simp [rangesToSet_append]
    rw [hsourceSet]
    ac_rfl
  exact ⟨by simpa [replaceStoredPredecessor, gap, hleft_decomp] using hpair,
    by simpa [replaceStoredPredecessor, gap, hleft_decomp] using hsets⟩

/-- With a genuine left boundary, scanning a fresh input accumulator and then
performing `insert_before` preserves canonical form and exact union. -/
private theorem fresh_accumulator_preserves_order_and_union
    (ranges : List NR) (input : NR)
    (hpw : List.Pairwise NR.before ranges)
    (hleftPred : ∀ predecessor,
      (lowerBoundGap input.val.lo ranges).peekPrev = some predecessor →
      predecessor ≺ input) :
    let gap := lowerBoundGap input.val.lo ranges
    let scanned := absorbSuccessors input gap.right
    let result := gap.insertBefore scanned.fst scanned.snd
    List.Pairwise NR.before result ∧
      rangesToSet result = rangesToSet ranges ∪ input.val.toSet := by
  dsimp
  have hgap := lowerBoundGap_spec ranges input.val.lo hpw
  rcases hgap with ⟨hsource, _, hright⟩
  let gap := lowerBoundGap input.val.lo ranges
  change ranges = gap.left ++ gap.right at hsource
  change (∀ nr ∈ gap.right, input.val.lo ≤ nr.val.lo) at hright
  have hwhole : List.Pairwise NR.before (gap.left ++ gap.right) :=
    hsource ▸ hpw
  have hscan := absorbSuccessors_preserves_order_lower_bound_and_union
    input.val.lo input gap.right rfl
    (List.pairwise_append.mp hwhole).2.1 hright
  have hleft_pair : List.Pairwise NR.before gap.left :=
    (List.pairwise_append.mp hwhole).1
  have hleft_before_input : ∀ p ∈ gap.left, p ≺ input := by
    intro p hp
    by_cases hempty : gap.left = []
    · simp [hempty] at hp
    · have hlast := List.getLast?_eq_some_getLast hempty
      let predecessor := gap.left.getLast hempty
      have hprev : gap.left.getLast? = some predecessor := hlast
      have hpred_input := hleftPred predecessor
        (by simpa [gap, CursorGap.peekPrev] using hprev)
      have hdecomp : ∃ pre, gap.left = pre ++ [predecessor] :=
        List.getLast?_eq_some_iff.mp hprev
      rcases hdecomp with ⟨pre, hdecomp⟩
      have hpwleft := hleft_pair
      rw [hdecomp] at hpwleft
      rcases (by simpa [hdecomp] using hp : p ∈ pre ∨ p = predecessor) with hp | rfl
      · have hp_before_pred := (List.pairwise_append.mp hpwleft).2.2 p
          hp predecessor (by simp)
        exact before_trans hp_before_pred hpred_input
      · exact hpred_input
  have hleft_to_scan : ∀ p ∈ gap.left, ∀ nr ∈
      (absorbSuccessors input gap.right).fst ::
        (absorbSuccessors input gap.right).snd, p ≺ nr := by
    intro p hp nr hn
    exact lt_of_lt_of_le (hleft_before_input p hp) (hscan.2.1 nr hn)
  have hpair : List.Pairwise NR.before
      (gap.left ++ (absorbSuccessors input gap.right).fst ::
        (absorbSuccessors input gap.right).snd) := by
    apply List.pairwise_append.mpr
    exact ⟨hleft_pair, hscan.1, hleft_to_scan⟩
  have hsets : rangesToSet
      (gap.left ++ (absorbSuccessors input gap.right).fst ::
        (absorbSuccessors input gap.right).snd) =
      rangesToSet ranges ∪ input.val.toSet := by
    rw [rangesToSet_append, hscan.2.2]
    have hsourceSet : rangesToSet ranges =
        rangesToSet gap.left ∪ rangesToSet gap.right := by
      rw [hsource, rangesToSet_append]
    rw [hsourceSet]
    ac_rfl
  exact ⟨by simpa [CursorGap.insertBefore, gap] using hpair,
    by simpa [CursorGap.insertBefore, gap] using hsets⟩

/-- The raw cursor-shaped computation has the two properties needed to package
its output as a `RangeSetBlaze`.  The proof follows the executable branches and
composes the preceding semantic obligations. -/
private theorem internalAddDNRs_preserves_order_and_union
    (ranges : List NR) (input : NR)
    (hpw : List.Pairwise NR.before ranges) :
    List.Pairwise NR.before (internalAddDNRs ranges input) ∧
      rangesToSet (internalAddDNRs ranges input) =
        rangesToSet ranges ∪ input.val.toSet := by
  classical
  let gap := lowerBoundGap input.val.lo ranges
  have hgap := lowerBoundGap_spec ranges input.val.lo hpw
  rcases hgap with ⟨hsource, hleft, _⟩
  change ranges = gap.left ++ gap.right at hsource
  change (∀ nr ∈ gap.left, nr.val.lo < input.val.lo) at hleft
  have hpred_mem : ∀ predecessor,
      gap.left.getLast? = some predecessor → predecessor ∈ ranges := by
    intro predecessor hpred
    rw [hsource]
    exact List.mem_append_left _
      (List.mem_of_mem_getLast? (by rw [hpred]; simp))
  have hsucc_mem : ∀ successor,
      gap.right.head? = some successor → successor ∈ ranges := by
    intro successor hsucc
    rw [hsource]
    exact List.mem_append_right _
      (List.mem_of_mem_head? (by rw [hsucc]; simp))
  dsimp [internalAddDNRs]
  split
  · rename_i predecessor hprev
    change gap.left.getLast? = some predecessor at hprev
    split
    · rename_i hmerge
      split
      · rename_i hcontains
        exact ⟨hpw, contained_input_preserves_union ranges input predecessor
          (hpred_mem predecessor hprev)
          (le_of_lt (hleft predecessor (by
            exact List.mem_of_mem_getLast? (by rw [hprev]; simp))))
          hcontains⟩
      · rename_i _hextend
        simpa [gap] using
          predecessor_reuse_preserves_order_and_union ranges input predecessor hpw
            hprev hmerge
    · rename_i hnotmerge
      have hleftPred : ∀ pred,
          (lowerBoundGap input.val.lo ranges).peekPrev = some pred → pred ≺ input := by
        intro pred hpred
        change gap.left.getLast? = some pred at hpred
        have heq : pred = predecessor := by simpa [hprev] using hpred.symm
        subst pred
        have hpred_lo : predecessor.val.lo ≤ input.val.lo :=
          (hleft predecessor (List.mem_of_mem_getLast? (by rw [hprev]; simp))).le
        by_contra hbefore
        exact hnotmerge (NR.mergeable_of_startsBefore_of_not_before hpred_lo hbefore)
      split
      · rename_i successor hnext
        change gap.right.head? = some successor at hnext
        split
        · rename_i hcontains
          exact ⟨hpw, contained_input_preserves_union ranges input successor
            (hsucc_mem successor hnext) hcontains.1.le hcontains.2⟩
        · rename_i _hnotcontains
          exact fresh_accumulator_preserves_order_and_union ranges input hpw hleftPred
      · rename_i _hnext
        exact fresh_accumulator_preserves_order_and_union ranges input hpw hleftPred
  · rename_i hprev
    change gap.left.getLast? = none at hprev
    have hleftPred : ∀ pred,
        (lowerBoundGap input.val.lo ranges).peekPrev = some pred → pred ≺ input := by
      intro pred hpred
      change gap.left.getLast? = some pred at hpred
      rw [hprev] at hpred
      simp at hpred
    cases hnext : gap.right.head? with
    | some successor =>
      simp [gap, CursorGap.peekNext, hnext]
      split
      · rename_i hcontains
        exact ⟨hpw, contained_input_preserves_union ranges input successor
          (hsucc_mem successor hnext) hcontains.1.le hcontains.2⟩
      · rename_i _hnotcontains
        exact fresh_accumulator_preserves_order_and_union ranges input hpw hleftPred
    | none =>
      simp [gap, CursorGap.peekNext, hnext]
      exact fresh_accumulator_preserves_order_and_union ranges input hpw hleftPred

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

The first examples assert concrete results without relying on Algo C.  The
remaining examples compare Algo D's concrete range lists with Algo C across
twelve control-flow situations.
-/

private def testNR (lo hi : Int) (h : lo ≤ hi := by omega) : NR :=
  ⟨{ lo := lo, hi := hi }, h⟩

private def testSet (ranges : List NR)
    (ok : List.Pairwise NR.before ranges := by native_decide) : RangeSetBlaze :=
  ⟨ranges, ok⟩

private def sameAsC (s : RangeSetBlaze) (r : IntRange) : Bool :=
  (internalAddD s r).ranges == (internalAddC s r).ranges

example : (internalAddD (testSet [testNR 10 30]) { lo := 10, hi := 20 }).ranges =
    [testNR 10 30] := by native_decide
example : (internalAddD (testSet [testNR 10 15]) { lo := 10, hi := 20 }).ranges =
    [testNR 10 20] := by native_decide
example : (internalAddD (testSet [testNR 1 5, testNR 10 15]) { lo := 4, hi := 11 }).ranges =
    [testNR 1 15] := by native_decide
example : (internalAddD
    (testSet [testNR 10 12, testNR 16 18, testNR 22 25])
    { lo := 11, hi := 23 }).ranges = [testNR 10 25] := by native_decide
example : (internalAddD (testSet [testNR 10 12, testNR 20 22])
    { lo := 11, hi := 15 }).ranges = [testNR 10 15, testNR 20 22] := by native_decide

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
