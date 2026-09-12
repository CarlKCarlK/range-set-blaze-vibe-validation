import RangeSetBlaze.Basic

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
  · simpa [List.span_eq_takeWhile_dropWhile] using
      NR.strict_start_split_suffix_lower_bound ranges start hpw

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
          exact NR.before_trans hcurrentBefore
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
  have hwhole : List.Pairwise NR.before (gap.left ++ gap.right) := hsource ▸ hpw
  obtain ⟨hleftPair, hrightPair, _⟩ := List.pairwise_append.mp hwhole
  rw [hleft_decomp] at hleftPair
  obtain ⟨hprefixPair, _, hprefixBeforePredecessor⟩ :=
    List.pairwise_append.mp hleftPair
  have hpred_left : ∀ nr ∈ pre, nr ≺ predecessor := by
    intro nr hmem
    exact hprefixBeforePredecessor nr hmem predecessor (by simp)
  have hpred_lo : predecessor.val.lo < input.val.lo := by
    apply hleft
    rw [hleft_decomp]
    simp
  have hscan := absorbSuccessors_preserves_order_lower_bound_and_union
    predecessor.val.lo (NR.glue predecessor input) gap.right
    (by
      simp [NR.glue, IntRange.mergeRange, min_eq_left (le_of_lt hpred_lo)])
    hrightPair
    (by
      intro nr hmem
      exact le_trans (le_of_lt hpred_lo) (hright nr hmem))
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
    refine ⟨hprefixPair, hscan.1, ?_⟩
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
        exact NR.before_trans hp_before_pred hpred_input
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
        refine ⟨hpw, (Set.union_eq_left.mpr ?_).symm⟩
        exact toSet_subset_rangesToSet_of_mem_of_bounds
          (hpred_mem predecessor hprev)
          (le_of_lt (hleft predecessor (by
            exact List.mem_of_mem_getLast? (by rw [hprev]; simp))))
          hcontains
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
          refine ⟨hpw, (Set.union_eq_left.mpr ?_).symm⟩
          exact toSet_subset_rangesToSet_of_mem_of_bounds
            (hsucc_mem successor hnext) hcontains.1.le hcontains.2
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
        refine ⟨hpw, (Set.union_eq_left.mpr ?_).symm⟩
        exact toSet_subset_rangesToSet_of_mem_of_bounds
          (hsucc_mem successor hnext) hcontains.1.le hcontains.2
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
    ⟨result, (internalAddDNRs_preserves_order_and_union s.ranges input s.canonical).1⟩

/-- Algo D's set-level correctness target. -/
theorem internalAddD_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAddD s r).toSet = s.toSet ∪ r.toSet := by
  by_cases hempty : r.hi < r.lo
  · simp [internalAddD, hempty, IntRange.toSet_eq_empty_of_hi_lt_lo hempty]
  · let input : NR := ⟨r, not_lt.mp hempty⟩
    have hspec := internalAddDNRs_preserves_order_and_union s.ranges input s.canonical
    simpa [internalAddD, hempty, RangeSetBlaze.toSet, input] using hspec.2

/-! ## Algo D with cached length

DLen is the cursor algorithm above with the production `len` updates made
explicit.  The cache is a mathematical `Int`; cardinalities remain `Nat`.
-/

/-- The externally useful result of cached-length Algo D insertion. -/
structure DLenResult where
  setResult : RangeSetBlaze
  cachedLength : Int
  deriving Repr

/-- Proof-free output used while the cursor-shaped result is being assembled. -/
private structure DLenRawResult where
  ranges : List NR
  cachedLength : Int

/-- Cursor successor absorption with Rust's subtract-on-removal bookkeeping. -/
private structure DLenScanResult where
  current : NR
  pending : List NR
  cachedLength : Int

private def mkDLenNR (lo hi : Int) (h : lo ≤ hi) : NR :=
  ⟨{ lo := lo, hi := hi }, h⟩

private def absorbSuccessorsDLen
    (current : NR) (right : List NR) (cachedLength : Int) : DLenScanResult :=
  match right with
  | [] => ⟨current, [], cachedLength⟩
  | next :: tail =>
      if _hmerge : NR.mergeable current next then
        absorbSuccessorsDLen (NR.glue current next) tail
          (cachedLength - Int.ofNat next.val.cardinality)
      else
        ⟨current, next :: tail, cachedLength⟩

private def finishDLenScan
    (current : NR) (right : List NR) (cachedLength : Int)
    (pendingWasStored : Bool) (originalEnd : Int) : DLenScanResult :=
  let scanned := absorbSuccessorsDLen current right cachedLength
  if pendingWasStored && originalEnd < scanned.current.val.hi then
    { scanned with
      cachedLength := scanned.cachedLength +
        Int.ofNat (IntRange.cardinality
          { lo := originalEnd, hi := scanned.current.val.hi - 1 }) }
  else
    scanned

/-- The fresh cursor path: remove swallowed successors, insert the accumulated
range, then add that newly represented range to the cache. -/
private def freshInsertDLen
    (gap : CursorGap) (input : NR) (cachedLength : Int) : DLenRawResult :=
  let scanned := finishDLenScan input gap.right cachedLength false input.val.hi
  ⟨gap.insertBefore scanned.current scanned.pending,
    scanned.cachedLength + Int.ofNat scanned.current.val.cardinality⟩

/-- The predecessor path: add the predecessor's newly covered tail, remove
swallowed successors, and add any final extension beyond the inserted end. -/
private def extendPredecessorDLen
    (gap : CursorGap) (predecessor input : NR) (cachedLength : Int) : DLenRawResult :=
  let extendedHi := max predecessor.val.hi input.val.hi
  let extended := mkDLenNR predecessor.val.lo extendedHi
    (predecessor.property.trans (le_max_left _ _))
  let afterExtension := cachedLength +
    Int.ofNat (IntRange.cardinality
      { lo := predecessor.val.hi, hi := input.val.hi - 1 })
  let scanned := finishDLenScan extended gap.right afterExtension true input.val.hi
  ⟨gap.left.dropLast ++ scanned.current :: scanned.pending, scanned.cachedLength⟩

/-- DLen's executable control flow is Algo D's control flow with only cache
updates threaded through the fresh and predecessor scan paths. -/
private def internalAddDLenRaw
    (ranges : List NR) (cachedLength : Int) (r : IntRange) : DLenRawResult :=
  if hempty : r.hi < r.lo then
    ⟨ranges, cachedLength⟩
  else
    let input : NR := ⟨r, not_lt.mp hempty⟩
    let gap := lowerBoundGap r.lo ranges
    match gap.peekPrev with
    | some predecessor =>
        if _hmerge : NR.mergeable predecessor input then
          if _hcovered : r.hi ≤ predecessor.val.hi then
            ⟨ranges, cachedLength⟩
          else
            extendPredecessorDLen gap predecessor input cachedLength
        else
          match gap.peekNext with
          | some successor =>
              if _hcovered : successor.val.lo = r.lo ∧ r.hi ≤ successor.val.hi then
                ⟨ranges, cachedLength⟩
              else
                freshInsertDLen gap input cachedLength
          | none => freshInsertDLen gap input cachedLength
    | none =>
        match gap.peekNext with
        | some successor =>
            if _hcovered : successor.val.lo = r.lo ∧ r.hi ≤ successor.val.hi then
              ⟨ranges, cachedLength⟩
            else
              freshInsertDLen gap input cachedLength
        | none => freshInsertDLen gap input cachedLength

private lemma absorbSuccessorsDLen_corresponds
    (current : NR) (right : List NR) (cachedLength : Int) :
    (absorbSuccessorsDLen current right cachedLength).current =
        (absorbSuccessors current right).fst ∧
      (absorbSuccessorsDLen current right cachedLength).pending =
        (absorbSuccessors current right).snd := by
  induction right generalizing current cachedLength with
  | nil => simp [absorbSuccessorsDLen, absorbSuccessors]
  | cons next tail ih =>
      by_cases hmerge : NR.mergeable current next
      · simp only [absorbSuccessorsDLen, absorbSuccessors, hmerge]
        exact ih _ _
      · simp [absorbSuccessorsDLen, absorbSuccessors, hmerge]

private lemma finishDLenScan_corresponds
    (current : NR) (right : List NR) (cachedLength : Int)
    (pendingWasStored : Bool) (originalEnd : Int) :
    (finishDLenScan current right cachedLength pendingWasStored originalEnd).current =
        (absorbSuccessors current right).fst ∧
      (finishDLenScan current right cachedLength pendingWasStored originalEnd).pending =
        (absorbSuccessors current right).snd := by
  have hscan := absorbSuccessorsDLen_corresponds current right cachedLength
  unfold finishDLenScan
  dsimp only
  split <;> exact ⟨hscan.1, hscan.2⟩

/-- Erasing DLen bookkeeping gives exactly Algo D's list output. -/
private theorem internalAddDLenRaw_corresponds
    (s : RangeSetBlaze) (cachedLength : Int) (r : IntRange) :
    (internalAddDLenRaw s.ranges cachedLength r).ranges =
      (internalAddD s r).ranges := by
  classical
  by_cases hempty : r.hi < r.lo
  · simp [internalAddDLenRaw, internalAddD, hempty]
  · have hD : (internalAddD s r).ranges =
        internalAddDNRs s.ranges ⟨r, not_lt.mp hempty⟩ := by
      simp [internalAddD, hempty]
    rw [hD]
    let input : NR := ⟨r, not_lt.mp hempty⟩
    let gap := lowerBoundGap r.lo s.ranges
    change (internalAddDLenRaw s.ranges cachedLength r).ranges =
      internalAddDNRs s.ranges input
    simp only [internalAddDLenRaw, hempty, input,
      internalAddDNRs]
    cases hprev : (lowerBoundGap r.lo s.ranges).peekPrev with
    | some predecessor =>
        simp_all
        split
        · split
          · simp_all
          · have hgap := lowerBoundGap_spec s.ranges r.lo s.canonical
            have hleft : ∀ nr ∈ (lowerBoundGap r.lo s.ranges).left,
                nr.val.lo < r.lo := hgap.2.1
            change (lowerBoundGap r.lo s.ranges).left.getLast? =
              some predecessor at hprev
            have hpred : predecessor.val.lo < r.lo := hleft predecessor
              (List.mem_of_mem_getLast? hprev)
            have hnr : mkDLenNR predecessor.val.lo (max predecessor.val.hi r.hi)
                (predecessor.property.trans (le_max_left _ _)) =
                NR.glue predecessor input := by
              apply Subtype.ext
              dsimp [input]
              simp [NR.glue, IntRange.mergeRange, min_eq_left hpred.le]
              rfl
            simp [extendPredecessorDLen, finishDLenScan_corresponds,
              replaceStoredPredecessor]
            rw [← hnr]
            exact ⟨rfl, rfl⟩
        · cases hnext : (lowerBoundGap r.lo s.ranges).peekNext with
          | some successor =>
              simp_all
              split
              · simp_all
              · simp [freshInsertDLen, finishDLenScan_corresponds]
          | none =>
              simp_all
              simp [freshInsertDLen, finishDLenScan_corresponds]
    | none =>
        simp_all
        cases hnext : (lowerBoundGap r.lo s.ranges).peekNext with
        | some successor =>
            simp_all
            split
            · simp_all
            · simp [freshInsertDLen, finishDLenScan_corresponds]
        | none =>
            simp_all
            simp [freshInsertDLen, finishDLenScan_corresponds]

/-- Removing absorbed successors subtracts exactly their old cardinalities,
leaving the untouched suffix contribution in the integer cache. -/
private lemma absorbSuccessorsDLen_preserves_cached_base
    (current : NR) (right : List NR) (cachedLength base : Int)
    (hlength : cachedLength = base + Int.ofNat (rangesCardinality right)) :
    let scanned := absorbSuccessorsDLen current right cachedLength
    scanned.cachedLength = base + Int.ofNat (rangesCardinality scanned.pending) := by
  induction right generalizing current cachedLength with
  | nil => simpa [absorbSuccessorsDLen] using hlength
  | cons next tail ih =>
      by_cases hmerge : NR.mergeable current next
      · simp only [absorbSuccessorsDLen, hmerge]
        apply ih
        rw [rangesCardinality_cons] at hlength
        have hcast : Int.ofNat (next.val.cardinality + rangesCardinality tail) =
            Int.ofNat next.val.cardinality + Int.ofNat (rangesCardinality tail) := by
          simp [Int.ofNat_eq_natCast, Nat.cast_add]
        rw [hcast] at hlength
        omega
      · simpa [absorbSuccessorsDLen, hmerge] using hlength

/-- The successor scan preserves the pending lower endpoint and only grows its
upper endpoint when all successor starts are at or to its right. -/
private lemma absorbSuccessorsDLen_preserves_endpoints
    (current : NR) (right : List NR) (cachedLength : Int)
    (hlower : ∀ nr ∈ right, current.val.lo ≤ nr.val.lo) :
    let scanned := absorbSuccessorsDLen current right cachedLength
    scanned.current.val.lo = current.val.lo ∧
      current.val.hi ≤ scanned.current.val.hi := by
  induction right generalizing current cachedLength with
  | nil => simp [absorbSuccessorsDLen]
  | cons next tail ih =>
      by_cases hmerge : NR.mergeable current next
      · simp only [absorbSuccessorsDLen, hmerge]
        have hnext := hlower next (by simp)
        have hglueLo : (NR.glue current next).val.lo = current.val.lo := by
          simp [NR.glue, IntRange.mergeRange, min_eq_left hnext]
        have hrec := ih (NR.glue current next)
          (cachedLength - Int.ofNat next.val.cardinality) (by
            intro nr hmem
            rw [hglueLo]
            exact hlower nr (by simp [hmem]))
        exact ⟨hrec.1.trans hglueLo, (le_max_left _ _).trans hrec.2⟩
      · simp [absorbSuccessorsDLen, hmerge]

/-- Fresh insertion removes absorbed successors and adds the final pending
range exactly once. -/
private theorem freshInsertDLen_preserves_cardinality
    (ranges : List NR) (gap : CursorGap) (input : NR) (cachedLength : Int)
    (hdecomp : ranges = gap.left ++ gap.right)
    (hlength : cachedLength = Int.ofNat (rangesCardinality ranges)) :
    (freshInsertDLen gap input cachedLength).cachedLength =
      Int.ofNat (rangesCardinality
        (freshInsertDLen gap input cachedLength).ranges) := by
  let scanned := absorbSuccessorsDLen input gap.right cachedLength
  have hcache : cachedLength = Int.ofNat (rangesCardinality gap.left) +
      Int.ofNat (rangesCardinality gap.right) := by
    rw [hlength, hdecomp, rangesCardinality_append]
    simp [Int.ofNat_eq_natCast, Nat.cast_add]
  have hscan := absorbSuccessorsDLen_preserves_cached_base input gap.right
    cachedLength (Int.ofNat (rangesCardinality gap.left)) hcache
  simp [freshInsertDLen, finishDLenScan, CursorGap.insertBefore,
    rangesCardinality_append]
  have hscan' : scanned.cachedLength =
      Int.ofNat (rangesCardinality gap.left) +
        Int.ofNat (rangesCardinality scanned.pending) := by
    simpa [scanned] using hscan
  dsimp only [scanned] at hscan'
  rw [hscan']
  simp only [Int.ofNat_eq_natCast]
  omega

/-- Extending a stored predecessor, removing absorbed successors, and adding
the final exposed right tail preserves the exact integer cardinality cache. -/
private theorem extendPredecessorDLen_preserves_cardinality
    (ranges : List NR) (gap : CursorGap) (predecessor input : NR)
    (cachedLength : Int)
    (hdecomp : ranges = gap.left ++ gap.right)
    (hlast : gap.left.getLast? = some predecessor)
    (hpredLo : predecessor.val.lo < input.val.lo)
    (hright : ∀ nr ∈ gap.right, input.val.lo ≤ nr.val.lo)
    (hextend : predecessor.val.hi < input.val.hi)
    (hlength : cachedLength = Int.ofNat (rangesCardinality ranges)) :
    (extendPredecessorDLen gap predecessor input cachedLength).cachedLength =
      Int.ofNat (rangesCardinality
        (extendPredecessorDLen gap predecessor input cachedLength).ranges) := by
  let init := gap.left.dropLast
  let extendedHi := max predecessor.val.hi input.val.hi
  let extended := mkDLenNR predecessor.val.lo extendedHi
    (predecessor.property.trans (le_max_left _ _))
  let added := IntRange.cardinality
    { lo := predecessor.val.hi, hi := input.val.hi - 1 }
  let afterExtension := cachedLength + Int.ofNat added
  let scanned := absorbSuccessorsDLen extended gap.right afterExtension
  have hne : gap.left ≠ [] := by
    intro hempty
    simp [hempty] at hlast
  have hlastEq : gap.left.getLast hne = predecessor :=
    List.getLast_of_getLast?_eq_some hlast
  have hleft : gap.left = init ++ [predecessor] := by
    simpa [init, hlastEq] using (List.dropLast_append_getLast hne).symm
  have hextendedHi : extended.val.hi = input.val.hi := by
    change max predecessor.val.hi input.val.hi = input.val.hi
    exact max_eq_right hextend.le
  have hcache : afterExtension =
      Int.ofNat (rangesCardinality init) + Int.ofNat extended.val.cardinality +
        Int.ofNat (rangesCardinality gap.right) := by
    have hcardExtended : extended.val.cardinality =
        predecessor.val.cardinality + added := by
      have hcard := NR.cardinality_eq_add_right_extension predecessor extended
        (by simp [extended, mkDLenNR])
        (by simp [extended, extendedHi, mkDLenNR, hextend])
      rw [hextendedHi] at hcard
      simpa [added, IntRange.rightExtensionCardinality] using hcard
    change cachedLength + Int.ofNat added = _
    rw [hlength, hdecomp, hleft, rangesCardinality_append,
      rangesCardinality_append, rangesCardinality_cons]
    simp only [rangesCardinality_nil, Nat.add_zero]
    rw [hcardExtended]
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    omega
  have hscan := absorbSuccessorsDLen_preserves_cached_base extended gap.right
    afterExtension
    (Int.ofNat (rangesCardinality init) + Int.ofNat extended.val.cardinality)
    (by omega)
  have hend := absorbSuccessorsDLen_preserves_endpoints extended gap.right
    afterExtension (by
      intro nr hmem
      exact (le_of_lt hpredLo).trans (hright nr hmem))
  by_cases hfinal : input.val.hi < scanned.current.val.hi
  · have hfinish :
        finishDLenScan extended gap.right afterExtension true input.val.hi =
          { scanned with cachedLength := (scanned.cachedLength +
              Int.ofNat (IntRange.cardinality
                { lo := input.val.hi, hi := scanned.current.val.hi - 1 })) } := by
      simp [finishDLenScan, scanned, hfinal]
    change (finishDLenScan extended gap.right afterExtension true input.val.hi).cachedLength =
      Int.ofNat (rangesCardinality
        (init ++ (finishDLenScan extended gap.right afterExtension true
          input.val.hi).current ::
          (finishDLenScan extended gap.right afterExtension true input.val.hi).pending))
    rw [hfinish]
    simp only [rangesCardinality_append, rangesCardinality_cons]
    have hcurrentCard : scanned.current.val.cardinality =
        extended.val.cardinality + IntRange.cardinality
          { lo := input.val.hi, hi := scanned.current.val.hi - 1 } := by
      simpa [IntRange.rightExtensionCardinality, hextendedHi] using
        (NR.cardinality_eq_add_right_extension extended scanned.current
          hend.1 (by simpa [hextendedHi] using hfinal))
    have hscan' : scanned.cachedLength =
        Int.ofNat (rangesCardinality init) + Int.ofNat extended.val.cardinality +
          Int.ofNat (rangesCardinality scanned.pending) := by
      simpa [scanned] using hscan
    dsimp [scanned] at hfinal hend hcurrentCard hscan' ⊢
    rw [hscan']
    rw [hcurrentCard]
    omega
  · have hfinish :
        finishDLenScan extended gap.right afterExtension true input.val.hi = scanned := by
      simp [finishDLenScan, scanned, hfinal]
    change (finishDLenScan extended gap.right afterExtension true input.val.hi).cachedLength =
      Int.ofNat (rangesCardinality
        (init ++ (finishDLenScan extended gap.right afterExtension true
          input.val.hi).current ::
          (finishDLenScan extended gap.right afterExtension true input.val.hi).pending))
    rw [hfinish]
    simp only [rangesCardinality_append, rangesCardinality_cons]
    have hscan' : scanned.cachedLength =
        Int.ofNat (rangesCardinality init) + Int.ofNat extended.val.cardinality +
          Int.ofNat (rangesCardinality scanned.pending) := by
      simpa [scanned] using hscan
    dsimp [scanned] at hfinal hend hscan' ⊢
    rw [hscan']
    have hendInput : input.val.hi ≤ (absorbSuccessorsDLen extended gap.right
        afterExtension).current.val.hi := by
      simpa [hextendedHi] using hend.2
    have hhiEq : (absorbSuccessorsDLen extended gap.right
        afterExtension).current.val.hi = extended.val.hi := by
      exact (le_antisymm (not_lt.mp hfinal) hendInput).trans hextendedHi.symm
    have hcurrentEq : (absorbSuccessorsDLen extended gap.right
        afterExtension).current.val.cardinality = extended.val.cardinality := by
      simp [IntRange.cardinality, hend.1, hhiEq]
    rw [hcurrentEq]
    omega

/-- Branch-local cached arithmetic computes the cardinality of DLen's output
from the canonical-list and lower-bound obligations exposed by Algo D. -/
private theorem internalAddDLenRaw_preserves_cardinality
    (s : RangeSetBlaze) (cachedLength : Int) (r : IntRange)
    (hlength : cachedLength = Int.ofNat s.cardinality) :
    (internalAddDLenRaw s.ranges cachedLength r).cachedLength =
      Int.ofNat (rangesCardinality
        (internalAddDLenRaw s.ranges cachedLength r).ranges) := by
  classical
  unfold internalAddDLenRaw
  by_cases hempty : r.hi < r.lo
  · simp [hempty, hlength, RangeSetBlaze.cardinality]
  · simp only [dif_neg hempty]
    let input : NR := ⟨r, not_lt.mp hempty⟩
    let gap := lowerBoundGap r.lo s.ranges
    have hgap := lowerBoundGap_spec s.ranges r.lo s.canonical
    have hdecomp : s.ranges = gap.left ++ gap.right := by
      simpa [gap] using hgap.1
    have hleft : ∀ nr ∈ gap.left, nr.val.lo < r.lo := by
      simpa [gap] using hgap.2.1
    have hright : ∀ nr ∈ gap.right, r.lo ≤ nr.val.lo := by
      simpa [gap] using hgap.2.2
    change (match gap.peekPrev with
      | some predecessor =>
          if NR.mergeable predecessor input then
            if r.hi ≤ predecessor.val.hi then
              (⟨s.ranges, cachedLength⟩ : DLenRawResult)
            else extendPredecessorDLen gap predecessor input cachedLength
          else
            match gap.peekNext with
            | some successor =>
                if successor.val.lo = r.lo ∧ r.hi ≤ successor.val.hi then
                  (⟨s.ranges, cachedLength⟩ : DLenRawResult)
                else freshInsertDLen gap input cachedLength
            | none => freshInsertDLen gap input cachedLength
      | none =>
          match gap.peekNext with
          | some successor =>
              if successor.val.lo = r.lo ∧ r.hi ≤ successor.val.hi then
                (⟨s.ranges, cachedLength⟩ : DLenRawResult)
              else freshInsertDLen gap input cachedLength
          | none => freshInsertDLen gap input cachedLength).cachedLength = _
    cases hprev : gap.peekPrev with
    | some predecessor =>
        by_cases hmerge : NR.mergeable predecessor input
        · simp only [hmerge, if_true]
          by_cases hcovered : r.hi ≤ predecessor.val.hi
          · simp [hmerge, hcovered, input, hlength,
              RangeSetBlaze.cardinality]
          · simp only [hcovered, if_false]
            have h := extendPredecessorDLen_preserves_cardinality s.ranges gap
              predecessor input cachedLength hdecomp
              (by simpa [CursorGap.peekPrev] using hprev)
              (hleft predecessor (List.mem_of_mem_getLast? (by
                simpa [CursorGap.peekPrev] using hprev)))
              (by simpa [input] using hright)
              (by simpa [input] using not_le.mp hcovered)
              (by simpa [RangeSetBlaze.cardinality] using hlength)
            simpa [hprev, hmerge, hcovered, input, gap, hempty] using h
        · simp only [hmerge, if_false]
          cases hnext : gap.peekNext with
          | some successor =>
              by_cases hcoveredNext : successor.val.lo = r.lo ∧
                  r.hi ≤ successor.val.hi
              · simp [hmerge, hcoveredNext, input, hlength,
                  RangeSetBlaze.cardinality]
              · have h := freshInsertDLen_preserves_cardinality s.ranges gap input
                    cachedLength hdecomp
                    (by simpa [RangeSetBlaze.cardinality] using hlength)
                simpa [hprev, hmerge, hnext, hcoveredNext, input, gap, hempty] using h
          | none =>
              have h := freshInsertDLen_preserves_cardinality s.ranges gap input
                cachedLength hdecomp
                (by simpa [RangeSetBlaze.cardinality] using hlength)
              simpa [hprev, hmerge, hnext, input, gap, hempty] using h
    | none =>
        cases hnext : gap.peekNext with
        | some successor =>
            by_cases hcoveredNext : successor.val.lo = r.lo ∧
                r.hi ≤ successor.val.hi
            · simp [hcoveredNext, hlength,
                RangeSetBlaze.cardinality]
            · have h := freshInsertDLen_preserves_cardinality s.ranges gap input
                  cachedLength hdecomp
                  (by simpa [RangeSetBlaze.cardinality] using hlength)
              simpa [hprev, hnext, hcoveredNext, input, gap, hempty] using h
        | none =>
            have h := freshInsertDLen_preserves_cardinality s.ranges gap input
              cachedLength hdecomp
              (by simpa [RangeSetBlaze.cardinality] using hlength)
            simpa [hprev, hnext, input, gap, hempty] using h

/-- Algo D insertion with an explicit incoming cached element count. -/
def internalAddDLen
    (s : RangeSetBlaze) (cachedLength : Int) (r : IntRange) : DLenResult :=
  let raw := internalAddDLenRaw s.ranges cachedLength r
  let setResult : RangeSetBlaze :=
    ⟨raw.ranges, by
      rw [internalAddDLenRaw_corresponds s cachedLength r]
      exact (internalAddD s r).canonical⟩
  ⟨setResult, raw.cachedLength⟩

/-- DLen's set component is exactly Algo D's result representation. -/
theorem internalAddDLen_setResult
    (s : RangeSetBlaze) (cachedLength : Int) (r : IntRange) :
    (internalAddDLen s cachedLength r).setResult = internalAddD s r := by
  unfold internalAddDLen
  dsimp only
  rw [RangeSetBlaze.mk.injEq]
  exact internalAddDLenRaw_corresponds s cachedLength r

/-- A valid incoming cached count remains valid after Algo D insertion. -/
theorem internalAddDLen_cachedLength
    (s : RangeSetBlaze) (cachedLength : Int) (r : IntRange)
    (hlength : cachedLength = Int.ofNat s.cardinality) :
    (internalAddDLen s cachedLength r).cachedLength =
      Int.ofNat (internalAddDLen s cachedLength r).setResult.cardinality := by
  exact internalAddDLenRaw_preserves_cardinality s cachedLength r hlength

/-- DLen inherits Algo D's already-proved set semantics. -/
theorem internalAddDLen_toSet
    (s : RangeSetBlaze) (cachedLength : Int) (r : IntRange) :
    (internalAddDLen s cachedLength r).setResult.toSet = s.toSet ∪ r.toSet := by
  rw [internalAddDLen_setResult]
  exact internalAddD_toSet s r

end RangeSetBlaze
