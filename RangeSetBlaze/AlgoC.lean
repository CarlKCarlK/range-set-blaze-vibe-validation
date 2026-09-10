import Mathlib.Data.List.TakeWhile
import RangeSetBlaze.Basic
import RangeSetBlaze.AlgoB

namespace RangeSetBlaze

open IntRange
open IntRange.NR
open scoped IntRange.NR

/-!
Algo C mirrors the production insertion algorithm over `NR` and `RangeSetBlaze`.
It splits ranges on the lower endpoint and handles gap, covered, and
extend-and-merge branches. Proof helpers establish `Pairwise NR.before` and
exact set-union correctness. The executable branch structure is protected
during proof refactoring.
-/

private def mkNR (lo hi : Int) (h : lo ≤ hi) : NR :=
  ⟨{ lo := lo, hi := hi }, h⟩

/-- Safe constructor when you already have the invariant. -/
private def fromNRs (xs : List NR)
  (hok : List.Pairwise NR.before xs) : RangeSetBlaze :=
  { ranges := xs, ok := hok }

-- NEW: top-level version of the previous nested `loop`
private def deleteExtraNRs_loop (current : NR) (pending : List NR) : Prod NR (List NR) :=
  match pending with
  | [] => (current, [])
  | next :: pendingTail =>
      if decide (next.val.lo ≤ current.val.hi + 1) then
        let newLo := current.val.lo
        let newHi := max current.val.hi next.val.hi
        have hcurr' : current.val.lo ≤ current.val.hi := current.property
        have hmax'  : current.val.hi ≤ newHi := le_max_left _ _
        have hmerged : newLo ≤ newHi := le_trans hcurr' hmax'
        let merged := mkNR newLo newHi hmerged
        deleteExtraNRs_loop merged pendingTail
      else
        (current, next :: pendingTail)

@[simp] private lemma deleteExtraNRs_loop_nil (current : NR) :
    deleteExtraNRs_loop current [] = (current, []) := rfl

@[simp] private lemma deleteExtraNRs_loop_cons_merge
    (current next : NR) (tail : List NR)
    (h : next.val.lo ≤ current.val.hi + 1) :
  deleteExtraNRs_loop current (next :: tail)
    =
  deleteExtraNRs_loop
    (mkNR current.val.lo (max current.val.hi next.val.hi)
      (by
        have hc : current.val.lo ≤ current.val.hi := current.property
        exact le_trans hc (le_max_left _ _)))
    tail := by
  simp [deleteExtraNRs_loop, h]

@[simp] private lemma deleteExtraNRs_loop_cons_noMerge
    (current next : NR) (tail : List NR)
    (h : ¬ next.val.lo ≤ current.val.hi + 1) :
  deleteExtraNRs_loop current (next :: tail) = (current, next :: tail) := by
  simp [deleteExtraNRs_loop, h]

/-- If two ordered ranges touch or overlap, their union equals the single
closed interval that stretches to the larger upper end. -/
private lemma union_touch_eq_Icc_max
    (lo₁ hi₁ lo₂ hi₂ : Int)
    (h₁ : lo₁ ≤ hi₁) (h₂ : lo₂ ≤ hi₂)
    (h_order : lo₁ ≤ lo₂)
    (h_touch : ¬ (hi₁ + 1 < lo₂)) :
    Set.Icc lo₁ hi₁ ∪ Set.Icc lo₂ hi₂ =
      Set.Icc lo₁ (max hi₁ hi₂) := by
  classical
  apply Set.ext
  intro x
  constructor
  · intro hx
    have _ := h₁
    have _ := h₂
    rcases hx with hx₁ | hx₂
    · rcases hx₁ with ⟨hx_lo, hx_hi⟩
      exact ⟨hx_lo, le_trans hx_hi (le_max_left _ _)⟩
    · rcases hx₂ with ⟨hx_lo, hx_hi⟩
      have hx_lo' : lo₁ ≤ x := le_trans h_order hx_lo
      have hx_hi' : x ≤ max hi₁ hi₂ := le_trans hx_hi (le_max_right _ _)
      exact ⟨hx_lo', hx_hi'⟩
  · intro hx
    rcases hx with ⟨hx_lo, hx_hi⟩
    by_cases hx_le : x ≤ hi₁
    · left
      exact ⟨hx_lo, hx_le⟩
    · have hx_gt : hi₁ < x := lt_of_not_ge hx_le
      have hx_add : hi₁ + 1 ≤ x := (Int.add_one_le_iff).2 hx_gt
      have h_lo₂ : lo₂ ≤ x := le_trans (le_of_not_gt h_touch) hx_add
      have hx_le_hi₂ : x ≤ hi₂ := by
        have h_or := (le_max_iff).1 hx_hi
        exact h_or.resolve_left hx_le
      right
      exact ⟨h_lo₂, hx_le_hi₂⟩

/-- Set-level description of a single merge step inside `deleteExtraNRs`. -/
private lemma merge_step_sets
    (current next : NR)
    (horder : current.val.lo ≤ next.val.lo)
    (htouch : ¬ (current.val.hi + 1 < next.val.lo)) :
    current.val.toSet ∪ next.val.toSet =
      (mkNR current.val.lo (max current.val.hi next.val.hi)
        (by
          have hc : current.val.lo ≤ current.val.hi := current.property
          have : current.val.hi ≤ max current.val.hi next.val.hi :=
            le_max_left _ _
          exact le_trans hc this)).val.toSet := by
  classical
  have h₁ : current.val.lo ≤ current.val.hi := current.property
  have h₂ : next.val.lo ≤ next.val.hi := next.property
  have h_union :=
    union_touch_eq_Icc_max current.val.lo current.val.hi
      next.val.lo next.val.hi h₁ h₂ horder htouch
  simpa [IntRange.toSet, mkNR] using h_union

private def deleteExtraNRs (xs : List NR) (start stop : Int) :
    List NR :=
  let split := List.span (fun nr => decide (nr.val.lo < start)) xs
  let before := split.fst
  let rest := split.snd
  match rest with
  | [] => xs
  | curr :: tail =>
      let initialHi := max curr.val.hi stop
      have hcurr : curr.val.lo ≤ curr.val.hi := curr.property
      have hmax : curr.val.hi ≤ initialHi := le_max_left _ _
      have hinit : curr.val.lo ≤ initialHi := le_trans hcurr hmax
      let initial := mkNR curr.val.lo initialHi hinit
      let result := deleteExtraNRs_loop initial tail
      before ++ (result.fst :: result.snd)

private def internalAdd2NRs (xs : List NR) (start stop : Int)
    (h : start ≤ stop) :
    List NR :=
  let split := List.span (fun nr => decide (nr.val.lo < start)) xs
  let before := split.fst
  let after := split.snd
  let inserted := mkNR start stop h
  deleteExtraNRs (before ++ (inserted :: after)) start stop

-- delete_extra deleted - use internalAdd2_safe instead
-- internalAdd2 deleted - use internalAdd2_safe or internalAdd2_safe_from_le instead

open Classical
open IntRange


-- Local helper: list-based set view (same as listToSet from Basic.lean but scoped to this file)
section LocalDefs

private def algoCListSet (rs : List NR) : Set Int :=
  rs.foldr (fun r acc => r.val.toSet ∪ acc) (∅ : Set Int)

@[simp] private lemma algoCListSet_nil :
    algoCListSet ([] : List NR) = (∅ : Set Int) := rfl

@[simp] private lemma algoCListSet_cons (r : NR) (rs : List NR) :
    algoCListSet (r :: rs) = r.val.toSet ∪ algoCListSet rs := rfl

@[simp] private lemma algoCListSet_append (xs ys : List NR) :
    algoCListSet (xs ++ ys) = algoCListSet xs ∪ algoCListSet ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [ih, Set.union_left_comm, Set.union_comm]

end LocalDefs

@[reducible] private def loLE (a b : NR) : Prop :=
  a.val.lo ≤ b.val.lo

/-- Pairwise gap-separated ranges form a chain in nondecreasing lower-endpoint order. -/
private lemma pairwise_before_implies_chain_loLE (xs : List NR)
    (h : List.Pairwise NR.before xs) :
    List.IsChain loLE xs := by
  exact (h.imp fun hab => by
    unfold loLE
    exact (NR.before_lo_lt hab).le).isChain

private lemma nr_mem_ranges_subset_algoCListSet : ∀ (ranges : List NR) (nr : NR),
    nr ∈ ranges → nr.val.toSet ⊆ algoCListSet ranges
  | [], _, h => by cases h
  | x :: xs, nr, h => by
      simp [List.mem_cons] at h
      rw [algoCListSet_cons]
      cases h with
      | inl heq =>
          subst heq
          exact Set.subset_union_left
      | inr htail =>
          exact Set.subset_union_of_subset_right (nr_mem_ranges_subset_algoCListSet xs nr htail) _

/-- For ranges ordered by lower endpoint, every range in the suffix obtained by spanning while `lo < start` starts at or after `start`. -/
private lemma span_suffix_all_ge_start_of_chain
    (xs : List NR) (start : Int)
    (hchain : List.IsChain loLE xs) :
    let p : NR → Bool := fun nr => decide (nr.val.lo < start)
    let split := List.span p xs
    ∀ nr ∈ split.snd, start ≤ nr.val.lo := by
  classical
  intro p split
  have h_span : split = (xs.takeWhile p, xs.dropWhile p) :=
    List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
  have h_take : split.fst = xs.takeWhile p := by
    exact congrArg Prod.fst h_span
  have h_drop : split.snd = xs.dropWhile p := by
    exact congrArg Prod.snd h_span
  have h_decomp : split.fst ++ split.snd = xs := by
    have := List.takeWhile_append_dropWhile (p := p) (l := xs)
    rw [h_take, h_drop]
    exact this
  intro nr hmem
  have hchain_append :
      List.IsChain loLE (split.fst ++ split.snd) := by
    rw [h_decomp]
    exact hchain
  have hchain_suffix :
      List.IsChain loLE split.snd :=
    List.IsChain.right_of_append (l₁ := split.fst)
      (l₂ := split.snd) hchain_append
  cases hA : split.snd with
  | nil =>
      rw [hA] at hmem
      cases hmem
  | cons y ys =>
      have hmem_cons : nr = y ∨ nr ∈ ys := by
        rw [hA] at hmem
        simp at hmem
        exact hmem
      have hy_head? :
          (xs.dropWhile p).head? = some y := by
        have : split.snd.head? = some y := by
          rw [hA]
          rfl
        rw [← h_drop]
        exact this
      have hy_false : p y = false := by
        have := List.head?_dropWhile_not (p := p) (l := xs)
        rw [hy_head?] at this
        simp at this
        exact this
      have hy_not_lt : ¬ y.val.lo < start := by
        intro hy_lt
        have hcontra : p y = true := by
          unfold p
          simp [hy_lt]
        rw [hcontra] at hy_false
        contradiction
      have h_start_le_y : start ≤ y.val.lo :=
        not_lt.mp hy_not_lt
      have hchain_after : List.IsChain loLE (y :: ys) := by
        rw [hA] at hchain_suffix
        exact hchain_suffix
      cases hmem_cons with
      | inl hnr =>
          subst hnr
          exact h_start_le_y
      | inr htail =>
          have h_y_le_nr :
              y.val.lo ≤ nr.val.lo :=
            hchain_after.rel_cons htail
          exact le_trans h_start_le_y h_y_le_nr

/-- Splice lemma assuming the input list is chain-sorted by `lo`. -/
lemma deleteExtraNRs_loop_sets
    (start : Int) :
    ∀ (pending : List NR) (current : NR),
      current.val.lo = start →
      (∀ nr ∈ pending, start ≤ nr.val.lo) →
      algoCListSet
          (let res := deleteExtraNRs_loop current pending;
            res.fst :: res.snd)
        =
          current.val.toSet ∪ algoCListSet pending := by
  intro pending current hcurlo hpend
  induction pending generalizing current with
  | nil =>
      simp [algoCListSet_nil, Set.union_comm]
  | cons next tail ih =>
      dsimp [deleteExtraNRs_loop]
      by_cases hmerge : next.val.lo ≤ current.val.hi + 1
      · -- merge branch
        have horder : current.val.lo ≤ next.val.lo := by
          have : start ≤ next.val.lo := hpend next (by simp)
          simpa [hcurlo] using this
        have htouch : ¬ (current.val.hi + 1 < next.val.lo) :=
          not_lt.mpr hmerge
        have hpend' : ∀ nr ∈ tail, start ≤ nr.val.lo := by
          intro nr hmem
          exact hpend nr (by simp [hmem])
        set merged :=
          mkNR current.val.lo (max current.val.hi next.val.hi)
            (by
              have hc : current.val.lo ≤ current.val.hi := current.property
              exact le_trans hc (le_max_left _ _)) with hmerged_def
        have hcurlo' : merged.val.lo = start := by
          simp [hmerged_def, mkNR, hcurlo]
        have hrec :=
          ih merged hcurlo' hpend'
        have hmerged_toSet :
            merged.val.toSet = current.val.toSet ∪ next.val.toSet := by
          simpa [hmerged_def] using
            (merge_step_sets current next horder htouch).symm
        have hstep :
            deleteExtraNRs_loop current (next :: tail)
              =
            deleteExtraNRs_loop merged tail := by
          simpa [hmerged_def] using
            (deleteExtraNRs_loop_cons_merge current next tail hmerge)
        have hloop_simplified :
            algoCListSet
                ((deleteExtraNRs_loop current (next :: tail)).fst ::
                  (deleteExtraNRs_loop current (next :: tail)).snd)
              =
                merged.val.toSet ∪ algoCListSet tail := by
          simpa [hstep] using hrec
        calc
          algoCListSet
              (let res := deleteExtraNRs_loop current (next :: tail);
                res.fst :: res.snd)
              =
                merged.val.toSet ∪ algoCListSet tail := hloop_simplified
          _ = (current.val.toSet ∪ next.val.toSet) ∪ algoCListSet tail := by
                simp [hmerged_toSet]
          _ = current.val.toSet ∪ algoCListSet (next :: tail) := by
                simp [algoCListSet_cons]; ac_rfl
      · -- no-merge branch
        have hmerge' : ¬ next.val.lo ≤ current.val.hi + 1 := hmerge
        have hloop_eq :
            deleteExtraNRs_loop current (next :: tail)
              = (current, next :: tail) := by
          simpa using deleteExtraNRs_loop_cons_noMerge current next tail hmerge'
        simp [hmerge, Set.union_left_comm]

/-- Helper: deleteExtraNRs_loop preserves the property that result.fst.lo = start
and all elements in result.snd have lo ≥ start. -/
private lemma deleteExtraNRs_loop_lo_ge
    (start : Int)
    (current : NR) (pending : List NR)
    (hlo : current.val.lo = start)
    (hge : ∀ nr ∈ pending, start ≤ nr.val.lo) :
    let res := deleteExtraNRs_loop current pending
    res.fst.val.lo = start ∧ ∀ nr ∈ res.snd, start ≤ nr.val.lo := by
  induction pending generalizing current with
  | nil =>
      simp
      exact hlo
  | cons next tail ih =>
      by_cases hmerge : next.val.lo ≤ current.val.hi + 1
      · -- Merge case
        set merged := mkNR current.val.lo (max current.val.hi next.val.hi)
          (by have := current.property; exact le_trans this (le_max_left _ _))
        have h_loop_eq : deleteExtraNRs_loop current (next :: tail) =
                          deleteExtraNRs_loop merged tail := by
          simpa using deleteExtraNRs_loop_cons_merge current next tail hmerge
        rw [h_loop_eq]
        apply ih merged
        · simp [merged, mkNR, hlo]
        · intro nr hmem
          exact hge nr (by simp [hmem])
      · -- No merge case
        have h_loop_eq : deleteExtraNRs_loop current (next :: tail) =
                          (current, next :: tail) := by
          simpa using deleteExtraNRs_loop_cons_noMerge current next tail hmerge
        rw [h_loop_eq]
        simp
        constructor
        · exact hlo
        · constructor
          · exact hge next (by simp)
          · intro a ha hmem
            exact hge ⟨a, nonempty_iff_not_empty a |>.mpr ha⟩ (by simp [hmem])

/-- Weak variant: we only assume `Pairwise pending` and `start ≤ lo` on `pending`.
It shows the loop output is `Pairwise`, even if `current` may overlap `pending.head`. -/
private lemma ok_deleteExtraNRs_loop_weak
    (start : Int)
    (current : NR) (pending : List NR)
    (hlo  : current.val.lo = start)
    (hge  : ∀ nr ∈ pending, start ≤ nr.val.lo)
    (hpwP : List.Pairwise NR.before pending) :
    List.Pairwise NR.before
      (let res := deleteExtraNRs_loop current pending; res.fst :: res.snd) := by
  induction pending generalizing current with
  | nil =>
      simp [deleteExtraNRs_loop]
  | cons next tail ih =>
      by_cases hmerge : next.val.lo ≤ current.val.hi + 1
      · -- MERGE: recurse on (merged, tail)
        set merged :=
          mkNR current.val.lo (max current.val.hi next.val.hi)
            (by have := current.property; exact le_trans this (le_max_left _ _))
        have hge' : ∀ nr ∈ tail, start ≤ nr.val.lo := by
          intro nr h; exact hge nr (by simp [h])
        have hpw_tail : List.Pairwise NR.before tail := by
          cases hpwP with
          | cons _ htail => exact htail
        have hmerged_lo : merged.val.lo = start := by
          simp [merged, mkNR, hlo]
        have h_loop_eq : deleteExtraNRs_loop current (next :: tail) = deleteExtraNRs_loop merged tail := by
          exact deleteExtraNRs_loop_cons_merge current next tail hmerge
        simp only [h_loop_eq]
        exact ih merged hmerged_lo hge' hpw_tail
      · -- NO MERGE: loop returns (current, next :: tail)
        have h_loop_eq : deleteExtraNRs_loop current (next :: tail) = (current, next :: tail) := by
          exact deleteExtraNRs_loop_cons_noMerge current next tail hmerge
        simp only [h_loop_eq]
        -- we need: current ≺ next and for all z∈tail, current ≺ z
        have h_head : NR.before current next := by
          unfold NR.before; simpa using (not_le.mp hmerge)
        -- For z ∈ tail, use chain order from `Pairwise pending`
        have hchain : List.IsChain loLE (next :: tail) :=
          pairwise_before_implies_chain_loLE (next :: tail) (by
            cases hpwP with
            | cons hx htail => exact List.Pairwise.cons hx htail)
        have hnext_le : ∀ z ∈ tail, next.val.lo ≤ z.val.lo :=
          fun z hz => hchain.rel_cons hz
        have h_current_tail : ∀ z ∈ tail, NR.before current z := by
          intro z hz
          have : current.val.hi + 1 < next.val.lo := by simpa [NR.before] using h_head
          have : current.val.hi + 1 < z.val.lo := lt_of_lt_of_le this (hnext_le z hz)
          simpa [NR.before] using this
        have hpw_tail : List.Pairwise NR.before tail := by
          cases hpwP with
          | cons _ htail => exact htail
        -- Construct Pairwise (current :: next :: tail)
        constructor
        · intro b hb
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact h_head
          · exact h_current_tail b hb
        · constructor
          · intro b hb
            cases hpwP with
            | cons hx _ => exact hx b hb
          · exact hpw_tail

/-- If `before` is nonempty and its last element is strictly before `start`,
then every element of `before` is strictly before `start`. -/
private lemma all_before_strict_before_start
    (before : List NR) (start : Int)
    (hpair : List.Pairwise NR.before before)
    (hne : before ≠ [])
    (hlast : (before.getLast hne).val.hi + 1 < start) :
    ∀ x ∈ before, x.val.hi + 1 < start := by
  -- every x ∈ (dropLast before) satisfies x ≺ last(before)
  have h_all : ∀ x ∈ List.dropLast before, NR.before x (before.getLast hne) := by
    intro x hx
    simpa using hpair.rel_dropLast_getLast hx
  -- now any x ∈ before is either the last or in dropLast
  intro x hx
  by_cases hdrop : x ∈ List.dropLast before
  · have hx_before_last := h_all x hdrop
    -- x ≺ last ⇒ x.hi + 1 < last.lo, and last.lo ≤ last.hi + 1 < start
    unfold NR.before at hx_before_last
    have last_lo_lt_start : (before.getLast hne).val.lo < start := by
      have : (before.getLast hne).val.lo ≤ (before.getLast hne).val.hi := (before.getLast hne).property
      calc (before.getLast hne).val.lo
        _ ≤ (before.getLast hne).val.hi := this
        _ < (before.getLast hne).val.hi + 1 := by omega
        _ < start := hlast
    exact lt_trans hx_before_last last_lo_lt_start
  · -- x is not in dropLast, so x must be the last
    have heq : x = before.getLast hne := by
      have : before = List.dropLast before ++ [before.getLast hne] := (List.dropLast_append_getLast hne).symm
      rw [this] at hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · contradiction
      · exact hx
    subst heq
    exact hlast

/-- Lemma for internalAdd2NRs: inserting [start,stop] into a Pairwise list maintains Pairwise.
This version requires a gap hypothesis: either before is empty, or the last element of before
is strictly before start. This matches the actual call sites in internalAddC. -/
private lemma ok_internalAdd2NRs (xs : List NR) (start stop : Int) (h_le : start ≤ stop)
    (hpw : List.Pairwise NR.before xs)
    (hgap : let split := List.span (fun nr => decide (nr.val.lo < start)) xs
            let before := split.fst
            before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < start) :
    let split := List.span (fun nr => decide (nr.val.lo < start)) xs
    let before := split.fst
    let after := split.snd
    let inserted := mkNR start stop h_le
    let ys := before ++ inserted :: after
    List.Pairwise NR.before (deleteExtraNRs ys start stop) := by
  intro split before after inserted ys

  -- Set up the predicate
  set p : NR → Bool := (fun nr => decide (nr.val.lo < start)) with hp

  -- Properties of before: all elements satisfy p (i.e., nr.lo < start)
  have h_before_all : ∀ nr ∈ before, p nr = true := by
    intro nr hmem
    -- before = xs.takeWhile p
    have h_split_eq := List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
    have : before = xs.takeWhile p := by
      have : split = (xs.takeWhile p, xs.dropWhile p) := h_split_eq
      simp [split, before] at this ⊢
      exact this.1
    rw [this] at hmem
    exact List.mem_takeWhile_imp hmem

  -- inserted doesn't satisfy p (inserted.lo = start, so not < start)
  have h_inserted_false : p inserted = false := by
    simp only [p, decide_eq_false_iff_not, not_lt]
    show start ≤ inserted.val.lo
    simp [inserted, mkNR]

  -- Span of ys gives back (before, inserted :: after)
  have h_span_ys : List.span p ys = (before, inserted :: after) := by
    have htake : ys.takeWhile p = before := by
      rw [List.takeWhile_append_of_pos h_before_all]
      simp [h_inserted_false]
    have hdrop : ys.dropWhile p = inserted :: after := by
      rw [List.dropWhile_append_of_pos h_before_all]
      simp [h_inserted_false]
    simp [List.span_eq_takeWhile_dropWhile, htake, hdrop]

  -- Now analyze deleteExtraNRs on ys
  unfold deleteExtraNRs

  -- The span in deleteExtraNRs uses the exact same predicate
  have h_span_match :
    List.span (fun nr => decide (nr.val.lo < start)) ys = (before, inserted :: after) := by
    convert h_span_ys using 1

  -- Simplify using the span result
  simp only [h_span_match]

  -- Now we have: before ++ (deleteExtraNRs_loop initial after).fst :: (deleteExtraNRs_loop initial after).snd
  -- where initial = mkNR inserted.lo (max inserted.hi stop) = mkNR start (max stop stop) = mkNR start stop

  -- Set up for applying ok_deleteExtraNRs_loop
  set curr := inserted
  set initialHi := max curr.val.hi stop
  have hcurr : curr.val.lo ≤ curr.val.hi := curr.property
  have hmax_prop : curr.val.hi ≤ initialHi := le_max_left _ _
  set initial := mkNR curr.val.lo initialHi (le_trans hcurr hmax_prop)
  set result := deleteExtraNRs_loop initial after

  -- Need to prove: before ++ (result.fst :: result.snd) is Pairwise

  -- Step 1: Get Pairwise on before (from xs)
  have hpw_before : List.Pairwise NR.before before := by
    exact List.Pairwise.sublist
      (by simpa [split, before] using
        (List.takeWhile_sublist p : (xs.takeWhile p).Sublist xs)) hpw

  -- Step 2: Extract Pairwise on after
  have hpw_after : List.Pairwise NR.before after := by
    exact List.Pairwise.sublist
      (by simpa [split, after] using
        (List.dropWhile_sublist p : (xs.dropWhile p).Sublist xs)) hpw

  have hchain : List.IsChain loLE xs := pairwise_before_implies_chain_loLE xs hpw
  have h_after_ge : ∀ nr ∈ after, start ≤ nr.val.lo := by
    simpa [p, split, after] using
      (span_suffix_all_ge_start_of_chain xs start hchain)

  have h_initial_lo : initial.val.lo = start := by
    simp [initial, curr, inserted, mkNR]
  have h_loop_props := deleteExtraNRs_loop_lo_ge start initial after h_initial_lo h_after_ge

  -- Step 3: Apply ok_deleteExtraNRs_loop_weak to get Pairwise on (result.fst :: result.snd)
  -- The weak version only requires Pairwise on `after`, not on (initial :: after)
  have hpw_result : List.Pairwise NR.before (result.fst :: result.snd) := by
    -- Apply the weak loop lemma - doesn't require Pairwise (initial :: after)
    exact ok_deleteExtraNRs_loop_weak start initial after h_initial_lo h_after_ge hpw_after

  -- Step 4: Prove cross product: all elements of before are ≺ all elements of result
  have hcross : ∀ x ∈ before, ∀ y ∈ (result.fst :: result.snd), NR.before x y := by
    intro x hx y hy
    unfold NR.before
    -- y ∈ (result.fst :: result.snd) means y.lo ≥ start (from loop preservation)
    have hy_ge : start ≤ y.val.lo := by
      simp [result] at hy
      rcases hy with rfl | hy_tail
      · rw [h_loop_props.1]
      · exact h_loop_props.2 y hy_tail

    -- Need: x.hi + 1 < y.lo
    -- Strategy: use the gap hypothesis to show all x ∈ before have x.hi + 1 < start,
    -- and all y in result have y.lo ≥ start (from deleteExtraNRs_loop_lo_ge)
    have hgap_before : before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < start := hgap
    rcases hgap_before with hempty | ⟨hne, hlast_gap⟩
    · -- before is empty, so x ∈ before is vacuous
      rw [hempty] at hx
      cases hx
    · -- Nonempty before with gap: last(before).hi + 1 < start
      -- From the last-gap, push gap to all elements of before
      have hall_before : ∀ x ∈ before, x.val.hi + 1 < start :=
        all_before_strict_before_start before start hpw_before hne hlast_gap

      -- Get: x.hi + 1 < start
      have hx_lt : x.val.hi + 1 < start := hall_before x hx

      -- Conclude: x.hi + 1 < start ≤ y.lo, so x.hi + 1 < y.lo
      exact lt_of_lt_of_le hx_lt hy_ge  -- Step 5: Apply pairwise_append
  exact List.pairwise_append.mpr ⟨hpw_before, hpw_result, hcross⟩

/-- If the (≤ start) split is empty, then the (< start) split is also empty.
This is because `< start` is strictly stronger than `≤ start`. -/
private lemma span_le_empty_implies_lt_empty (xs : List NR) (start : Int)
    (h_le_empty : (List.span (fun nr => decide (nr.val.lo ≤ start)) xs).fst = []) :
    (List.span (fun nr => decide (nr.val.lo < start)) xs).fst = [] := by
  -- Convert both spans to takeWhile
  have h_le_eq := List.span_eq_takeWhile_dropWhile (p := fun nr => decide (nr.val.lo ≤ start)) (l := xs)
  have h_lt_eq := List.span_eq_takeWhile_dropWhile (p := fun nr => decide (nr.val.lo < start)) (l := xs)

  have h_le_take : xs.takeWhile (fun nr => decide (nr.val.lo ≤ start)) = [] := by
    have : (List.span (fun nr => decide (nr.val.lo ≤ start)) xs).fst =
           xs.takeWhile (fun nr => decide (nr.val.lo ≤ start)) := by
      rw [h_le_eq]
    rw [h_le_empty] at this
    exact this.symm

  -- Show takeWhile (< start) is also empty
  have h_lt_take : xs.takeWhile (fun nr => decide (nr.val.lo < start)) = [] := by
    cases hxs : xs with
    | nil => simp [List.takeWhile]
    | cons hd tl =>
      -- If takeWhile (≤ start) is empty, then hd doesn't satisfy (≤ start)
      have h_hd_not_le : ¬(hd.val.lo ≤ start) := by
        rw [hxs] at h_le_take
        simp [List.takeWhile] at h_le_take
        by_contra h_le
        simp [h_le] at h_le_take
      -- Therefore hd doesn't satisfy (< start) either
      have h_hd_not_lt : ¬(hd.val.lo < start) := fun h => h_hd_not_le (le_of_lt h)
      -- So takeWhile (< start) stops immediately
      simp [List.takeWhile, h_hd_not_lt]

  -- Convert back to span
  have : (List.span (fun nr => decide (nr.val.lo < start)) xs).fst =
         xs.takeWhile (fun nr => decide (nr.val.lo < start)) := by
    rw [h_lt_eq]
  rw [this, h_lt_take]

-- Helper lemma: getLast? = some implies getLast returns the same value
theorem getLast?_eq_some_getLast {α : Type*} {xs : List α} {x : α} (h : xs.getLast? = some x) :
    ∃ hne : xs ≠ [], xs.getLast hne = x := by
  have hne : xs ≠ [] := by
    intro hnil
    simp [hnil] at h
  exact ⟨hne, List.getLast_of_getLast?_eq_some h⟩

/-- The last range in the non-strict start split starts no later than `start` and is sourced from `xs`. -/
private lemma start_split_predecessor_le_and_mem
    (xs : List NR) (start : Int) (prev : NR)
    (hlast :
      (List.span (fun nr => decide (nr.val.lo ≤ start)) xs).fst.getLast? =
        some prev) :
    prev.val.lo ≤ start ∧ prev ∈ xs := by
  have h_span :
      (List.span (fun nr => decide (nr.val.lo ≤ start)) xs).fst =
        xs.takeWhile (fun nr => decide (nr.val.lo ≤ start)) :=
    congrArg Prod.fst (List.span_eq_takeWhile_dropWhile _ _)
  have ⟨hne, heq⟩ := getLast?_eq_some_getLast hlast
  have h_prev_mem_take :
      prev ∈ xs.takeWhile (fun nr => decide (nr.val.lo ≤ start)) := by
    rw [← h_span, ← heq]
    exact List.getLast_mem hne
  have h_pred := List.mem_takeWhile_imp h_prev_mem_take
  exact ⟨of_decide_eq_true h_pred, List.takeWhile_subset _ h_prev_mem_take⟩

/-- Safe version of internalAdd2 that uses the gap hypothesis to construct
a provably-Pairwise result via fromNRs instead of fromNRsUnsafe. -/
def internalAdd2_safe (s : RangeSetBlaze) (r : IntRange)
    (hgap_lt :
      let split := List.span (fun nr => decide (nr.val.lo < r.lo)) s.ranges
      let before := split.fst
      before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < r.lo) :
    RangeSetBlaze :=
  if hempty : r.hi < r.lo then
    s
  else
    let hle : r.lo ≤ r.hi := not_lt.mp hempty
    let xs := s.ranges
    have hok : List.Pairwise NR.before
        (internalAdd2NRs xs r.lo r.hi hle) :=
      ok_internalAdd2NRs xs r.lo r.hi hle s.ok hgap_lt
    fromNRs (internalAdd2NRs xs r.lo r.hi hle) hok

/-- Wrapper for internalAdd2_safe that accepts a gap hypothesis with (≤ start) predicate
and converts it to the (< start) predicate needed by internalAdd2_safe. -/
def internalAdd2_safe_from_le (s : RangeSetBlaze) (r : IntRange)
    (hgap_le :
      let split := List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges
      let before := split.fst
      before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < r.lo) :
    RangeSetBlaze :=
  -- Convert the (≤) gap to (<) gap
  have hgap_lt : let split := List.span (fun nr => decide (nr.val.lo < r.lo)) s.ranges
                 let before := split.fst
                 before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < r.lo := by
    cases hgap_le with
    | inl h_empty =>
        -- The (≤ start) split is empty, so the (< start) split is also empty
        left
        exact span_le_empty_implies_lt_empty s.ranges r.lo h_empty
    | inr h =>
        -- Nonempty (≤) split with a gap at its last element
        obtain ⟨hne_le, h_gap⟩ := h
        let split_le := List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges
        let before_le := split_le.fst
        let split_lt := List.span (fun nr => decide (nr.val.lo < r.lo)) s.ranges
        let before_lt := split_lt.fst

        -- Key: x = last of (≤ split) has x.hi + 1 < r.lo, so x.lo < r.lo
        let x := before_le.getLast hne_le
        have hx_gap : x.val.hi + 1 < r.lo := h_gap
        have hx_prop : x.val.lo ≤ x.val.hi := x.property
        have hx_lt : x.val.lo < r.lo := calc x.val.lo
          _ ≤ x.val.hi := hx_prop
          _ < x.val.hi + 1 := by omega
          _ < r.lo := hx_gap

        -- The two splits are equal (both cut at the same point)
        have before_eq : before_lt = before_le := by
          unfold before_lt split_lt before_le split_le
          simp only [List.span_eq_takeWhile_dropWhile]
          -- Prove that takeWhile (< r.lo) consumes exactly the same prefix as takeWhile (≤ r.lo)
          -- Key: the last element x of before_le satisfies x.lo < r.lo (proven above)
          -- Strategy: show both takeWhile operations stop at the same place
          have key : ∀ nr ∈ s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)), nr.val.lo < r.lo := by
            intro nr hnr
            -- All elements in before_le satisfy nr.lo ≤ r.lo (by definition of takeWhile)
            have h_le : nr.val.lo ≤ r.lo := by
              have h_pred := List.mem_takeWhile_imp hnr
              exact of_decide_eq_true h_pred
            -- If nr = x (the last element), we have nr.lo < r.lo by hx_lt
            by_cases h_eq : nr = x
            · rw [h_eq]; exact hx_lt
            · -- If nr ≠ x, then nr appears before x in the list
              -- Since s.ranges is Pairwise (· ≺ ·) and x is the last in before_le,
              -- we have nr.val.hi + 1 < x.val.lo, so nr.lo ≤ nr.hi < x.lo < r.lo

              -- First establish that before_le equals the takeWhile result
              have before_le_eq : before_le = s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) := by
                unfold before_le split_le
                simp only [List.span_eq_takeWhile_dropWhile]

              -- Decompose before_le as init ++ [x]
              have h_decomp : ∃ init, before_le = init ++ [x] := by
                use before_le.dropLast
                exact (List.dropLast_append_getLast hne_le).symm
              obtain ⟨init, h_init⟩ := h_decomp

              -- nr is in init (since nr ∈ before_le and nr ≠ x)
              have hnr_init : nr ∈ init := by
                have hnr_before : nr ∈ before_le := by rw [before_le_eq]; exact hnr
                rw [h_init] at hnr_before
                simp at hnr_before
                cases hnr_before with
                | inl h => exact h
                | inr h => exact absurd h h_eq

              -- Get Pairwise property on s.ranges, then restrict to takeWhile
              have h_pw_take : List.Pairwise (· ≺ ·) (s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo))) := by
                have h_decomp : s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) ++
                                s.ranges.dropWhile (fun nr => decide (nr.val.lo ≤ r.lo)) = s.ranges :=
                  List.takeWhile_append_dropWhile
                have h_ok_decomp : List.Pairwise (· ≺ ·) (s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) ++
                                                           s.ranges.dropWhile (fun nr => decide (nr.val.lo ≤ r.lo))) := by
                  rw [h_decomp]; exact s.ok
                exact (List.pairwise_append.mp h_ok_decomp).1

              -- Now apply it to before_le
              have h_pw_before : List.Pairwise (· ≺ ·) before_le := by
                rw [before_le_eq]
                exact h_pw_take

              -- Apply Pairwise relation from the prefix to the final element
              rw [h_init] at h_pw_before
              have h_before : nr ≺ x := by
                have hnr_drop : nr ∈ (init ++ [x]).dropLast := by
                  simpa using hnr_init
                simpa using h_pw_before.rel_dropLast_getLast hnr_drop

              -- Unfold the definition of ≺
              have : nr.val.hi + 1 < x.val.lo := h_before

              calc nr.val.lo
                _ ≤ nr.val.hi := nr.property
                _ < nr.val.hi + 1 := by omega
                _ < x.val.lo := this
                _ < r.lo := hx_lt

          -- Now prove the two takeWhile results are equal
          -- Key insight: every element in takeWhile (≤ r.lo) also satisfies (< r.lo)
          -- We'll use the `key` lemma which applies to s.ranges specifically
          suffices h_suff : ∀ (xs : List NR),
              (∀ nr ∈ xs.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)), nr.val.lo < r.lo) →
              xs.takeWhile (fun nr => decide (nr.val.lo < r.lo)) =
              xs.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) by
            exact h_suff s.ranges key
          intro xs hkey
          induction xs with
          | nil =>
              simp [List.takeWhile]
          | cons hd tl ih =>
              simp only [List.takeWhile]
              by_cases h_hd_le : decide (hd.val.lo ≤ r.lo) = true
              · -- hd satisfies (≤ r.lo), so it should also satisfy (< r.lo)
                have h_hd_lt : decide (hd.val.lo < r.lo) = true := by
                  have h_hd_mem : hd ∈ (hd :: tl).takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) := by
                    simp [List.takeWhile, h_hd_le]
                  have : hd.val.lo < r.lo := hkey hd h_hd_mem
                  exact decide_eq_true this
                simp [h_hd_le, h_hd_lt]
                apply ih
                intro nr hnr
                have : nr ∈ (hd :: tl).takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) := by
                  simp [List.takeWhile, h_hd_le]
                  right
                  exact hnr
                exact hkey nr this
              · -- hd doesn't satisfy (≤ r.lo), so it doesn't satisfy (< r.lo) either
                have h_hd_not_lt : decide (hd.val.lo < r.lo) = false := by
                  simp [decide_eq_false_iff_not, not_lt] at h_hd_le ⊢
                  omega
                simp [h_hd_le, h_hd_not_lt]

        -- Provide the gap witness
        right
        have hne_lt : before_lt ≠ [] := by intro h; rw [before_eq] at h; exact hne_le h
        use hne_lt
        show (split_lt.fst.getLast hne_lt).val.hi + 1 < r.lo
        simp only [split_lt, before_lt, split_le, before_le, before_eq]
        exact h_gap
  internalAdd2_safe s r hgap_lt

/-- Safe extend when `prev` touches/overlaps `r` and `r.hi > prev.hi`.
    We replace `prev` by `extended := [prev.lo, max prev.hi r.hi]` and
    run the same loop on the tail. -/
private def internalAddC_extendPrev_safe
    (s : RangeSetBlaze) (_r : IntRange)
    (start stop : Int)  -- start = r.lo, stop = r.hi
    (before after : List NR) (prev : NR)
    (hDecomp :
      (List.span (fun nr => decide (nr.val.lo ≤ start)) s.ranges
        = (before, after)))
    (hLast : List.getLast? before = some prev)
    (_hNoGap : ¬ (prev.val.hi + 1 < start))
    (_hExtend : prev.val.hi < stop) :
    RangeSetBlaze :=
  -- Decompose before = init ++ [prev]
  -- Since getLast? before = some prev, we know before is non-empty
  have hne : before ≠ [] := by
    intro h; simp [h] at hLast
  let init := before.dropLast
  -- Create extended range that merges prev with r
  let extendedHi := max prev.val.hi stop
  have hExtendedValid : prev.val.lo ≤ extendedHi := by
    have := prev.property
    exact le_trans this (le_max_left _ _)
  let extended := mkNR prev.val.lo extendedHi hExtendedValid
  -- Run deleteExtraNRs_loop to merge with after
  let res := deleteExtraNRs_loop extended after
  -- Build the result
  let newRanges := init ++ res.fst :: res.snd
  -- Prove Pairwise on newRanges
  have hpw_newRanges : List.Pairwise NR.before newRanges := by
    let p := fun nr : NR => decide (nr.val.lo ≤ start)
    have h_s_decomp : s.ranges = before ++ after := by
      have h_span : List.span p s.ranges = (before, after) := by
        simpa [p] using hDecomp
      rw [List.span_eq_takeWhile_dropWhile] at h_span
      calc s.ranges
        _ = s.ranges.takeWhile p ++ s.ranges.dropWhile p :=
          (List.takeWhile_append_dropWhile (p := p) (l := s.ranges)).symm
        _ = before ++ after := by
          have h1 : s.ranges.takeWhile p = before := by
            simpa using congrArg Prod.fst h_span
          have h2 : s.ranges.dropWhile p = after := by
            simpa using congrArg Prod.snd h_span
          rw [h1, h2]
    have h_ok_decomp : List.Pairwise NR.before (before ++ after) := by
      rw [← h_s_decomp]
      exact s.ok

    -- Extract Pairwise for before from s.ok using span decomposition
    have hpw_before : List.Pairwise NR.before before := by
      exact (List.pairwise_append.mp h_ok_decomp).1

    -- Extract Pairwise for init using dropLast
    have hpw_init : List.Pairwise NR.before init := by
      have ⟨hne', heq⟩ := getLast?_eq_some_getLast hLast
      have : before = init ++ [before.getLast hne'] := (List.dropLast_append_getLast hne').symm
      rw [heq] at this
      rw [this] at hpw_before
      exact (List.pairwise_append.mp hpw_before).1

    -- Extract Pairwise for after from s.ok
    have hpw_after : List.Pairwise NR.before after := by
      exact (List.pairwise_append.mp h_ok_decomp).2.1

    -- Use start' := prev.val.lo as our reference point
    let start' := prev.val.lo

    -- Prove extended.val.lo = start' (trivial by definition)
    have h_extended_lo : extended.val.lo = start' := by
      simp only [extended, mkNR, start']

    -- Prove ∀ nr ∈ after, start' ≤ nr.val.lo using Pairwise
    -- Since prev is the last element of before and s.ranges = before ++ after,
    -- all elements in after come after prev in the Pairwise ordering
    have h_after_ge_start' : ∀ nr ∈ after, start' ≤ nr.val.lo := by
      intro nr hmem
      -- From Pairwise on before ++ after, we get that prev ≺ nr for all nr ∈ after
      have h_prev_before_nr : NR.before prev nr :=
        NR.pairwise_before_prefix_last_suffix h_ok_decomp hLast nr hmem
      have h_prev_lo_lt : prev.val.lo < nr.val.lo :=
        NR.before_lo_lt h_prev_before_nr
      have : start' < nr.val.lo := by simpa [start'] using h_prev_lo_lt
      exact this.le

    -- Apply ok_deleteExtraNRs_loop_weak to get Pairwise on (res.fst :: res.snd)
    -- Use start' = prev.val.lo as our reference point
    have hpw_res : List.Pairwise NR.before (res.fst :: res.snd) :=
      ok_deleteExtraNRs_loop_weak start' extended after h_extended_lo h_after_ge_start' hpw_after

    -- Prove cross-relations from init to (res.fst :: res.snd)
    have hcross : ∀ x ∈ init, ∀ y ∈ (res.fst :: res.snd), NR.before x y := by
      intro x hx y hy
      -- From deleteExtraNRs_loop_lo_ge, y.val.lo ≥ start'
      have h_loop_props := deleteExtraNRs_loop_lo_ge start' extended after h_extended_lo h_after_ge_start'
      have h_y_ge : start' ≤ y.val.lo := by
        simp only [List.mem_cons] at hy
        cases hy with
        | inl heq => subst heq; exact le_of_eq h_loop_props.1.symm
        | inr hmem => exact h_loop_props.2 y hmem
      -- From pairwise on before, x ≺ prev
      have ⟨hne', heq⟩ := getLast?_eq_some_getLast hLast
      have h_before_decomp : before = init ++ [before.getLast hne'] := (List.dropLast_append_getLast hne').symm
      rw [heq] at h_before_decomp
      rw [h_before_decomp] at hpw_before
      have h_x_before_prev : NR.before x prev := by
        have hcross_init_prev := (List.pairwise_append.mp hpw_before).2.2
        exact hcross_init_prev x hx prev (by simp)
      -- x.val.hi + 1 < prev.val.lo = start'
      have h_x_hi_lt_start' : x.val.hi + 1 < start' := by
        simp only [start']; exact h_x_before_prev
      -- Therefore x.val.hi + 1 < start' ≤ y.val.lo
      exact lt_of_lt_of_le h_x_hi_lt_start' h_y_ge

    -- Apply pairwise_append to combine
    exact List.pairwise_append.mpr ⟨hpw_init, hpw_res, hcross⟩

  fromNRs newRanges hpw_newRanges
def internalAddC (s : RangeSetBlaze) (r : IntRange) : RangeSetBlaze :=
  let start := r.lo
  let stop := r.hi
  if _hstop : stop < start then
    s
  else
    let xs := s.ranges
    let split := List.span (fun nr => decide (nr.val.lo <= start)) xs
    let before := split.fst
    let after := split.snd
    match h_last : List.getLast? before with
    | none =>
        -- before is empty, so pass the trivial gap
        have h_before_nil : before = [] := by
          cases hb : before with
          | nil => rfl
          | cons hd tl =>
            rw [hb] at h_last
            simp [List.getLast?] at h_last
        have hgap : before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < start := by
          left
          exact h_before_nil
        internalAdd2_safe_from_le s r hgap
    | some prev =>
        if hgap : decide (prev.val.hi + 1 < start) then
          -- prev has a gap, pass it along
          have hgap_proof : before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < start := by
            right
            have hne : before ≠ [] := by
              intro h_empty
              simp [h_empty] at h_last
            use hne
            have ⟨hne', heq⟩ := getLast?_eq_some_getLast h_last
            have : hne = hne' := proof_irrel hne hne'
            rw [this, heq]
            exact of_decide_eq_true hgap
          internalAdd2_safe_from_le s r hgap_proof
        else
          -- No gap case: prev.hi + 1 ≥ start
          -- Check if r extends beyond prev
          if _hextend : stop <= prev.val.hi then
            -- r is fully covered by prev, return unchanged
            s
          else
            -- r extends beyond prev: call safe extend helper
            have hDecomp : List.span (fun nr => decide (nr.val.lo ≤ start)) s.ranges = (before, after) := rfl
            have hNoGap : ¬ (prev.val.hi + 1 < start) := by
              intro h_gap
              have : decide (prev.val.hi + 1 < start) = true := decide_eq_true h_gap
              rw [this] at hgap
              simp at hgap
            have hExtend : prev.val.hi < stop := not_le.mp _hextend
            internalAddC_extendPrev_safe s r start stop before after prev hDecomp h_last hNoGap hExtend

/-- If all `before` satisfy `lo < start`, `inserted.lo = start`, and all `after` satisfy `start ≤ lo`,
then `List.span (·.val.lo < start)` on `before ++ inserted :: after` yields `(before, inserted :: after)`. -/
private lemma span_split_on_splice
    (start : Int)
    (before after : List NR)
    (inserted : NR)
    (h_before_all : ∀ nr ∈ before, nr.val.lo < start)
    (h_inserted_lo : inserted.val.lo = start)
    (_h_after_ge : ∀ nr ∈ after, start ≤ nr.val.lo) :
    List.span (fun nr => decide (nr.val.lo < start)) (before ++ inserted :: after)
      = (before, inserted :: after) := by
  let p : NR → Bool := fun nr => decide (nr.val.lo < start)
  -- Prove via takeWhile/dropWhile
  have h_before_p : ∀ nr ∈ before, p nr = true := by
    intro nr hmem
    simp [p]
    exact h_before_all nr hmem
  have h_inserted_p : p inserted = false := by
    simp [p, h_inserted_lo]
  have htake : (before ++ inserted :: after).takeWhile p = before :=
    by
      rw [List.takeWhile_append_of_pos h_before_p]
      simp [h_inserted_p]
  have hdrop : (before ++ inserted :: after).dropWhile p = inserted :: after :=
    by
      rw [List.dropWhile_append_of_pos h_before_p]
      simp [h_inserted_p]
  rw [List.span_eq_takeWhile_dropWhile]
  rw [htake, hdrop]

/-- For a lower-endpoint-ordered list, the start split has a `< start` prefix, a `≥ start` suffix, and preserves the chain order across their concatenation. -/
private lemma span_props_from_chain
    (xs : List NR) (start : Int)
    (hchain : List.IsChain loLE xs) :
    let p : NR → Bool := fun nr => decide (nr.val.lo < start)
    let split := List.span p xs
    let before := split.fst
    let after := split.snd
    ( (∀ nr ∈ before, nr.val.lo < start)
    ∧ (∀ nr ∈ after, start ≤ nr.val.lo)
    ∧ List.IsChain loLE (before ++ after) ) := by
  let p : NR → Bool := fun nr => decide (nr.val.lo < start)
  let split := List.span p xs
  let before := split.fst
  let after := split.snd
  have h_span : split = (xs.takeWhile p, xs.dropWhile p) :=
    List.span_eq_takeWhile_dropWhile (p := p) (l := xs)

  constructor
  · -- ∀ nr ∈ before, nr.val.lo < start
    intro nr hmem
    show nr.val.lo < start
    have hmem_take : nr ∈ xs.takeWhile p := by
      have h_fst : split.fst = xs.takeWhile p := congrArg Prod.fst h_span
      rw [← h_fst]
      exact hmem
    have := List.mem_takeWhile_imp hmem_take
    simp [p] at this
    exact this

  constructor
  · -- ∀ nr ∈ after, start ≤ nr.val.lo
    intro nr hmem
    show start ≤ nr.val.lo
    exact span_suffix_all_ge_start_of_chain xs start hchain nr hmem

  · -- List.IsChain loLE (before ++ after)
    show List.IsChain loLE (split.fst ++ split.snd)
    have : split = (xs.takeWhile p, xs.dropWhile p) := h_span
    rw [congrArg Prod.fst this, congrArg Prod.snd this]
    have : xs.takeWhile p ++ xs.dropWhile p = xs := by
      exact List.takeWhile_append_dropWhile (p := p) (l := xs)
    rw [this]
    exact hchain

/-- Explicit version: given plain `before`, `after`, `inserted` and the needed properties,
`deleteExtraNRs` over `before ++ inserted :: after` yields the expected set union.
This version has no let-bindings in the type signature, eliminating dependent type issues. -/
private lemma deleteExtraNRs_sets_after_splice_explicit
    (start stop : Int) (_h : start ≤ stop)
    (before after : List NR) (inserted : NR)
    (h_before_all : ∀ nr ∈ before, nr.val.lo < start)
    (h_after_ge : ∀ nr ∈ after, start ≤ nr.val.lo)
    (h_inserted_lo : inserted.val.lo = start)
    (h_inserted_hi : inserted.val.hi = stop)
    (_hchain_before_after : List.IsChain loLE (before ++ after)) :
    algoCListSet (deleteExtraNRs (before ++ inserted :: after) start stop)
      = algoCListSet before ∪ inserted.val.toSet ∪ algoCListSet after := by
  classical
  let p : NR → Bool := fun nr => decide (nr.val.lo < start)

  -- Use span_split_on_splice to show the span decomposes correctly
  have h_span_splice : List.span p (before ++ inserted :: after) = (before, inserted :: after) := by
    exact span_split_on_splice start before after inserted h_before_all h_inserted_lo h_after_ge

  -- inserted breaks the predicate
  have h_inserted_false : p inserted = false := by
    simp [p, h_inserted_lo]

  -- Unfold deleteExtraNRs and rewrite the span
  unfold deleteExtraNRs
  rw [h_span_splice]
  simp only []

  -- Set up the initial value in the cons branch
  set initialHi := max inserted.val.hi stop
  have h_inserted_le : inserted.val.lo ≤ inserted.val.hi := inserted.property
  have h_max_ge : inserted.val.hi ≤ initialHi := le_max_left _ _
  have h_initial_valid : inserted.val.lo ≤ initialHi := le_trans h_inserted_le h_max_ge
  set initial := mkNR inserted.val.lo initialHi h_initial_valid
  set res := deleteExtraNRs_loop initial after

  -- The result is: before ++ res.fst :: res.snd
  have h_result : algoCListSet (before ++ res.fst :: res.snd) =
                  algoCListSet before ∪ algoCListSet (res.fst :: res.snd) := listSet_append _ _
  rw [h_result]

  -- Apply the loop lemma
  have h_initial_lo : initial.val.lo = start := by
    simp [initial, mkNR, h_inserted_lo]
  have h_loop := deleteExtraNRs_loop_sets start after initial h_initial_lo h_after_ge
  rw [h_loop]

  -- Now we have: algoCListSet before ∪ (initial.toSet ∪ algoCListSet after)
  -- Need to show this equals: algoCListSet before ∪ inserted.toSet ∪ algoCListSet after
  -- Prove initial.toSet = inserted.toSet
  have h_initial_eq : initial.val.toSet = inserted.val.toSet := by
    have h_init_hi : initialHi = max stop stop := by
      simp [initialHi, h_inserted_hi]
    have : initialHi = stop := by simp [h_init_hi]
    simp [initial, mkNR, IntRange.toSet, this, h_inserted_lo, h_inserted_hi]

  rw [h_initial_eq, Set.union_assoc]

/-- Core list lemma: inserting [start,stop] via `internalAdd2NRs` preserves sets. -/
private lemma internalAdd2NRs_sets
    (xs : List NR) (start stop : Int) (h : start ≤ stop)
    (hchain : List.IsChain loLE xs) :
  algoCListSet (internalAdd2NRs xs start stop h)
    = algoCListSet xs ∪ (mkNR start stop h).val.toSet := by
  -- Unfold to expose deleteExtraNRs
  unfold internalAdd2NRs

  -- Get the span decomposition and its properties using our new helper
  let p : NR → Bool := fun nr => decide (nr.val.lo < start)
  let split := List.span p xs
  let before := split.fst
  let after := split.snd

  -- Extract properties from the chain
  have ⟨h_before_all, h_after_ge, h_chain_concat⟩ := span_props_from_chain xs start hchain

  -- Set up inserted
  set inserted := mkNR start stop h
  have h_inserted_lo : inserted.val.lo = start := by simp [inserted, mkNR]
  have h_inserted_hi : inserted.val.hi = stop := by simp [inserted, mkNR]

  -- Apply the explicit splice lemma
  have h_splice := deleteExtraNRs_sets_after_splice_explicit start stop h before after inserted
    h_before_all h_after_ge h_inserted_lo h_inserted_hi h_chain_concat

  -- Now prove xs = before ++ after to rewrite algoCListSet xs
  have h_xs_eq : xs = before ++ after := by
    have h_span := List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
    have h_fst : before = xs.takeWhile p := congrArg Prod.fst h_span
    have h_snd : after = xs.dropWhile p := congrArg Prod.snd h_span
    rw [h_fst, h_snd]
    exact (List.takeWhile_append_dropWhile (p := p) (l := xs)).symm

  -- The LHS unfolds to deleteExtraNRs applied to the spliced list
  -- We need to show this equals the RHS
  calc algoCListSet (internalAdd2NRs xs start stop h)
    _ = algoCListSet (deleteExtraNRs (before ++ inserted :: after) start stop) := by rfl
    _ = algoCListSet before ∪ inserted.val.toSet ∪ algoCListSet after := h_splice
    _ = algoCListSet before ∪ algoCListSet after ∪ inserted.val.toSet := by ac_rfl
    _ = algoCListSet (before ++ after) ∪ inserted.val.toSet := by rw [← algoCListSet_append]
    _ = algoCListSet xs ∪ inserted.val.toSet := by rw [← h_xs_eq]

-- Bridge lemma: algoCListSet here matches the foldr pattern used in Basic.lean's listToSet
private lemma algoCListSet_eq_foldr (rs : List NR) :
    algoCListSet rs = rs.foldr (fun r acc => r.val.toSet ∪ acc) ∅ := rfl

/-- Safe insertion: set-level correctness. -/
theorem internalAdd2_safe_toSet
    (s : RangeSetBlaze) (r : IntRange)
    (hgap_lt :
      let split := List.span (fun nr => decide (nr.val.lo < r.lo)) s.ranges
      let before := split.fst
      before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < r.lo) :
  (internalAdd2_safe s r hgap_lt).toSet = s.toSet ∪ r.toSet := by
  by_cases hempty : r.hi < r.lo
  · -- empty range
    have h_empty_set : r.toSet = (∅ : Set Int) := IntRange.toSet_eq_empty_of_hi_lt_lo hempty
    simp [internalAdd2_safe, hempty, h_empty_set, Set.union_comm]
  · -- non-empty range
    have hle : r.lo ≤ r.hi := not_lt.mp hempty
    have hchain : List.IsChain loLE s.ranges :=
      pairwise_before_implies_chain_loLE s.ranges s.ok
    -- use the list lemma
    have hsets := internalAdd2NRs_sets s.ranges r.lo r.hi hle hchain
    -- The result is fromNRs with ok_internalAdd2NRs
    simp only [internalAdd2_safe, hempty, dite_false]
    -- fromNRs just wraps the list, so toSet unfolds to foldr
    unfold fromNRs RangeSetBlaze.toSet
    simp only []
    -- Now both sides are foldr, use the list lemma
    have h1 : algoCListSet (internalAdd2NRs s.ranges r.lo r.hi hle) =
              (internalAdd2NRs s.ranges r.lo r.hi hle).foldr (fun r acc => r.val.toSet ∪ acc) ∅ := rfl
    have h2 : algoCListSet s.ranges = s.ranges.foldr (fun r acc => r.val.toSet ∪ acc) ∅ := rfl
    rw [← h1, ← h2, hsets]
    simp [mkNR]

/-- Bridge: the `_from_le` wrapper preserves the same set equality as `internalAdd2_safe`. -/
theorem internalAdd2_safe_from_le_toSet
    (s : RangeSetBlaze) (r : IntRange)
    (hgap_le :
      let split := List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges
      let before := split.fst
      before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < r.lo) :
  (internalAdd2_safe_from_le s r hgap_le).toSet = s.toSet ∪ r.toSet := by
  -- unfold and convert the hypothesis using span_le_empty_implies_lt_empty
  unfold internalAdd2_safe_from_le
  -- The conversion is already done in the definition, just apply the theorem
  exact internalAdd2_safe_toSet s r _

/-- Set-correctness for the extend-prev branch. -/
theorem internalAddC_extendPrev_safe_toSet
    (s : RangeSetBlaze) (r : IntRange)
    (start stop : Int)
    (before after : List NR) (prev : NR)
    (hDecomp : List.span (fun nr => decide (nr.val.lo ≤ start)) s.ranges = (before, after))
    (hLast : List.getLast? before = some prev)
    (hNoGap : ¬ (prev.val.hi + 1 < start))
    (hExtend : prev.val.hi < stop)
    (hStartEq : start = r.lo)
    (hStopEq : stop = r.hi) :
  (internalAddC_extendPrev_safe s r start stop before after prev hDecomp hLast hNoGap hExtend).toSet
    = s.toSet ∪ r.toSet := by
  -- Unfold the definition
  unfold internalAddC_extendPrev_safe
  simp only [fromNRs]
  rw [RangeSetBlaze.toSet_eq_listToSet]

  -- Set up the local definitions from the function body
  have hne : before ≠ [] := by intro h; simp [h] at hLast
  let init := before.dropLast
  let extendedHi := max prev.val.hi stop
  have hExtendedValid : prev.val.lo ≤ extendedHi := by
    have := prev.property
    exact le_trans this (le_max_left _ _)
  let extended := mkNR prev.val.lo extendedHi hExtendedValid
  let res := deleteExtraNRs_loop extended after
  let newRanges := init ++ res.fst :: res.snd

  -- Step 1: Decompose s.toSet
  -- We have s.ranges = before ++ after and before = init ++ [prev]
  have ⟨hne', heq⟩ := getLast?_eq_some_getLast hLast
  have h_before_decomp : before = init ++ [prev] := by
    have : before = before.dropLast ++ [before.getLast hne'] := (List.dropLast_append_getLast hne').symm
    rw [heq] at this
    exact this

  have h_s_ranges_decomp : s.ranges = before ++ after := by
    let p := fun nr : NR => decide (nr.val.lo ≤ start)
    have := List.span_eq_takeWhile_dropWhile (p := p) (l := s.ranges)
    calc s.ranges
      _ = s.ranges.takeWhile p ++ s.ranges.dropWhile p := (List.takeWhile_append_dropWhile (p := p) (l := s.ranges)).symm
      _ = before ++ after := by
        have h1 : before = s.ranges.takeWhile p := by
          rw [List.span_eq_takeWhile_dropWhile] at hDecomp
          simp only [Prod.mk.injEq] at hDecomp
          exact hDecomp.1.symm
        have h2 : after = s.ranges.dropWhile p := by
          rw [List.span_eq_takeWhile_dropWhile] at hDecomp
          simp only [Prod.mk.injEq] at hDecomp
          exact hDecomp.2.symm
        rw [h1, h2]

  have h_s_toSet : s.toSet = algoCListSet init ∪ prev.val.toSet ∪ algoCListSet after := by
    have : s.toSet = algoCListSet s.ranges := RangeSetBlaze.toSet_eq_listToSet s
    rw [this, h_s_ranges_decomp, h_before_decomp]
    rw [algoCListSet_append, algoCListSet_append]
    simp only [algoCListSet_cons, algoCListSet_nil, Set.union_empty]

  -- Step 2: Show extended.toSet = prev.toSet ∪ r.toSet
  have h_last_span :
      (List.span (fun nr => decide (nr.val.lo ≤ start)) s.ranges).fst.getLast? =
        some prev := by
    rw [hDecomp]
    exact hLast
  have h_prev_lo_le_start : prev.val.lo ≤ start :=
    (start_split_predecessor_le_and_mem s.ranges start prev h_last_span).1

  have h_extended_toSet : extended.val.toSet = prev.val.toSet ∪ r.toSet := by
    have horder : prev.val.lo ≤ r.lo := by rw [← hStartEq]; exact h_prev_lo_le_start
    have htouch : ¬ (prev.val.hi + 1 < r.lo) := by rw [← hStartEq]; exact hNoGap
    have h_r_valid : r.lo ≤ r.hi := by
      rw [← hStartEq, ← hStopEq]
      calc start ≤ prev.val.hi + 1 := not_lt.mp hNoGap
        _ ≤ stop := by have := hExtend; omega
    have h_max_stop_eq_rhi : max prev.val.hi stop = r.hi := by
      rw [← hStopEq, max_eq_right]; exact le_of_lt hExtend
    have h_max_rhi_eq_rhi : max prev.val.hi r.hi = r.hi := by
      rw [max_eq_right]; rw [← hStopEq]; exact le_of_lt hExtend
    have h_merged := merge_step_sets prev (mkNR r.lo r.hi h_r_valid) horder htouch
    simp only [mkNR, IntRange.toSet] at h_merged
    simp only [extended, mkNR, extendedHi, IntRange.toSet]
    rw [h_max_rhi_eq_rhi] at h_merged
    rw [h_max_stop_eq_rhi]
    exact h_merged.symm

  -- Step 3: Apply deleteExtraNRs_loop_sets
  let start' := prev.val.lo
  have h_extended_lo : extended.val.lo = start' := by simp only [extended, mkNR, start']

  have h_after_ge_start' : ∀ nr ∈ after, start' ≤ nr.val.lo := by
    intro nr hmem
    -- From Pairwise on s.ranges and prev being last of before
    have h_ok_decomp : List.Pairwise NR.before (before ++ after) := by
      rw [← h_s_ranges_decomp]; exact s.ok
    have h_prev_before_nr : NR.before prev nr :=
      NR.pairwise_before_prefix_last_suffix h_ok_decomp hLast nr hmem
    show start' ≤ nr.val.lo
    have h_prev_lo_lt : prev.val.lo < nr.val.lo :=
      NR.before_lo_lt h_prev_before_nr
    have h_start_lt : start' < nr.val.lo := by simpa [start'] using h_prev_lo_lt
    exact h_start_lt.le

  have h_loop_sets := deleteExtraNRs_loop_sets start' after extended h_extended_lo h_after_ge_start'

  -- Step 4: Assemble the result
  calc algoCListSet newRanges
    _ = algoCListSet (init ++ res.fst :: res.snd) := rfl
    _ = algoCListSet init ∪ algoCListSet (res.fst :: res.snd) := algoCListSet_append init (res.fst :: res.snd)
    _ = algoCListSet init ∪ (extended.val.toSet ∪ algoCListSet after) := by rw [h_loop_sets]
    _ = algoCListSet init ∪ ((prev.val.toSet ∪ r.toSet) ∪ algoCListSet after) := by rw [h_extended_toSet]
    _ = (algoCListSet init ∪ prev.val.toSet ∪ algoCListSet after) ∪ r.toSet := by ac_rfl
    _ = s.toSet ∪ r.toSet := by rw [h_s_toSet]

-- Main correctness theorem for internalAddC
theorem internalAddC_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAddC s r).toSet = s.toSet ∪ r.toSet := by
  unfold internalAddC
  by_cases hempty : r.hi < r.lo
  case pos =>
    -- empty range case
    simp [hempty]
    have h_empty_set : r.toSet = ∅ := IntRange.toSet_eq_empty_of_hi_lt_lo hempty
    rw [h_empty_set, Set.union_empty]
  case neg =>
    simp [hempty]
    -- match on getLast?
    split
    case h_1 =>
      -- none case: before = [], call internalAdd2_safe_from_le
      exact internalAdd2_safe_from_le_toSet s r _
    case h_2 =>
      -- some prev case
      split
      case isTrue =>
        -- gap case: prev.hi + 1 < start, call internalAdd2_safe_from_le
        exact internalAdd2_safe_from_le_toSet s r _
      case isFalse =>
        -- no gap case: check if covered or extend
        split
        case isTrue =>
          -- covered case: r.hi ≤ prev.hi, return s unchanged
          -- Need to show s.toSet ∪ r.toSet = s.toSet, i.e., r.toSet ⊆ s.toSet
          rename_i prev h_last h_no_gap h_covered
          have h_r_covered : r.toSet ⊆ s.toSet := by
            -- prev is from getLast? of span (≤ r.lo), so prev.lo ≤ r.lo
            have h_prev_props :=
              start_split_predecessor_le_and_mem s.ranges r.lo prev h_last
            have h_prev_lo_le : prev.val.lo ≤ r.lo := h_prev_props.1
            -- r.hi ≤ prev.hi from h_covered
            have h_r_hi_le : r.hi ≤ prev.val.hi := h_covered
            -- Show r.toSet ⊆ prev.toSet ⊆ s.toSet
            have h_r_subset_prev : r.toSet ⊆ prev.val.toSet := by
              intro x hx
              simp [IntRange.toSet] at hx ⊢
              exact ⟨le_trans h_prev_lo_le hx.1, le_trans hx.2 h_r_hi_le⟩
            have h_prev_in_s : prev.val.toSet ⊆ s.toSet := by
              -- s.toSet = s.ranges.foldr (fun r acc => r.val.toSet ∪ acc) ∅ by definition
              -- algoCListSet s.ranges = s.ranges.foldr (fun r acc => r.val.toSet ∪ acc) ∅ by algoCListSet_eq_foldr
              -- So algoCListSet s.ranges = s.toSet definitionally
              have h_algoC_eq_toSet : algoCListSet s.ranges = s.toSet := by
                unfold RangeSetBlaze.toSet
                rw [algoCListSet_eq_foldr]
              have h_subset_algoC :=
                nr_mem_ranges_subset_algoCListSet s.ranges prev h_prev_props.2
              rw [h_algoC_eq_toSet] at h_subset_algoC
              exact h_subset_algoC
            exact Set.Subset.trans h_r_subset_prev h_prev_in_s
          -- Goal reduces to s.toSet = s.toSet ∪ r.toSet after unfolding
          show s.toSet = s.toSet ∪ r.toSet
          rw [Set.union_eq_self_of_subset_right h_r_covered]
        case isFalse =>
          -- extend case: prev.hi < r.hi, call internalAddC_extendPrev_safe
          rename_i prev h_last h_no_gap h_not_covered
          have h_extend : prev.val.hi < r.hi := not_le.mp h_not_covered
          have h_start : r.lo = r.lo := rfl
          have h_stop : r.hi = r.hi := rfl
          -- Build the decomposition proof: span gives (before, after)
          have h_decomp : List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges =
                          (List.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges,
                           List.dropWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges) :=
            List.span_eq_takeWhile_dropWhile _ _
          -- Convert h_last from span.fst to takeWhile
          have h_last_tw : (List.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges).getLast? = some prev := by
            have : (List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges).1 =
                   List.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges :=
              congrArg Prod.fst h_decomp
            rw [← this]
            exact h_last
          -- Now apply the theorem with this decomposition
          exact internalAddC_extendPrev_safe_toSet s r r.lo r.hi
                  (List.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges)
                  (List.dropWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges)
                  prev h_decomp h_last_tw h_no_gap h_extend h_start h_stop

open Classical
open IntRange

end RangeSetBlaze
