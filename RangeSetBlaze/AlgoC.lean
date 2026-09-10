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

/-- In pairwise gap-separated ranges, every range after the strict-start split
has lower endpoint at least `start`. -/
private lemma strict_start_split_suffix_lower_bound
    (xs : List NR) (start : Int)
    (hpw : List.Pairwise NR.before xs) :
    let p : NR → Bool := fun nr => decide (nr.val.lo < start)
    let split := List.span p xs
    ∀ nr ∈ split.snd, start ≤ nr.val.lo := by
  dsimp only
  rw [List.span_eq_takeWhile_dropWhile]
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : x.val.lo < start
      · rw [List.dropWhile_cons_of_pos (by simp [hx])]
        exact ih hpw.tail
      · rw [List.dropWhile_cons_of_neg (by simp [hx])]
        intro nr hmem
        rw [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact not_lt.mp hx
        · exact le_trans (not_lt.mp hx)
            (NR.before_lo_lt (List.rel_of_pairwise_cons hpw hmem)).le

/-- One semantic contract for the scan: it preserves the represented union,
keeps every output lower endpoint at or after the scan start, and preserves
ordering whenever the pending input is ordered. -/
private lemma deleteExtraNRs_loop_preserves_order_lower_bound_and_union
    (start : Int) (current : NR) (pending : List NR)
    (hlo : current.val.lo = start)
    (hge : ∀ nr ∈ pending, start ≤ nr.val.lo) :
    let res := deleteExtraNRs_loop current pending
    (List.Pairwise NR.before pending →
      List.Pairwise NR.before (res.fst :: res.snd)) ∧
      (∀ nr ∈ (res.fst :: res.snd), start ≤ nr.val.lo) ∧
      algoCListSet (res.fst :: res.snd) =
        current.val.toSet ∪ algoCListSet pending := by
  induction pending generalizing current with
  | nil =>
      simp [deleteExtraNRs_loop, algoCListSet_nil, Set.union_comm, hlo]
  | cons next tail ih =>
      dsimp [deleteExtraNRs_loop]
      by_cases hmerge : next.val.lo ≤ current.val.hi + 1
      · set merged :=
          mkNR current.val.lo (max current.val.hi next.val.hi)
            (by
              have hc : current.val.lo ≤ current.val.hi := current.property
              exact le_trans hc (le_max_left _ _)) with hmerged_def
        have horder : current.val.lo ≤ next.val.lo := by
          have : start ≤ next.val.lo := hge next (by simp)
          simpa [hlo] using this
        have htouch : ¬ (current.val.hi + 1 < next.val.lo) := not_lt.mpr hmerge
        have hge' : ∀ nr ∈ tail, start ≤ nr.val.lo := by
          intro nr hmem
          exact hge nr (by simp [hmem])
        have hlo' : merged.val.lo = start := by
          simp [hmerged_def, mkNR, hlo]
        have hrec := ih merged hlo' hge'
        have hstep :
            deleteExtraNRs_loop current (next :: tail) =
              deleteExtraNRs_loop merged tail := by
          simpa [hmerged_def] using
            (deleteExtraNRs_loop_cons_merge current next tail hmerge)
        have hmerged_toSet :
            merged.val.toSet = current.val.toSet ∪ next.val.toSet := by
          simpa [hmerged_def] using
            (merge_step_sets current next horder htouch).symm
        have horder_out :
            List.Pairwise NR.before (next :: tail) →
            List.Pairwise NR.before
              ((deleteExtraNRs_loop current (next :: tail)).fst ::
                (deleteExtraNRs_loop current (next :: tail)).snd) := by
          intro hpw
          have hpw_tail : List.Pairwise NR.before tail := by
            cases hpw with
            | cons _ htail => exact htail
          simpa [hstep] using hrec.1 hpw_tail
        have hbound_out :
            ∀ nr ∈ ((deleteExtraNRs_loop current (next :: tail)).fst ::
              (deleteExtraNRs_loop current (next :: tail)).snd),
              start ≤ nr.val.lo := by
          simpa [hstep] using hrec.2.1
        have hsets_out :
            algoCListSet
                ((deleteExtraNRs_loop current (next :: tail)).fst ::
                  (deleteExtraNRs_loop current (next :: tail)).snd) =
              current.val.toSet ∪ algoCListSet (next :: tail) := by
          calc
            algoCListSet
                ((deleteExtraNRs_loop current (next :: tail)).fst ::
                  (deleteExtraNRs_loop current (next :: tail)).snd)
                = merged.val.toSet ∪ algoCListSet tail := by
                    simpa [hstep] using hrec.2.2
            _ = (current.val.toSet ∪ next.val.toSet) ∪ algoCListSet tail := by
                  rw [hmerged_toSet]
            _ = current.val.toSet ∪ algoCListSet (next :: tail) := by
                  simp [algoCListSet_cons]; ac_rfl
        exact ⟨horder_out, hbound_out, hsets_out⟩
      · have h_loop_eq :
            deleteExtraNRs_loop current (next :: tail) = (current, next :: tail) := by
          exact deleteExtraNRs_loop_cons_noMerge current next tail hmerge
        have horder_out :
          List.Pairwise NR.before (next :: tail) →
          List.Pairwise NR.before
            ((deleteExtraNRs_loop current (next :: tail)).fst ::
              (deleteExtraNRs_loop current (next :: tail)).snd) := by
          intro hpwP
          have h_head : NR.before current next := by
            unfold NR.before
            simpa using (not_le.mp hmerge)
          have hchain : List.IsChain loLE (next :: tail) :=
            pairwise_before_implies_chain_loLE (next :: tail) (by
              cases hpwP with
              | cons hx htail => exact List.Pairwise.cons hx htail)
          have hnext_le : ∀ z ∈ tail, next.val.lo ≤ z.val.lo :=
            fun z hz => hchain.rel_cons hz
          have h_current_tail : ∀ z ∈ tail, NR.before current z := by
            intro z hz
            have hnext_gap : current.val.hi + 1 < next.val.lo := by
              simpa [NR.before] using h_head
            have hz_gap : current.val.hi + 1 < z.val.lo :=
              lt_of_lt_of_le hnext_gap (hnext_le z hz)
            simpa [NR.before] using hz_gap
          have hpw_tail : List.Pairwise NR.before tail := by
            cases hpwP with
            | cons _ htail => exact htail
          rw [h_loop_eq]
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
        have hbound_out :
            ∀ nr ∈ ((deleteExtraNRs_loop current (next :: tail)).fst ::
              (deleteExtraNRs_loop current (next :: tail)).snd),
              start ≤ nr.val.lo := by
          rw [h_loop_eq]
          intro nr hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · simp [hlo]
          · exact hge nr (by simp [hmem])
        have hsets_out :
            algoCListSet
                ((deleteExtraNRs_loop current (next :: tail)).fst ::
                  (deleteExtraNRs_loop current (next :: tail)).snd) =
              current.val.toSet ∪ algoCListSet (next :: tail) := by
          rw [h_loop_eq]
          simp [Set.union_left_comm]
        exact ⟨horder_out, hbound_out, hsets_out⟩
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
  intro pending current hlo hge
  exact (deleteExtraNRs_loop_preserves_order_lower_bound_and_union
    start current pending hlo hge).2.2


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

/-- Inserting a nonempty interval across a strict start gap preserves both the
ordered representation and the exact represented union. -/
private lemma internalAdd2NRs_preserves_order_and_union
    (xs : List NR) (start stop : Int) (h_le : start ≤ stop)
    (hpw : List.Pairwise NR.before xs)
    (hgap : let split := List.span (fun nr => decide (nr.val.lo < start)) xs
            let before := split.fst
            before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < start) :
    List.Pairwise NR.before (internalAdd2NRs xs start stop h_le) ∧
      algoCListSet (internalAdd2NRs xs start stop h_le) =
        algoCListSet xs ∪ (mkNR start stop h_le).val.toSet := by
  -- Both guarantees use the same strict-start split.
  set p : NR → Bool := (fun nr => decide (nr.val.lo < start)) with hp
  set split := List.span p xs
  set before := split.fst
  set after := split.snd
  set inserted := mkNR start stop h_le
  set ys := before ++ inserted :: after

  have h_span_eq : split = (xs.takeWhile p, xs.dropWhile p) :=
    List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
  have h_before_eq : before = xs.takeWhile p := by
    simpa [before] using congrArg Prod.fst h_span_eq
  have h_after_eq : after = xs.dropWhile p := by
    simpa [after] using congrArg Prod.snd h_span_eq

  -- The prefix satisfies the strict split predicate, while the inserted range
  -- is its first failure.
  have h_before_all : ∀ nr ∈ before, p nr = true := by
    intro nr hmem
    rw [h_before_eq] at hmem
    exact List.mem_takeWhile_imp hmem

  have h_inserted_false : p inserted = false := by
    simp only [p, decide_eq_false_iff_not, not_lt]
    show start ≤ inserted.val.lo
    simp [inserted, mkNR]

  have h_span_ys : List.span p ys = (before, inserted :: after) := by
    have htake : ys.takeWhile p = before := by
      rw [List.takeWhile_append_of_pos h_before_all]
      simp [h_inserted_false]
    have hdrop : ys.dropWhile p = inserted :: after := by
      rw [List.dropWhile_append_of_pos h_before_all]
      simp [h_inserted_false]
    simp [List.span_eq_takeWhile_dropWhile, htake, hdrop]

  have h_span_match :
    List.span (fun nr => decide (nr.val.lo < start)) ys = (before, inserted :: after) := by
    convert h_span_ys using 1

  -- Expose the one loop result consumed by both semantic guarantees.
  set curr := inserted
  set initialHi := max curr.val.hi stop
  have hcurr : curr.val.lo ≤ curr.val.hi := curr.property
  have hmax_prop : curr.val.hi ≤ initialHi := le_max_left _ _
  set initial := mkNR curr.val.lo initialHi (le_trans hcurr hmax_prop)
  set result := deleteExtraNRs_loop initial after

  have h_output :
      internalAdd2NRs xs start stop h_le = before ++ result.fst :: result.snd := by
    unfold internalAdd2NRs deleteExtraNRs
    change deleteExtraNRs ys start stop = _
    unfold deleteExtraNRs
    rw [h_span_match]

  have hpw_before : List.Pairwise NR.before before := by
    exact List.Pairwise.sublist
      (by rw [h_before_eq]
          exact (List.takeWhile_sublist p : (xs.takeWhile p).Sublist xs)) hpw

  have hpw_after : List.Pairwise NR.before after := by
    exact List.Pairwise.sublist
      (by rw [h_after_eq]
          exact (List.dropWhile_sublist p : (xs.dropWhile p).Sublist xs)) hpw

  have h_after_ge : ∀ nr ∈ after, start ≤ nr.val.lo := by
    simpa [p, split, after] using
      (strict_start_split_suffix_lower_bound xs start hpw)

  have h_initial_lo : initial.val.lo = start := by
    simp [initial, curr, inserted, mkNR]
  have h_loop_props :=
    deleteExtraNRs_loop_preserves_order_lower_bound_and_union
      start initial after h_initial_lo h_after_ge

  have hpw_result : List.Pairwise NR.before (result.fst :: result.snd) := by
    exact h_loop_props.1 hpw_after

  -- A strict gap before `start`, combined with the loop's preserved lower
  -- bound, establishes every prefix-to-result ordering edge.
  have hcross : ∀ x ∈ before, ∀ y ∈ (result.fst :: result.snd), NR.before x y := by
    intro x hx y hy
    unfold NR.before
    have hy_ge : start ≤ y.val.lo := by
      exact h_loop_props.2.1 y (by simpa [result] using hy)

    have hgap_before : before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < start := hgap
    rcases hgap_before with hempty | ⟨hne, hlast_gap⟩
    ·
      rw [hempty] at hx
      cases hx
    ·
      have hall_before : ∀ x ∈ before, x.val.hi + 1 < start :=
        all_before_strict_before_start before start hpw_before hne hlast_gap
      have hx_lt : x.val.hi + 1 < start := hall_before x hx
      exact lt_of_lt_of_le hx_lt hy_ge

  have horder : List.Pairwise NR.before (internalAdd2NRs xs start stop h_le) := by
    rw [h_output]
    exact List.pairwise_append.mpr ⟨hpw_before, hpw_result, hcross⟩

  have h_xs_eq : xs = before ++ after := by
    rw [h_before_eq, h_after_eq]
    exact (List.takeWhile_append_dropWhile (p := p) (l := xs)).symm

  have h_initial_set : initial.val.toSet = inserted.val.toSet := by
    have h_initial_hi : initialHi = stop := by
      simp [initialHi, curr, inserted, mkNR]
    simp [initial, curr, inserted, mkNR, IntRange.toSet, h_initial_hi]

  have hsets :
      algoCListSet (internalAdd2NRs xs start stop h_le) =
        algoCListSet xs ∪ inserted.val.toSet := by
    rw [h_output, algoCListSet_append]
    rw [h_loop_props.2.2]
    rw [h_initial_set]
    rw [h_xs_eq, algoCListSet_append]
    ac_rfl

  exact ⟨horder, by simpa [inserted] using hsets⟩

/-- In an ordered range list, a strict gap after the non-strict start prefix
makes that whole prefix strict, so the two start prefixes have the same gap. -/
private theorem nonstrict_start_gap_implies_strict_start_gap
    (xs : List NR) (start : Int)
    (hpair : List.Pairwise NR.before xs)
    (hgap_le :
      let before := (List.span (fun nr => decide (nr.val.lo ≤ start)) xs).fst
      before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < start) :
    let before := (List.span (fun nr => decide (nr.val.lo < start)) xs).fst
    before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < start := by
  simp only [List.span_eq_takeWhile_dropWhile] at hgap_le ⊢
  let strict : NR → Bool := fun nr => decide (nr.val.lo < start)
  let nonstrict : NR → Bool := fun nr => decide (nr.val.lo ≤ start)
  let hasGap : List NR → Prop := fun before =>
    before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < start
  change hasGap (xs.takeWhile nonstrict) at hgap_le
  change hasGap (xs.takeWhile strict)
  have h_nested :
      xs.takeWhile strict = (xs.takeWhile nonstrict).takeWhile strict := by
    rw [List.takeWhile_takeWhile]
    congr 2
    funext nr
    simp [strict, nonstrict]
    exact le_of_lt
  rcases hgap_le with h_empty | ⟨hne, hlast⟩
  · left
    rw [h_nested, h_empty]
    simp
  · have hpair_lo : List.Pairwise (fun a b : NR => a.val.lo ≤ b.val.lo)
        (xs.takeWhile nonstrict) :=
      (List.Pairwise.sublist (List.takeWhile_sublist nonstrict) hpair).imp
        fun hab => (NR.before_lo_lt hab).le
    have hlast_lo : ((xs.takeWhile nonstrict).getLast hne).val.lo < start :=
      lt_of_le_of_lt ((xs.takeWhile nonstrict).getLast hne).property
        (lt_trans (lt_add_one _) hlast)
    have hall_strict : ∀ nr ∈ xs.takeWhile nonstrict, strict nr := by
      intro nr hnr
      exact decide_eq_true
        (lt_of_le_of_lt (hpair_lo.rel_getLast hnr) hlast_lo)
    have hprefix_eq : (xs.takeWhile nonstrict).takeWhile strict =
        xs.takeWhile nonstrict :=
      List.takeWhile_eq_self_iff.mpr hall_strict
    have heq : xs.takeWhile strict = xs.takeWhile nonstrict :=
      h_nested.trans hprefix_eq
    exact heq.symm ▸
      (show hasGap (xs.takeWhile nonstrict) from Or.inr ⟨hne, hlast⟩)

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
      (internalAdd2NRs_preserves_order_and_union
        xs r.lo r.hi hle s.ok hgap_lt).1
    fromNRs (internalAdd2NRs xs r.lo r.hi hle) hok

/-- Wrapper for internalAdd2_safe that accepts a gap hypothesis with (≤ start) predicate
and converts it to the (< start) predicate needed by internalAdd2_safe. -/
def internalAdd2_safe_from_le (s : RangeSetBlaze) (r : IntRange)
    (hgap_le :
      let split := List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges
      let before := split.fst
      before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < r.lo) :
    RangeSetBlaze :=
  internalAdd2_safe s r
    (nonstrict_start_gap_implies_strict_start_gap s.ranges r.lo s.ok hgap_le)

/-- The extend-predecessor helper has two proof clients: its executable
wrapper needs the ordering invariant, while the public correctness theorem
needs exact set semantics.  This specification derives the split,
predecessor decomposition, and predecessor-to-suffix boundary once, then
exposes both guarantees as projections. -/
private lemma extend_predecessor_preserves_order_and_union
    (s : RangeSetBlaze)
    (start stop : Int)
    (before after : List NR) (prev : NR)
    (hDecomp :
      (List.span (fun nr => decide (nr.val.lo ≤ start)) s.ranges
        = (before, after)))
    (hLast : List.getLast? before = some prev)
    (hNoGap : ¬ (prev.val.hi + 1 < start))
    (hExtend : prev.val.hi < stop) :
    let init := before.dropLast
    let extendedHi := max prev.val.hi stop
    let extended := mkNR prev.val.lo extendedHi (by
      exact le_trans prev.property (le_max_left _ _))
    let res := deleteExtraNRs_loop extended after
    let newRanges := init ++ res.fst :: res.snd
    List.Pairwise NR.before newRanges ∧
      algoCListSet newRanges = s.toSet ∪
        (mkNR start stop (by
          omega)).val.toSet := by
  intro init extendedHi extended res newRanges
  have hne : before ≠ [] := by
    intro h
    simp [h] at hLast
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
  have hpw_before : List.Pairwise NR.before before :=
    (List.pairwise_append.mp h_ok_decomp).1
  have hpw_after : List.Pairwise NR.before after :=
    (List.pairwise_append.mp h_ok_decomp).2.1
  have heq : before.getLast hne = prev :=
    List.getLast_of_getLast?_eq_some hLast
  have h_before_decomp : before = init ++ [prev] := by
    have h := (List.dropLast_append_getLast hne).symm
    rw [heq] at h
    exact h
  have hpw_before_prev : List.Pairwise NR.before (init ++ [prev]) := by
    rw [← h_before_decomp]
    exact hpw_before
  have hpw_init : List.Pairwise NR.before init :=
    (List.pairwise_append.mp hpw_before_prev).1
  have h_prev_before_after : ∀ nr ∈ after, NR.before prev nr := by
    intro nr hmem
    exact NR.pairwise_before_prefix_last_suffix h_ok_decomp hLast nr hmem
  let start' := prev.val.lo
  have h_extended_lo : extended.val.lo = start' := by
    simp only [extended, mkNR, start']
  have h_after_ge_start' : ∀ nr ∈ after, start' ≤ nr.val.lo := by
    intro nr hmem
    have h_prev_lo_lt : prev.val.lo < nr.val.lo :=
      NR.before_lo_lt (h_prev_before_after nr hmem)
    have h_start_lt : start' < nr.val.lo := by
      simpa [start'] using h_prev_lo_lt
    exact h_start_lt.le
  have h_loop_props :=
    deleteExtraNRs_loop_preserves_order_lower_bound_and_union
      start' extended after h_extended_lo h_after_ge_start'
  have hpw_res : List.Pairwise NR.before (res.fst :: res.snd) :=
    h_loop_props.1 hpw_after
  have h_res_lo_ge : ∀ y ∈ (res.fst :: res.snd), start' ≤ y.val.lo := by
    intro y hy
    exact h_loop_props.2.1 y (by simpa [res] using hy)
  have h_init_before_prev : ∀ x ∈ init, NR.before x prev := by
    intro x hx
    exact (List.pairwise_append.mp hpw_before_prev).2.2 x hx prev (by simp)
  have hcross : ∀ x ∈ init, ∀ y ∈ (res.fst :: res.snd), NR.before x y := by
    intro x hx y hy
    have h_x_hi_lt_start' : x.val.hi + 1 < start' := by
      simpa [start', NR.before] using h_init_before_prev x hx
    exact lt_of_lt_of_le h_x_hi_lt_start' (h_res_lo_ge y hy)
  have hpw_newRanges : List.Pairwise NR.before newRanges :=
    List.pairwise_append.mpr ⟨hpw_init, hpw_res, hcross⟩
  have h_last_span :
      (List.span (fun nr => decide (nr.val.lo ≤ start)) s.ranges).fst.getLast? =
        some prev := by
    rw [hDecomp]
    exact hLast
  have h_prev_lo_le_start : prev.val.lo ≤ start :=
    (start_split_predecessor_le_and_mem s.ranges start prev h_last_span).1
  have h_start_stop : start ≤ stop := by
    have h_start : start ≤ prev.val.hi + 1 := le_of_not_gt hNoGap
    omega
  let inserted := mkNR start stop h_start_stop
  have h_extended_toSet : extended.val.toSet = prev.val.toSet ∪ inserted.val.toSet := by
    have horder : prev.val.lo ≤ inserted.val.lo := by
      simpa [inserted, mkNR] using h_prev_lo_le_start
    have htouch : ¬ (prev.val.hi + 1 < inserted.val.lo) := by
      simpa [inserted, mkNR] using hNoGap
    simpa [extended, extendedHi, inserted, mkNR] using
      (merge_step_sets prev inserted horder htouch).symm
  have h_s_toSet : s.toSet = algoCListSet init ∪ prev.val.toSet ∪ algoCListSet after := by
    have h_s_ranges : s.toSet = algoCListSet s.ranges := by
      unfold RangeSetBlaze.toSet
      rfl
    rw [h_s_ranges, h_s_decomp, h_before_decomp]
    rw [algoCListSet_append, algoCListSet_append]
    simp only [algoCListSet_cons, algoCListSet_nil, Set.union_empty]
  constructor
  · exact hpw_newRanges
  · calc
      algoCListSet newRanges
        = algoCListSet (init ++ res.fst :: res.snd) := rfl
      _ = algoCListSet init ∪ algoCListSet (res.fst :: res.snd) :=
        algoCListSet_append init (res.fst :: res.snd)
      _ = algoCListSet init ∪ (extended.val.toSet ∪ algoCListSet after) := by
        rw [h_loop_props.2.2]
      _ = algoCListSet init ∪ ((prev.val.toSet ∪ inserted.val.toSet) ∪ algoCListSet after) := by
        rw [h_extended_toSet]
      _ = (algoCListSet init ∪ prev.val.toSet ∪ algoCListSet after) ∪ inserted.val.toSet := by
        ac_rfl
      _ = s.toSet ∪ inserted.val.toSet := by rw [h_s_toSet]

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
    RangeSetBlaze := by
  let init := before.dropLast
  let extendedHi := max prev.val.hi stop
  have hExtendedValid : prev.val.lo ≤ extendedHi := by
    exact le_trans prev.property (le_max_left _ _)
  let extended := mkNR prev.val.lo extendedHi hExtendedValid
  let res := deleteExtraNRs_loop extended after
  let newRanges := init ++ res.fst :: res.snd
  have hspec := extend_predecessor_preserves_order_and_union s start stop before after prev
    hDecomp hLast _hNoGap _hExtend
  exact fromNRs newRanges hspec.1
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
    have hsets := (internalAdd2NRs_preserves_order_and_union
      s.ranges r.lo r.hi hle s.ok hgap_lt).2
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
  -- The wrapper's named gap conversion supplies `internalAdd2_safe` directly.
  unfold internalAdd2_safe_from_le
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
  have hspec := extend_predecessor_preserves_order_and_union s start stop before after prev
    hDecomp hLast hNoGap hExtend
  have h_start_stop : start ≤ stop := by
    have h_start : start ≤ prev.val.hi + 1 := le_of_not_gt hNoGap
    omega
  have h_interval : (mkNR start stop h_start_stop).val.toSet = r.toSet := by
    simp [mkNR, IntRange.toSet, hStartEq, hStopEq]
  unfold internalAddC_extendPrev_safe
  simp only [fromNRs, RangeSetBlaze.toSet]
  change algoCListSet _ = s.toSet ∪ r.toSet
  simpa [h_interval] using hspec.2

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
          exact internalAddC_extendPrev_safe_toSet s r r.lo r.hi
            (List.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges)
            (List.dropWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges)
            prev (List.span_eq_takeWhile_dropWhile _ _)
            (by simpa only [List.span_eq_takeWhile_dropWhile] using h_last)
            h_no_gap h_extend rfl rfl

open Classical
open IntRange

end RangeSetBlaze
