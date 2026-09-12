import Mathlib.Data.List.TakeWhile
import RangeSetBlaze.Basic

namespace RangeSetBlaze

open IntRange
open IntRange.NR
open scoped IntRange.NR

/-!
Algo C is the list model of the production `RangeSetBlaze` insertion algorithm.
Its executable path deliberately retains the production branches: reject an
empty input, locate the last range whose lower endpoint is at most the input
start, insert after a true gap, return an already-covered input unchanged, or
extend the predecessor and merge forward.

The proof follows the same operation boundaries:

* `deleteExtraNRs_loop` scans the suffix until the first true gap. Its unified
  contract proves ordered output, preservation of the scan's lower bound, and
  exact union preservation in one induction.
* `internalAdd2NRs` inserts at a strict-start split and invokes that merge
  logic. Its contract proves both `List.Pairwise NR.before` and set-union
  correctness.
* `extendPredecessor` replaces a touching predecessor by its
  extension, merges forward, and obtains both guarantees from the
  extend-predecessor contract.
* `internalAddC_toSet` mirrors the executable branches and normally dispatches
  to those contracts; the covered branch uses the shared range-containment
  lemma.

The two start predicates express different boundaries. `internalAddC` uses
`nr.lo ≤ start` so a stored range beginning exactly at `start` is a predecessor
candidate. The insertion helper uses `nr.lo < start` because the newly inserted
range begins at `start` and must not enter the untouched prefix. These
predicates are not equivalent. In the separated-predecessor branch,
`nonstrict_start_gap_implies_strict_start_gap` bridges them: nonempty ranges and
pairwise `NR.before` ordering imply that a non-strict prefix ending before a
strict gap consists entirely of ranges starting strictly below `start`.

The list split, `getLast?`, and `dropLast` operations model `BTreeMap` range and
predecessor operations; they are representation choices, not a different
insertion algorithm. The executable branch structure and the final theorem
`(internalAddC s r).toSet = s.toSet ∪ r.toSet` are protected.
-/

private def mkNR (lo hi : Int) (h : lo ≤ hi) : NR :=
  ⟨{ lo := lo, hi := hi }, h⟩

/-- Safe constructor when you already have the invariant. -/
private def fromNRs (xs : List NR)
  (hcanonical : List.Pairwise NR.before xs) : RangeSetBlaze :=
  { ranges := xs, canonical := hcanonical }

/-- Scan forward from `current`, merging touching or overlapping pending ranges
and stopping at the first range separated by a true gap. -/
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

/-- Set-level description of a single forward merge step. -/
private lemma mergeForward_toSet
    (current next : NR)
    (horder : current.val.lo ≤ next.val.lo)
    (htouch : ¬ (current.val.hi + 1 < next.val.lo)) :
    (mkNR current.val.lo (max current.val.hi next.val.hi)
        (by
          have hc : current.val.lo ≤ current.val.hi := current.property
          have : current.val.hi ≤ max current.val.hi next.val.hi :=
            le_max_left _ _
          exact le_trans hc this)).val.toSet =
      current.val.toSet ∪ next.val.toSet := by
  have hmergeable : NR.mergeable current next :=
    NR.mergeable_of_startsBefore_of_not_before
      (show NR.startsBefore current next from horder) htouch
  simpa [NR.glue, IntRange.mergeRange, mkNR, min_eq_left horder] using
    NR.glue_sets current next hmergeable

/-- Locate the first range not strictly before `start`, extend its upper
endpoint through `stop`, and merge any following ranges that no longer have a
gap. -/
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

/-- Insert a nonempty interval at the strict-start boundary, then merge away
the touching or overlapping suffix. -/
private def internalAdd2NRs (xs : List NR) (start stop : Int)
    (h : start ≤ stop) :
    List NR :=
  let split := List.span (fun nr => decide (nr.val.lo < start)) xs
  let before := split.fst
  let after := split.snd
  let inserted := mkNR start stop h
  deleteExtraNRs (before ++ (inserted :: after)) start stop

open Classical
open IntRange

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
      rangesToSet (res.fst :: res.snd) =
        current.val.toSet ∪ rangesToSet pending := by
  induction pending generalizing current with
  | nil =>
      simp [deleteExtraNRs_loop, Set.union_comm, hlo]
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
            (mergeForward_toSet current next horder htouch)
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
            rangesToSet
                ((deleteExtraNRs_loop current (next :: tail)).fst ::
                  (deleteExtraNRs_loop current (next :: tail)).snd) =
              current.val.toSet ∪ rangesToSet (next :: tail) := by
          calc
            rangesToSet
                ((deleteExtraNRs_loop current (next :: tail)).fst ::
                  (deleteExtraNRs_loop current (next :: tail)).snd)
                = merged.val.toSet ∪ rangesToSet tail := by
                    simpa [hstep] using hrec.2.2
            _ = (current.val.toSet ∪ next.val.toSet) ∪ rangesToSet tail := by
                  rw [hmerged_toSet]
            _ = current.val.toSet ∪ rangesToSet (next :: tail) := by
                  simp [rangesToSet_cons]; ac_rfl
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
          have h_current_tail : ∀ z ∈ tail, NR.before current z := by
            intro z hz
            exact NR.before_trans h_head
              (List.rel_of_pairwise_cons hpwP hz)
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
            · exact hpwP.tail
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
            rangesToSet
                ((deleteExtraNRs_loop current (next :: tail)).fst ::
                  (deleteExtraNRs_loop current (next :: tail)).snd) =
              current.val.toSet ∪ rangesToSet (next :: tail) := by
          rw [h_loop_eq]
          simp [Set.union_left_comm]
        exact ⟨horder_out, hbound_out, hsets_out⟩
/-- If `before` is nonempty and its last element is strictly before `start`,
then every element of `before` is strictly before `start`. -/
private lemma all_before_strict_before_start
    (before : List NR) (start : Int)
    (hpair : List.Pairwise NR.before before)
    (hne : before ≠ [])
    (hlast : (before.getLast hne).val.hi + 1 < start) :
    ∀ x ∈ before, x.val.hi + 1 < start := by
  intro x hx
  by_cases hlastx : x = before.getLast hne
  · simpa [hlastx] using hlast
  · have hdrop := List.mem_dropLast_of_mem_of_ne_getLast hx hlastx
    have hx_before_last := hpair.rel_dropLast_getLast hdrop
    -- x ≺ last ⇒ x.hi + 1 < last.lo, and last.lo ≤ last.hi + 1 < start
    unfold NR.before at hx_before_last
    have last_lo_lt_start : (before.getLast hne).val.lo < start := by
      have : (before.getLast hne).val.lo ≤ (before.getLast hne).val.hi := (before.getLast hne).property
      calc (before.getLast hne).val.lo
        _ ≤ (before.getLast hne).val.hi := this
        _ < (before.getLast hne).val.hi + 1 := by omega
        _ < start := hlast
    exact lt_trans hx_before_last last_lo_lt_start

/-- Inserting a nonempty interval across a strict start gap preserves both the
ordered representation and the exact represented union. -/
private lemma internalAdd2NRs_preserves_order_and_union
    (xs : List NR) (start stop : Int) (h_le : start ≤ stop)
    (hpw : List.Pairwise NR.before xs)
    (hgap : let split := List.span (fun nr => decide (nr.val.lo < start)) xs
            let before := split.fst
            before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < start) :
    List.Pairwise NR.before (internalAdd2NRs xs start stop h_le) ∧
      rangesToSet (internalAdd2NRs xs start stop h_le) =
        rangesToSet xs ∪ (mkNR start stop h_le).val.toSet := by
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
      (NR.strict_start_split_suffix_lower_bound xs start hpw)

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
      rangesToSet (internalAdd2NRs xs start stop h_le) =
        rangesToSet xs ∪ inserted.val.toSet := by
    rw [h_output, rangesToSet_append]
    rw [h_loop_props.2.2]
    rw [h_initial_set]
    rw [h_xs_eq, rangesToSet_append]
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
  rw [h_span] at hlast
  have h_prev_mem_take :
      prev ∈ xs.takeWhile (fun nr => decide (nr.val.lo ≤ start)) := by
    exact List.mem_of_mem_getLast? hlast
  have h_pred := List.mem_takeWhile_imp h_prev_mem_take
  exact ⟨of_decide_eq_true h_pred, List.takeWhile_subset _ h_prev_mem_take⟩

/-- Insert after a strict-start gap and construct the result from the proved
`Pairwise NR.before` invariant. -/
private def insertAtStrictStartGap (s : RangeSetBlaze) (r : IntRange)
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
    have hcanonical : List.Pairwise NR.before
        (internalAdd2NRs xs r.lo r.hi hle) :=
      (internalAdd2NRs_preserves_order_and_union
        xs r.lo r.hi hle s.canonical hgap_lt).1
    fromNRs (internalAdd2NRs xs r.lo r.hi hle) hcanonical

/-- Insert through the non-strict predecessor split after converting its gap
evidence to the strict insertion boundary. -/
private def insertAtNonstrictStartGap (s : RangeSetBlaze) (r : IntRange)
    (hgap_le :
      let split := List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges
      let before := split.fst
      before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < r.lo) :
    RangeSetBlaze :=
  insertAtStrictStartGap s r
    (nonstrict_start_gap_implies_strict_start_gap s.ranges r.lo s.canonical hgap_le)

/-- The extend-predecessor helper has two proof clients: its executable
wrapper needs the ordering invariant, while the correctness projection used
by the final theorem needs exact set semantics. This specification derives
the split,
predecessor decomposition, and predecessor-to-suffix boundary once, then
exposes both guarantees as projections. -/
private lemma extend_predecessor_preserves_order_and_union
    (s : RangeSetBlaze) (r : IntRange)
    (before after : List NR) (prev : NR)
    (hDecomp :
      (List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges
        = (before, after)))
    (hLast : List.getLast? before = some prev)
    (hNoGap : ¬ (prev.val.hi + 1 < r.lo))
    (hExtend : prev.val.hi < r.hi) :
    let init := before.dropLast
    let extendedHi := max prev.val.hi r.hi
    let extended := mkNR prev.val.lo extendedHi (by
      exact le_trans prev.property (le_max_left _ _))
    let res := deleteExtraNRs_loop extended after
    let newRanges := init ++ res.fst :: res.snd
    List.Pairwise NR.before newRanges ∧
      rangesToSet newRanges = s.toSet ∪
        (mkNR r.lo r.hi (by
          omega)).val.toSet := by
  intro init extendedHi extended res newRanges
  have hne : before ≠ [] := by
    intro h
    simp [h] at hLast
  let p := fun nr : NR => decide (nr.val.lo ≤ r.lo)
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
  have hcanonicalDecomp : List.Pairwise NR.before (before ++ after) := by
    rw [← h_s_decomp]
    exact s.canonical
  have hpw_before : List.Pairwise NR.before before :=
    (List.pairwise_append.mp hcanonicalDecomp).1
  have hpw_after : List.Pairwise NR.before after :=
    (List.pairwise_append.mp hcanonicalDecomp).2.1
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
    exact NR.pairwise_before_prefix_last_suffix hcanonicalDecomp hLast nr hmem
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
      (List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges).fst.getLast? =
        some prev := by
    rw [hDecomp]
    exact hLast
  have h_prev_lo_le_start : prev.val.lo ≤ r.lo :=
    (start_split_predecessor_le_and_mem s.ranges r.lo prev h_last_span).1
  have h_start_stop : r.lo ≤ r.hi := by
    have h_start : r.lo ≤ prev.val.hi + 1 := le_of_not_gt hNoGap
    omega
  let inserted := mkNR r.lo r.hi h_start_stop
  have h_extended_toSet : extended.val.toSet = prev.val.toSet ∪ inserted.val.toSet := by
    have horder : prev.val.lo ≤ inserted.val.lo := by
      simpa [inserted, mkNR] using h_prev_lo_le_start
    have htouch : ¬ (prev.val.hi + 1 < inserted.val.lo) := by
      simpa [inserted, mkNR] using hNoGap
    simpa [extended, extendedHi, inserted, mkNR] using
      (mergeForward_toSet prev inserted horder htouch)
  have h_s_toSet : s.toSet = rangesToSet init ∪ prev.val.toSet ∪ rangesToSet after := by
    have h_s_ranges : s.toSet = rangesToSet s.ranges := by
      unfold RangeSetBlaze.toSet
      rfl
    rw [h_s_ranges, h_s_decomp, h_before_decomp]
    rw [rangesToSet_append, rangesToSet_append]
    simp only [rangesToSet_cons, rangesToSet_nil, Set.union_empty]
  constructor
  · exact hpw_newRanges
  · calc
      rangesToSet newRanges
        = rangesToSet (init ++ res.fst :: res.snd) := rfl
      _ = rangesToSet init ∪ rangesToSet (res.fst :: res.snd) :=
        rangesToSet_append init (res.fst :: res.snd)
      _ = rangesToSet init ∪ (extended.val.toSet ∪ rangesToSet after) := by
        rw [h_loop_props.2.2]
      _ = rangesToSet init ∪ ((prev.val.toSet ∪ inserted.val.toSet) ∪ rangesToSet after) := by
        rw [h_extended_toSet]
      _ = (rangesToSet init ∪ prev.val.toSet ∪ rangesToSet after) ∪ inserted.val.toSet := by
        ac_rfl
      _ = s.toSet ∪ inserted.val.toSet := by rw [h_s_toSet]

/-- Extend when `prev` touches/overlaps `r` and `r.hi > prev.hi`.
    We replace `prev` by `extended := [prev.lo, max prev.hi r.hi]` and
    run the same loop on the tail. -/
private def extendPredecessor
    (s : RangeSetBlaze) (r : IntRange)
    (before after : List NR) (prev : NR)
    (hDecomp :
      (List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges
        = (before, after)))
    (hLast : List.getLast? before = some prev)
    (_hNoGap : ¬ (prev.val.hi + 1 < r.lo))
    (_hExtend : prev.val.hi < r.hi) :
    RangeSetBlaze := by
  let init := before.dropLast
  let extendedHi := max prev.val.hi r.hi
  have hExtendedValid : prev.val.lo ≤ extendedHi := by
    exact le_trans prev.property (le_max_left _ _)
  let extended := mkNR prev.val.lo extendedHi hExtendedValid
  let res := deleteExtraNRs_loop extended after
  let newRanges := init ++ res.fst :: res.snd
  have hspec := extend_predecessor_preserves_order_and_union s r before after prev
    hDecomp hLast _hNoGap _hExtend
  exact fromNRs newRanges hspec.1
/-- Production-shaped insertion: handle empty, separated, covered, and
extend-and-merge cases after locating the non-strict predecessor. -/
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
        insertAtNonstrictStartGap s r hgap
    | some prev =>
        if hgap : decide (prev.val.hi + 1 < start) then
          -- prev has a gap, pass it along
          have hgap_proof : before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < start := by
            right
            have hne : before ≠ [] := by
              intro h_empty
              simp [h_empty] at h_last
            use hne
            rw [List.getLast_of_getLast?_eq_some h_last]
            exact of_decide_eq_true hgap
          insertAtNonstrictStartGap s r hgap_proof
        else
          -- No gap case: prev.hi + 1 ≥ start
          -- Check if r extends beyond prev
          if _hextend : stop <= prev.val.hi then
            -- r is fully covered by prev, return unchanged
            s
          else
            -- r extends beyond prev: extend it and merge forward
            have hDecomp : List.span (fun nr => decide (nr.val.lo ≤ start)) s.ranges = (before, after) := rfl
            have hNoGap : ¬ (prev.val.hi + 1 < start) := by
              intro h_gap
              have : decide (prev.val.hi + 1 < start) = true := decide_eq_true h_gap
              rw [this] at hgap
              simp at hgap
            have hExtend : prev.val.hi < stop := not_le.mp _hextend
            extendPredecessor s r before after prev hDecomp h_last hNoGap hExtend

/-- Correctness of insertion across the strict start boundary. -/
private theorem insertAtStrictStartGap_toSet
    (s : RangeSetBlaze) (r : IntRange)
    (hgap_lt :
      let split := List.span (fun nr => decide (nr.val.lo < r.lo)) s.ranges
      let before := split.fst
      before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < r.lo) :
  (insertAtStrictStartGap s r hgap_lt).toSet = s.toSet ∪ r.toSet := by
  by_cases hempty : r.hi < r.lo
  · simp [insertAtStrictStartGap, hempty, IntRange.toSet_eq_empty_of_hi_lt_lo hempty]
  · simpa [insertAtStrictStartGap, hempty, fromNRs, RangeSetBlaze.toSet, mkNR] using
      (internalAdd2NRs_preserves_order_and_union
        s.ranges r.lo r.hi (not_lt.mp hempty) s.canonical hgap_lt).2

/-- Correctness of insertion through the non-strict predecessor boundary. -/
private theorem insertAtNonstrictStartGap_toSet
    (s : RangeSetBlaze) (r : IntRange)
    (hgap_le :
      let split := List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges
      let before := split.fst
      before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < r.lo) :
  (insertAtNonstrictStartGap s r hgap_le).toSet = s.toSet ∪ r.toSet := by
  unfold insertAtNonstrictStartGap
  exact insertAtStrictStartGap_toSet s r _

/-- Set-correctness for the extend-prev branch. -/
private theorem extendPredecessor_toSet
    (s : RangeSetBlaze) (r : IntRange)
    (before after : List NR) (prev : NR)
    (hDecomp : List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges = (before, after))
    (hLast : List.getLast? before = some prev)
    (hNoGap : ¬ (prev.val.hi + 1 < r.lo))
    (hExtend : prev.val.hi < r.hi) :
    (extendPredecessor s r before after prev hDecomp hLast hNoGap hExtend).toSet
    = s.toSet ∪ r.toSet := by
  have hspec := extend_predecessor_preserves_order_and_union s r before after prev
    hDecomp hLast hNoGap hExtend
  have h_start_stop : r.lo ≤ r.hi := by
    have h_start : r.lo ≤ prev.val.hi + 1 := le_of_not_gt hNoGap
    omega
  have h_interval : (mkNR r.lo r.hi h_start_stop).val.toSet = r.toSet := by
    rfl
  unfold extendPredecessor
  simp only [fromNRs, RangeSetBlaze.toSet]
  change rangesToSet _ = s.toSet ∪ r.toSet
  simpa [h_interval] using hspec.2

/-- Algo C represents exactly the union of the old range set and the input
interval. The proof follows the same branch structure as `internalAddC`. -/
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
      -- none case: before = [], insert through the predecessor boundary
      exact insertAtNonstrictStartGap_toSet s r _
    case h_2 =>
      -- some prev case
      split
      case isTrue =>
        -- gap case: prev.hi + 1 < start, insert through the predecessor boundary
        exact insertAtNonstrictStartGap_toSet s r _
      case isFalse =>
        -- no gap case: check if covered or extend
        split
        case isTrue =>
          -- covered case: r.hi ≤ prev.hi, return s unchanged
          rename_i prev h_last h_no_gap h_covered
          have h_prev_props :=
            start_split_predecessor_le_and_mem s.ranges r.lo prev h_last
          have h_r_covered : r.toSet ⊆ s.toSet := by
            simpa [RangeSetBlaze.toSet] using
              toSet_subset_rangesToSet_of_mem_of_bounds
                h_prev_props.2 h_prev_props.1 h_covered
          show s.toSet = s.toSet ∪ r.toSet
          rw [Set.union_eq_self_of_subset_right h_r_covered]
        case isFalse =>
          -- extend case: prev.hi < r.hi, extend the predecessor
          rename_i prev h_last h_no_gap h_not_covered
          have h_extend : prev.val.hi < r.hi := not_le.mp h_not_covered
          exact extendPredecessor_toSet s r
            (List.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges)
            (List.dropWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges)
            prev (List.span_eq_takeWhile_dropWhile _ _)
            (by simpa only [List.span_eq_takeWhile_dropWhile] using h_last)
            h_no_gap h_extend

open Classical
open IntRange

end RangeSetBlaze
