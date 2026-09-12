import RangeSetBlaze.Basic

namespace RangeMapBlaze

open IntRange (NR)
open scoped IntRange.NR

/-!
## Algo A for range maps

This module implements the deliberately simple reference map overwrite. It
first removes the overwritten part of every old run, retaining a left and/or
right residual where appropriate, and inserts the new run between the two
ordered lists. It then normalizes that raw representation by coalescing
equal-valued touching neighbors.

The result is canonical and its partial-function view is exactly pointwise
`overwrite`. As elsewhere in the Lean map model, cached length is intentionally
not represented.
-/

private def leftResidual {Value : Type*} (start : Int) (run : Run Value) : Option (Run Value) :=
  if h : run.range.val.lo < start then
    some {
      range := ⟨⟨run.range.val.lo, min run.range.val.hi (start - 1)⟩, by
        change run.range.val.lo ≤ min run.range.val.hi (start - 1)
        exact le_min run.range.property (by omega)⟩
      value := run.value
    }
  else none

private def rightResidual {Value : Type*} (stop : Int) (run : Run Value) : Option (Run Value) :=
  if h : stop < run.range.val.hi then
    some {
      range := ⟨⟨max run.range.val.lo (stop + 1), run.range.val.hi⟩, by
        change max run.range.val.lo (stop + 1) ≤ run.range.val.hi
        exact max_le run.range.property (by omega)⟩
      value := run.value
    }
  else none

private def mergeTouchingRuns {Value : Type*} (left right : Run Value)
    (htouch : left.range.val.hi + 1 = right.range.val.lo) : Run Value :=
  {
    range := ⟨⟨left.range.val.lo, right.range.val.hi⟩,
      le_trans left.range.property (le_trans (by omega : left.range.val.hi ≤ right.range.val.lo) right.range.property)⟩
    value := left.value
  }

/-- Coalesce adjacent equal-valued touching runs in an ordered, nonoverlapping
run list. -/
private def coalesceRuns {Value : Type*} [DecidableEq Value] : List (Run Value) → List (Run Value)
  | [] => []
  | run :: rest =>
      match coalesceRuns rest with
      | [] => [run]
      | next :: tail =>
          if htouch : run.value = next.value ∧
              run.range.val.hi + 1 = next.range.val.lo then
            mergeTouchingRuns run next htouch.2 :: tail
          else
            run :: next :: tail
termination_by runs => runs.length

/-- The raw overwrite representation: all surviving residuals plus the new run. -/
private def trimAndInsert {Value : Type*}
    (runs : List (Run Value)) (input : IntRange) (value : Value)
    (h : input.lo ≤ input.hi) : List (Run Value) :=
  runs.filterMap (leftResidual input.lo) ++
    { range := ⟨input, h⟩, value := value } ::
    runs.filterMap (rightResidual input.hi)

private lemma leftResiduals_toFunction {Value : Type*}
    (runs : List (Run Value)) (start key : Int) :
    runsToFunction (runs.filterMap (leftResidual start)) key =
      if key < start then runsToFunction runs key else none := by
  induction runs with
  | nil => simp
  | cons run rest ih =>
      by_cases hlo : run.range.val.lo < start
      · by_cases hkey : key < start
        · by_cases hold : run.range.val.lo ≤ key ∧ key ≤ run.range.val.hi
          · have hpiece : run.range.val.lo ≤ key ∧
                key ≤ min run.range.val.hi (start - 1) :=
              ⟨hold.1, le_min hold.2 (by omega)⟩
            simp [leftResidual, hlo, hkey, hold, hpiece]
          · have hpiece : ¬ (run.range.val.lo ≤ key ∧
                key ≤ min run.range.val.hi (start - 1)) := by
              omega
            simp [leftResidual, hlo, ih, hkey, hold]
            intro hloKey hkeyHi _
            exact (hold ⟨hloKey, hkeyHi⟩).elim
        · have hpiece : ¬ (run.range.val.lo ≤ key ∧
              key ≤ min run.range.val.hi (start - 1)) := by
            omega
          simp [leftResidual, hlo, ih, hkey]
          omega
      · by_cases hkey : key < start
        · have hold : ¬ (run.range.val.lo ≤ key ∧ key ≤ run.range.val.hi) := by
            omega
          simp [leftResidual, hlo, ih, hkey, hold]
        · simp [leftResidual, hlo, ih, hkey]

private lemma rightResiduals_toFunction {Value : Type*}
    (runs : List (Run Value)) (stop key : Int) :
    runsToFunction (runs.filterMap (rightResidual stop)) key =
      if stop < key then runsToFunction runs key else none := by
  induction runs with
  | nil => simp
  | cons run rest ih =>
      by_cases hhi : stop < run.range.val.hi
      · by_cases hkey : stop < key
        · by_cases hold : run.range.val.lo ≤ key ∧ key ≤ run.range.val.hi
          · have hpiece : max run.range.val.lo (stop + 1) ≤ key ∧
                key ≤ run.range.val.hi :=
              ⟨max_le hold.1 (by omega), hold.2⟩
            simp [rightResidual, hhi, hkey, hold, hpiece]
          · have hpiece : ¬ (max run.range.val.lo (stop + 1) ≤ key ∧
                key ≤ run.range.val.hi) := by
              omega
            simp [rightResidual, hhi, ih, hkey, hold]
            intro hloKey _ hkeyHi
            exact (hold ⟨hloKey, hkeyHi⟩).elim
        · have hpiece : ¬ (max run.range.val.lo (stop + 1) ≤ key ∧
              key ≤ run.range.val.hi) := by
            omega
          simp [rightResidual, hhi, ih, hkey]
          omega
      · by_cases hkey : stop < key
        · have hold : ¬ (run.range.val.lo ≤ key ∧ key ≤ run.range.val.hi) := by
            omega
          simp [rightResidual, hhi, ih, hkey, hold]
        · simp [rightResidual, hhi, ih, hkey]

private lemma trimAndInsert_toFunction {Value : Type*}
    (runs : List (Run Value)) (input : IntRange) (value : Value)
    (h : input.lo ≤ input.hi) :
    runsToFunction (trimAndInsert runs input value h) =
      overwrite (runsToFunction runs) input value := by
  funext key
  simp only [trimAndInsert, runsToFunction_append,
    leftResiduals_toFunction, rightResiduals_toFunction,
    runsToFunction_cons]
  by_cases hleft : key < input.lo
  · have hnot : ¬ (input.lo ≤ key ∧ key ≤ input.hi) := by omega
    have hright : ¬ input.hi < key := by omega
    simp [hleft, hright, hnot, overwrite]
    cases runsToFunction runs key <;> rfl
  · by_cases hright : input.hi < key
    · have hnot : ¬ (input.lo ≤ key ∧ key ≤ input.hi) := by omega
      simp [hleft, hright, hnot, overwrite]
    · have hin : input.lo ≤ key ∧ key ≤ input.hi := by omega
      simp [hleft, hin, overwrite]

private lemma mergeTouchingRuns_toFunction {Value : Type*}
    (left right : Run Value) (tail : List (Run Value))
    (htouch : left.range.val.hi + 1 = right.range.val.lo)
    (hvalue : left.value = right.value) :
    runsToFunction (mergeTouchingRuns left right htouch :: tail) =
      runsToFunction (left :: right :: tail) := by
  funext key
  have hleftNonempty := left.range.property
  have hrightNonempty := right.range.property
  change left.range.val.lo ≤ left.range.val.hi at hleftNonempty
  change right.range.val.lo ≤ right.range.val.hi at hrightNonempty
  simp only [runsToFunction_cons]
  by_cases hleft : left.range.val.lo ≤ key ∧ key ≤ left.range.val.hi
  · have hmerged : left.range.val.lo ≤ key ∧ key ≤ right.range.val.hi :=
      ⟨hleft.1, le_trans hleft.2 (by omega)⟩
    simp [mergeTouchingRuns, hleft, hmerged]
  · by_cases hright : right.range.val.lo ≤ key ∧ key ≤ right.range.val.hi
    · have hmerged : left.range.val.lo ≤ key ∧ key ≤ right.range.val.hi :=
        ⟨by omega, hright.2⟩
      simp [mergeTouchingRuns, hright, hmerged, hvalue]
    · have hmerged : ¬ (left.range.val.lo ≤ key ∧ key ≤ right.range.val.hi) := by
        intro h
        by_cases hk : key ≤ left.range.val.hi
        · exact hleft ⟨h.1, hk⟩
        · exact hright ⟨by omega, h.2⟩
      simp [mergeTouchingRuns, hleft, hright, hmerged]

private lemma coalesceRuns_head_lo {Value : Type*} [DecidableEq Value]
    (first : Run Value) (rest : List (Run Value))
    {head : Run Value} {tail : List (Run Value)}
    (hresult : coalesceRuns (first :: rest) = head :: tail) :
    head.range.val.lo = first.range.val.lo := by
  unfold coalesceRuns at hresult
  cases hrest : coalesceRuns rest with
  | nil =>
      simpa [hrest] using
        (congrArg (fun xs => xs.head?.map (fun r => r.range.val.lo)) hresult).symm
  | cons next remainder =>
      by_cases htouch : first.value = next.value ∧
          first.range.val.hi + 1 = next.range.val.lo
      · simp [hrest, htouch, mergeTouchingRuns] at hresult
        exact (congrArg (fun r : Run Value => r.range.val.lo) hresult.1).symm
      · simp [hrest, htouch] at hresult
        exact (congrArg (fun r : Run Value => r.range.val.lo) hresult.1).symm

private lemma Run.before_of_disjointBefore_of_not_coalescible
    {Value : Type*} {left right : Run Value}
    (hdisjoint : Run.disjointBefore left right)
    (hnot : ¬ (left.value = right.value ∧
      left.range.val.hi + 1 = right.range.val.lo)) :
    Run.before left right := by
  change left.range.val.hi < right.range.val.lo at hdisjoint
  refine ⟨hdisjoint, ?_⟩
  intro hvalue
  unfold IntRange.NR.before
  have hne : left.range.val.hi + 1 ≠ right.range.val.lo :=
    fun heq => hnot ⟨hvalue, heq⟩
  omega

private lemma mergeTouchingRuns_before {Value : Type*}
    {left next later : Run Value}
    (htouch : left.range.val.hi + 1 = next.range.val.lo)
    (hvalue : left.value = next.value)
    (hbefore : Run.before next later) :
    Run.before (mergeTouchingRuns left next htouch) later := by
  constructor
  · simpa [mergeTouchingRuns, Run.disjointBefore] using hbefore.1
  · intro heq
    apply hbefore.2
    simpa [mergeTouchingRuns, hvalue] using heq

/-- Coalescing has one contract: on ordered, nonoverlapping input it produces a
canonical representation without changing the represented partial function. -/
private lemma coalesceRuns_spec {Value : Type*} [DecidableEq Value]
    (runs : List (Run Value))
    (hordered : List.Pairwise Run.disjointBefore runs) :
    Canonical (coalesceRuns runs) ∧
      runsToFunction (coalesceRuns runs) = runsToFunction runs := by
  induction runs with
  | nil => simp [coalesceRuns, Canonical]
  | cons run rest ih =>
      have hspecRest := ih hordered.tail
      have hcanonicalRest := hspecRest.1
      have hfunctionRest := hspecRest.2
      cases hcoal : coalesceRuns rest with
      | nil =>
          constructor
          · simp [coalesceRuns, hcoal, Canonical]
          · funext key
            have hnone : runsToFunction rest key = none := by
              rw [← hfunctionRest, hcoal]
              rfl
            simp [coalesceRuns, hcoal, hnone]
      | cons next tail =>
          have hnextTail : List.Pairwise Run.before (next :: tail) := by
            simpa [Canonical, hcoal] using hcanonicalRest
          cases rest with
          | nil => simp [coalesceRuns] at hcoal
          | cons original remainder =>
              have hlo : next.range.val.lo = original.range.val.lo :=
                coalesceRuns_head_lo original remainder hcoal
              have hrunOriginal : Run.disjointBefore run original :=
                List.rel_of_pairwise_cons hordered (by simp)
              have hrunNext : Run.disjointBefore run next := by
                unfold Run.disjointBefore at *
                omega
              have htailFunction : runsToFunction (next :: tail) =
                  runsToFunction (original :: remainder) := by
                rw [← hcoal]
                exact hfunctionRest
              by_cases htouch : run.value = next.value ∧
                  run.range.val.hi + 1 = next.range.val.lo
              · have hresult : coalesceRuns (run :: original :: remainder) =
                    mergeTouchingRuns run next htouch.2 :: tail := by
                    simp [coalesceRuns, hcoal, htouch]
                constructor
                · rw [hresult]
                  apply List.pairwise_cons.mpr
                  constructor
                  · intro later hlater
                    exact mergeTouchingRuns_before htouch.2 htouch.1
                      (List.rel_of_pairwise_cons hnextTail hlater)
                  · exact hnextTail.tail
                · rw [hresult]
                  rw [mergeTouchingRuns_toFunction run next tail htouch.2 htouch.1]
                  funext key
                  simp only [runsToFunction_cons]
                  split
                  · rfl
                  · simpa only [runsToFunction_cons] using congrFun htailFunction key
              · have hresult : coalesceRuns (run :: original :: remainder) =
                    run :: next :: tail := by
                    simp [coalesceRuns, hcoal, htouch]
                constructor
                · rw [hresult]
                  apply List.pairwise_cons.mpr
                  constructor
                  · intro later hlater
                    rcases List.mem_cons.mp hlater with rfl | hlater
                    · exact Run.before_of_disjointBefore_of_not_coalescible
                        hrunNext htouch
                    · exact Run.before_trans
                        (Run.before_of_disjointBefore_of_not_coalescible hrunNext htouch)
                        (List.rel_of_pairwise_cons hnextTail hlater)
                  · exact hnextTail
                · rw [hresult]
                  funext key
                  simp only [runsToFunction_cons]
                  split
                  · rfl
                  · simpa only [runsToFunction_cons] using congrFun htailFunction key

private lemma leftResidual_properties {Value : Type*}
    {start : Int} {run output : Run Value}
    (houtput : leftResidual start run = some output) :
    output.range.val.lo = run.range.val.lo ∧
      output.range.val.hi ≤ run.range.val.hi ∧
      output.range.val.hi < start ∧
      output.value = run.value := by
  unfold leftResidual at houtput
  split at houtput
  · simp only [Option.some.injEq] at houtput
    subst output
    refine ⟨rfl, min_le_left _ _, ?_, rfl⟩
    exact lt_of_le_of_lt (min_le_right _ _) (by omega)
  · contradiction

private lemma rightResidual_properties {Value : Type*}
    {stop : Int} {run output : Run Value}
    (houtput : rightResidual stop run = some output) :
    run.range.val.lo ≤ output.range.val.lo ∧
      stop < output.range.val.lo ∧
      output.range.val.hi = run.range.val.hi ∧
      output.value = run.value := by
  unfold rightResidual at houtput
  split at houtput
  · simp only [Option.some.injEq] at houtput
    subst output
    refine ⟨le_max_left _ _, ?_, rfl, rfl⟩
    exact lt_of_lt_of_le (by omega) (le_max_right _ _)
  · contradiction

private lemma leftResiduals_pairwise {Value : Type*}
    (runs : List (Run Value)) (start : Int)
    (hordered : List.Pairwise Run.disjointBefore runs) :
    List.Pairwise Run.disjointBefore (runs.filterMap (leftResidual start)) := by
  apply hordered.filterMap (leftResidual start)
  intro left right hbefore left' hleft right' hright
  have pleft := leftResidual_properties hleft
  have pright := leftResidual_properties hright
  unfold Run.disjointBefore
  exact lt_of_le_of_lt pleft.2.1 (hbefore.trans_eq pright.1.symm)

private lemma rightResiduals_pairwise {Value : Type*}
    (runs : List (Run Value)) (stop : Int)
    (hordered : List.Pairwise Run.disjointBefore runs) :
    List.Pairwise Run.disjointBefore (runs.filterMap (rightResidual stop)) := by
  apply hordered.filterMap (rightResidual stop)
  intro left right hbefore left' hleft right' hright
  have pleft := rightResidual_properties hleft
  have pright := rightResidual_properties hright
  unfold Run.disjointBefore
  exact lt_of_eq_of_lt pleft.2.2.1 (hbefore.trans_le pright.1)

private lemma leftResidual_mem_ends_before {Value : Type*}
    {runs : List (Run Value)} {start : Int} {output : Run Value}
    (hmem : output ∈ runs.filterMap (leftResidual start)) :
    output.range.val.hi < start := by
  rcases List.mem_filterMap.mp hmem with ⟨run, _, hrun⟩
  exact (leftResidual_properties hrun).2.2.1

private lemma rightResidual_mem_starts_after {Value : Type*}
    {runs : List (Run Value)} {stop : Int} {output : Run Value}
    (hmem : output ∈ runs.filterMap (rightResidual stop)) :
    stop < output.range.val.lo := by
  rcases List.mem_filterMap.mp hmem with ⟨run, _, hrun⟩
  exact (rightResidual_properties hrun).2.1

private lemma trimAndInsert_pairwise {Value : Type*}
    (runs : List (Run Value)) (input : IntRange) (value : Value)
    (hnonempty : input.lo ≤ input.hi)
    (hordered : List.Pairwise Run.disjointBefore runs) :
    List.Pairwise Run.disjointBefore
      (trimAndInsert runs input value hnonempty) := by
  let left := runs.filterMap (leftResidual input.lo)
  let right := runs.filterMap (rightResidual input.hi)
  let inserted : Run Value := { range := ⟨input, hnonempty⟩, value := value }
  have hleft : List.Pairwise Run.disjointBefore left :=
    leftResiduals_pairwise runs input.lo hordered
  have hright : List.Pairwise Run.disjointBefore right :=
    rightResiduals_pairwise runs input.hi hordered
  have hinsertedRight : ∀ candidate ∈ right,
      Run.disjointBefore inserted candidate := by
    intro candidate hcandidate
    unfold Run.disjointBefore inserted
    exact rightResidual_mem_starts_after hcandidate
  have hleftInsertedRight : ∀ candidate ∈ left, ∀ following ∈ inserted :: right,
      Run.disjointBefore candidate following := by
    intro candidate hcandidate following hfollowing
    have hcand := leftResidual_mem_ends_before hcandidate
    rcases List.mem_cons.mp hfollowing with rfl | hfollowing
    · exact hcand
    · unfold Run.disjointBefore
      have hfollow := rightResidual_mem_starts_after hfollowing
      omega
  unfold trimAndInsert
  change List.Pairwise Run.disjointBefore (left ++ inserted :: right)
  apply List.pairwise_append.mpr
  exact ⟨hleft, List.pairwise_cons.mpr ⟨hinsertedRight, hright⟩,
    hleftInsertedRight⟩

/-- A simple reference RangeMap overwrite: trim old runs, insert the new run,
then coalesce equal-valued touching neighbors. -/
def internalAddAMap {Value : Type*} [DecidableEq Value]
    (map : RangeMapBlaze Value) (input : IntRange) (value : Value) : RangeMapBlaze Value := by
  if h : input.hi < input.lo then
    exact map
  else
    have hnonempty : input.lo ≤ input.hi := by omega
    have hordered : List.Pairwise Run.disjointBefore map.runs :=
      map.canonical.imp fun hbefore => hbefore.1
    let runs := coalesceRuns (trimAndInsert map.runs input value hnonempty)
    refine ⟨runs, ?_⟩
    exact (coalesceRuns_spec _
      (trimAndInsert_pairwise map.runs input value hnonempty hordered)).1

/-- Algo A has exactly the pointwise semantics of overwriting the input
interval with the supplied value. -/
theorem internalAddAMap_toFunction {Value : Type*} [DecidableEq Value]
    (map : RangeMapBlaze Value) (input : IntRange) (value : Value) :
    (internalAddAMap map input value).toFunction = overwrite map.toFunction input value := by
  unfold internalAddAMap
  split <;> rename_i h
  · exact (overwrite_eq_of_hi_lt_lo map.toFunction input value h).symm
  · dsimp only [toFunction]
    have hordered : List.Pairwise Run.disjointBefore map.runs :=
      map.canonical.imp fun hbefore => hbefore.1
    rw [(coalesceRuns_spec _
      (trimAndInsert_pairwise map.runs input value (by omega) hordered)).2]
    apply trimAndInsert_toFunction

end RangeMapBlaze
