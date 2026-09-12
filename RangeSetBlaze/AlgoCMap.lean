import RangeSetBlaze.Basic

namespace RangeMapBlaze

open IntRange (NR)

/-!
## Production-shaped range-map insertion

This module models the proof-relevant part of the production Rust insertion
path independently of `BTreeMap` cursors.  A strict lower-bound split locates
the predecessor, the predecessor is either retained, merged, or trimmed, and a
forward scan removes overwritten runs until the first unaffected run.  Equal
valued touching runs are merged during that same scan.

The model deliberately omits cursor movement, mutation order, cached-length
updates, and bounded-integer overflow guards.  Lean's endpoint type is `Int`,
so successor and predecessor arithmetic is total.
-/

/-- A run with the same lower endpoint and value as `left`, extended through
the upper endpoint of `right`. -/
private def mergeForward {Value : Type*} (left right : Run Value) : Run Value :=
  {
    range := ⟨⟨left.range.val.lo, max left.range.val.hi right.range.val.hi⟩,
      left.range.property.trans (le_max_left _ _)⟩
    value := left.value
  }

/-- The part of `run` strictly to the right of `stop`. -/
private def rightResidualAfter {Value : Type*}
    (stop : Int) (run : Run Value) (h : stop < run.range.val.hi) : Run Value :=
  {
    range := ⟨⟨stop + 1, run.range.val.hi⟩, by
      change stop + 1 ≤ run.range.val.hi
      omega⟩
    value := run.value
  }

/-- The part of a predecessor strictly to the left of `start`. -/
private def leftResidualBefore {Value : Type*}
    (start : Int) (run : Run Value) (h : run.range.val.lo < start) : Run Value :=
  {
    range := ⟨⟨run.range.val.lo, start - 1⟩, by
      change run.range.val.lo ≤ start - 1
      omega⟩
    value := run.value
  }

/-- Scan the unprocessed suffix after a pending inserted run.

Equal-valued touching or overlapping runs extend `pending`; differently
valued overlapping runs are deleted, except that a final overhanging run leaves
one right residual.  The scan stops at the first run not affected by either
overwrite or equal-value canonicalization. -/
private def scanForward {Value : Type*} [DecidableEq Value]
    (pending : Run Value) : List (Run Value) → List (Run Value)
  | [] => [pending]
  | next :: rest =>
      if next.range.val.lo = pending.range.val.lo ∧
          pending.value = next.value ∧
          pending.range.val.hi ≤ next.range.val.hi then
        next :: rest
      else
        if _hsame : pending.value = next.value then
          if next.range.val.lo ≤ pending.range.val.hi + 1 then
            scanForward (mergeForward pending next) rest
          else
            pending :: next :: rest
        else if _hoverlap : next.range.val.lo ≤ pending.range.val.hi then
          if hextends : pending.range.val.hi < next.range.val.hi then
            pending :: rightResidualAfter pending.range.val.hi next hextends :: rest
          else
            scanForward pending rest
        else
          pending :: next :: rest
termination_by suffix => suffix.length

/-- Merging equal-valued touching runs preserves their first-match function. -/
private lemma mergeForward_toFunction {Value : Type*}
    (pending next : Run Value) (rest : List (Run Value))
    (hlower : pending.range.val.lo ≤ next.range.val.lo)
    (htouch : next.range.val.lo ≤ pending.range.val.hi + 1)
    (hsame : pending.value = next.value) :
    runsToFunction (mergeForward pending next :: rest) =
      runsToFunction (pending :: next :: rest) := by
  funext key
  simp only [runsToFunction_cons]
  by_cases hpending : pending.range.val.lo ≤ key ∧ key ≤ pending.range.val.hi
  · have hmerged : pending.range.val.lo ≤ key ∧
        key ≤ max pending.range.val.hi next.range.val.hi :=
      ⟨hpending.1, hpending.2.trans (le_max_left _ _)⟩
    simp [mergeForward, hpending, hmerged]
  · by_cases hnext : next.range.val.lo ≤ key ∧ key ≤ next.range.val.hi
    · have hmerged : pending.range.val.lo ≤ key ∧
          key ≤ max pending.range.val.hi next.range.val.hi :=
        ⟨hlower.trans hnext.1, hnext.2.trans (le_max_right _ _)⟩
      simp [mergeForward, hnext, hmerged, hsame]
    · have hmerged : ¬ (pending.range.val.lo ≤ key ∧
          key ≤ max pending.range.val.hi next.range.val.hi) := by
        intro h
        rcases (le_max_iff.mp h.2) with hhi | hhi
        · exact hpending ⟨h.1, hhi⟩
        · by_cases hk : key ≤ pending.range.val.hi
          · exact hpending ⟨h.1, hk⟩
          · exact hnext ⟨by omega, hhi⟩
      change (if pending.range.val.lo ≤ key ∧
          key ≤ max pending.range.val.hi next.range.val.hi then
          some pending.value else runsToFunction rest key) = _
      rw [if_neg hmerged, if_neg hpending, if_neg hnext]

/-- A same-valued run with the pending start and at least its end already
represents the pending insertion. -/
private lemma sameValueExactCover_toFunction {Value : Type*}
    (pending next : Run Value) (rest : List (Run Value))
    (hlo : next.range.val.lo = pending.range.val.lo)
    (hsame : pending.value = next.value)
    (hhi : pending.range.val.hi ≤ next.range.val.hi) :
    runsToFunction (next :: rest) =
      runsToFunction (pending :: next :: rest) := by
  funext key
  simp only [runsToFunction_cons]
  by_cases hpending : pending.range.val.lo ≤ key ∧ key ≤ pending.range.val.hi
  · have hnext : next.range.val.lo ≤ key ∧ key ≤ next.range.val.hi :=
      ⟨hlo.trans_le hpending.1, hpending.2.trans hhi⟩
    simp [hpending, hnext, hsame]
  · simp [hpending]

/-- A later run fully covered by `pending` can be deleted without changing
first-match semantics. -/
private lemma coveredRunDeletion_toFunction {Value : Type*}
    (pending next : Run Value) (rest : List (Run Value))
    (hlower : pending.range.val.lo ≤ next.range.val.lo)
    (hhi : next.range.val.hi ≤ pending.range.val.hi) :
    runsToFunction (pending :: rest) =
      runsToFunction (pending :: next :: rest) := by
  funext key
  simp only [runsToFunction_cons]
  by_cases hpending : pending.range.val.lo ≤ key ∧ key ≤ pending.range.val.hi
  · simp [hpending]
  · have hnext : ¬ (next.range.val.lo ≤ key ∧ key ≤ next.range.val.hi) := by
      omega
    simp [hpending, hnext]

/-- Replacing the overlapping part of `next` by its right residual preserves
the function of `pending :: next :: rest`. -/
private lemma rightResidualSplit_toFunction {Value : Type*}
    (pending next : Run Value) (rest : List (Run Value))
    (hlower : pending.range.val.lo ≤ next.range.val.lo)
    (hoverlap : next.range.val.lo ≤ pending.range.val.hi)
    (hextends : pending.range.val.hi < next.range.val.hi) :
    runsToFunction
        (pending :: rightResidualAfter pending.range.val.hi next hextends :: rest) =
      runsToFunction (pending :: next :: rest) := by
  funext key
  simp only [runsToFunction_cons]
  by_cases hpending : pending.range.val.lo ≤ key ∧ key ≤ pending.range.val.hi
  · simp [hpending]
  · have hequiv :
        (pending.range.val.hi + 1 ≤ key ∧ key ≤ next.range.val.hi) ↔
          (next.range.val.lo ≤ key ∧ key ≤ next.range.val.hi) := by
      constructor <;> intro h
      · exact ⟨by omega, h.2⟩
      · exact ⟨by omega, h.2⟩
    simp [rightResidualAfter, hpending, hequiv]

/-- The forward scan's single recursive contract: it restores canonical shape
and preserves the first-match function of `pending :: suffix`. -/
private lemma scanForward_spec {Value : Type*} [DecidableEq Value]
    (pending : Run Value) (suffix : List (Run Value))
    (hcanonical : Canonical suffix)
    (hlower : ∀ run ∈ suffix, pending.range.val.lo ≤ run.range.val.lo) :
    Canonical (scanForward pending suffix) ∧
      runsToFunction (scanForward pending suffix) =
        runsToFunction (pending :: suffix) := by
  induction suffix generalizing pending with
  | nil => simp [scanForward, Canonical]
  | cons next rest ih =>
      have hlowerNext : pending.range.val.lo ≤ next.range.val.lo :=
        hlower next (by simp)
      have hlowerRest : ∀ run ∈ rest,
          pending.range.val.lo ≤ run.range.val.lo := by
        intro run hrun
        exact hlower run (by simp [hrun])
      have hcanonicalRest : Canonical rest := hcanonical.tail
      have hnextBefore : ∀ run ∈ rest, Run.before next run :=
        fun run hrun => List.rel_of_pairwise_cons hcanonical hrun
      unfold scanForward
      by_cases hexact : next.range.val.lo = pending.range.val.lo ∧
          pending.value = next.value ∧
          pending.range.val.hi ≤ next.range.val.hi
      · simp only [hexact]
        exact ⟨hcanonical,
          sameValueExactCover_toFunction pending next rest
            hexact.1 hexact.2.1 hexact.2.2⟩
      · simp only [hexact]
        by_cases hsame : pending.value = next.value
        · simp only [hsame, ↓reduceDIte]
          by_cases htouch : next.range.val.lo ≤ pending.range.val.hi + 1
          · simp only [htouch]
            have hlowerMerged : ∀ run ∈ rest,
                (mergeForward pending next).range.val.lo ≤ run.range.val.lo := by
              simpa [mergeForward] using hlowerRest
            have hspec := ih (mergeForward pending next) hcanonicalRest hlowerMerged
            refine ⟨hspec.1, ?_⟩
            exact hspec.2.trans
              (mergeForward_toFunction pending next rest hlowerNext htouch hsame)
          · simp only [htouch]
            have hgap : pending.range.val.hi + 1 < next.range.val.lo := by omega
            have hbeforeNext : Run.before pending next := by
              refine ⟨?_, ?_⟩
              · unfold Run.disjointBefore
                omega
              intro _
              simpa only [IntRange.NR.before] using hgap
            have hbeforeAll : ∀ run ∈ next :: rest, Run.before pending run := by
              intro run hrun
              rcases List.mem_cons.mp hrun with rfl | hrun
              · exact hbeforeNext
              · exact Run.before_trans hbeforeNext (hnextBefore run hrun)
            exact ⟨List.pairwise_cons.mpr ⟨hbeforeAll, hcanonical⟩, rfl⟩

        · simp only [hsame, ↓reduceDIte]
          by_cases hoverlap : next.range.val.lo ≤ pending.range.val.hi
          · simp only [hoverlap, ↓reduceDIte]
            by_cases hextends : pending.range.val.hi < next.range.val.hi
            · simp only [hextends, ↓reduceDIte]
              let residual := rightResidualAfter pending.range.val.hi next hextends
              have hpendingResidual : Run.before pending residual := by
                refine ⟨?_, ?_⟩
                · simp [residual, rightResidualAfter, Run.disjointBefore]
                · intro heq
                  have : pending.value = next.value := by
                    simpa [residual, rightResidualAfter] using heq
                  exact (hsame this).elim
              have hresidualAll : ∀ run ∈ rest, Run.before residual run := by
                intro run hrun
                have hnr := hnextBefore run hrun
                constructor
                · simpa [residual, rightResidualAfter, Run.disjointBefore] using hnr.1
                · intro heq
                  apply hnr.2
                  simpa [residual, rightResidualAfter] using heq
              have hresidualCanonical : Canonical (residual :: rest) :=
                List.pairwise_cons.mpr ⟨hresidualAll, hcanonicalRest⟩
              refine ⟨List.pairwise_cons.mpr ⟨?_, hresidualCanonical⟩, ?_⟩
              · intro run hrun
                rcases List.mem_cons.mp hrun with rfl | hrun
                · exact hpendingResidual
                · exact Run.before_trans hpendingResidual (hresidualAll run hrun)
              · exact rightResidualSplit_toFunction
                  pending next rest hlowerNext hoverlap hextends
            · simp only [hextends, ↓reduceDIte]
              have hspec := ih pending hcanonicalRest hlowerRest
              refine ⟨hspec.1, ?_⟩
              exact hspec.2.trans
                (coveredRunDeletion_toFunction pending next rest hlowerNext (by omega))
          · simp only [hoverlap, ↓reduceDIte]
            have hbeforeNext : Run.before pending next := by
              refine ⟨?_, ?_⟩
              · unfold Run.disjointBefore
                omega
              intro heq
              exact (hsame heq).elim
            have hbeforeAll : ∀ run ∈ next :: rest, Run.before pending run := by
              intro run hrun
              rcases List.mem_cons.mp hrun with rfl | hrun
              · exact hbeforeNext
              · exact Run.before_trans hbeforeNext (hnextBefore run hrun)
            exact ⟨List.pairwise_cons.mpr ⟨hbeforeAll, hcanonical⟩, rfl⟩

/-- A run already canonical before both the pending run and its suffix remains
before every run emitted by the forward scan. -/
private lemma scanForward_preserves_left_boundary {Value : Type*} [DecidableEq Value]
    (left pending : Run Value) (suffix : List (Run Value))
    (hpending : Run.before left pending)
    (hsuffix : ∀ run ∈ suffix, Run.before left run) :
    ∀ run ∈ scanForward pending suffix, Run.before left run := by
  induction suffix generalizing pending with
  | nil => simpa [scanForward] using hpending
  | cons next rest ih =>
      have hnext : Run.before left next := hsuffix next (by simp)
      have hrest : ∀ run ∈ rest, Run.before left run := by
        intro run hrun
        exact hsuffix run (by simp [hrun])
      unfold scanForward
      by_cases hexact : next.range.val.lo = pending.range.val.lo ∧
          pending.value = next.value ∧
          pending.range.val.hi ≤ next.range.val.hi
      · simpa [hexact] using hsuffix
      · simp only [hexact, if_false]
        by_cases hsame : pending.value = next.value
        · simp only [hsame, ↓reduceDIte]
          by_cases htouch : next.range.val.lo ≤ pending.range.val.hi + 1
          · simp only [htouch]
            apply ih (mergeForward pending next)
            · constructor
              · simpa [mergeForward, Run.disjointBefore] using hpending.1
              · intro hvalue
                apply hpending.2
                simpa [mergeForward] using hvalue
            · exact hrest
          · simpa [htouch] using
              (show ∀ run ∈ pending :: next :: rest, Run.before left run by
                intro run hrun
                rcases List.mem_cons.mp hrun with rfl | hrun
                · exact hpending
                · exact hsuffix run hrun)
        · simp only [hsame, ↓reduceDIte]
          by_cases hoverlap : next.range.val.lo ≤ pending.range.val.hi
          · simp only [hoverlap, ↓reduceDIte]
            by_cases hextends : pending.range.val.hi < next.range.val.hi
            · simp only [hextends, ↓reduceDIte]
              have hresidual : Run.before left
                  (rightResidualAfter pending.range.val.hi next hextends) := by
                constructor
                · change left.range.val.hi < pending.range.val.hi + 1
                  have hleftPending : left.range.val.hi < pending.range.val.lo :=
                    hpending.1
                  have hpendingNonempty : pending.range.val.lo ≤ pending.range.val.hi :=
                    pending.range.property
                  omega
                · intro hvalue
                  have hgap := hnext.2 (by simpa [rightResidualAfter] using hvalue)
                  unfold IntRange.NR.before at hgap ⊢
                  simp only [rightResidualAfter]
                  omega
              intro run hrun
              simp only [List.mem_cons] at hrun
              rcases hrun with rfl | rfl | hrun
              · exact hpending
              · exact hresidual
              · exact hrest run hrun
            · simp only [hextends]
              exact ih pending hpending hrest
          · simpa [hoverlap] using
              (show ∀ run ∈ pending :: next :: rest, Run.before left run by
                intro run hrun
                rcases List.mem_cons.mp hrun with rfl | hrun
                · exact hpending
                · exact hsuffix run hrun)

/-- Runs in the suffix of a strict start split begin at or after the split
point. -/
private lemma strictStartSuffix_lower_bound {Value : Type*}
    (runs : List (Run Value)) (start : Int) (hcanonical : Canonical runs) :
    ∀ run ∈ (List.span (fun candidate =>
      decide (candidate.range.val.lo < start)) runs).snd,
      start ≤ run.range.val.lo := by
  rw [List.span_eq_takeWhile_dropWhile]
  induction runs with
  | nil => simp
  | cons first rest ih =>
      by_cases hfirst : first.range.val.lo < start
      · rw [List.dropWhile_cons_of_pos (by simp [hfirst])]
        exact ih hcanonical.tail
      · rw [List.dropWhile_cons_of_neg (by simp [hfirst])]
        intro run hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact not_lt.mp hfirst
        · exact (not_lt.mp hfirst).trans
            (Run.before_lo_lt (List.rel_of_pairwise_cons hcanonical hmem)).le

/-- A suffix whose runs start at or after `start` has no value below `start`. -/
private lemma runsToFunction_eq_none_belowLowerBound {Value : Type*}
    (runs : List (Run Value)) (start key : Int)
    (hlower : ∀ run ∈ runs, start ≤ run.range.val.lo)
    (hkey : key < start) : runsToFunction runs key = none := by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
      have hrun := hlower run (by simp)
      have hnot : ¬ (run.range.val.lo ≤ key ∧ key ≤ run.range.val.hi) := by
        omega
      rw [runsToFunction_cons, if_neg hnot]
      exact ih (fun candidate hmem => hlower candidate (by simp [hmem]))

/-- Prepending an inserted run to a suffix beginning at its lower bound realizes
pointwise overwrite on that suffix. -/
private lemma insertedSuffix_toFunction {Value : Type*}
    (suffix : List (Run Value)) (input : IntRange) (value : Value)
    (hnonempty : input.lo ≤ input.hi)
    (hlower : ∀ run ∈ suffix, input.lo ≤ run.range.val.lo) :
    runsToFunction ({ range := ⟨input, hnonempty⟩, value := value } :: suffix) =
      overwrite (runsToFunction suffix) input value := by
  funext key
  simp only [runsToFunction_cons]
  by_cases hin : input.lo ≤ key ∧ key ≤ input.hi
  · simp [hin, overwrite]
  · by_cases hkey : key < input.lo
    · have hsuffix := runsToFunction_eq_none_belowLowerBound
        suffix input.lo key hlower hkey
      simp [hin, overwrite, hsuffix]
    · simp [hin, overwrite]

/-- An untouched prefix ending before the input can be prepended to a proved
tail overwrite. -/
private lemma prepend_left_of_overwrite {Value : Type*}
    (leftPrefix oldTail newTail : List (Run Value))
    (input : IntRange) (value : Value)
    (hleft : ∀ run ∈ leftPrefix, run.range.val.hi < input.lo)
    (htail : runsToFunction newTail =
      overwrite (runsToFunction oldTail) input value) :
    runsToFunction (leftPrefix ++ newTail) =
      overwrite (runsToFunction (leftPrefix ++ oldTail)) input value := by
  induction leftPrefix with
  | nil => simpa using htail
  | cons run rest ih =>
      have hrun := hleft run (by simp)
      have hrest : ∀ candidate ∈ rest,
          candidate.range.val.hi < input.lo := by
        intro candidate hmem
        exact hleft candidate (by simp [hmem])
      have ih' := ih hrest
      funext key
      simp only [List.cons_append, runsToFunction_cons]
      by_cases hcontains : run.range.val.lo ≤ key ∧ key ≤ run.range.val.hi
      · have hnotInput : ¬ (input.lo ≤ key ∧ key ≤ input.hi) := by
          omega
        simp [hcontains, overwrite, hnotInput]
      · simp only [hcontains, ↓reduceIte]
        rw [congrFun ih' key]
        simp [overwrite, hcontains]

/-- Trimming an overlapping differently-valued predecessor into residuals and
inserting the new run has exact overwrite semantics. -/
private lemma replacePredecessor_toFunction {Value : Type*}
    (prev : Run Value) (after : List (Run Value))
    (input : IntRange) (value : Value) (hnonempty : input.lo ≤ input.hi)
    (hstart : prev.range.val.lo < input.lo)
    (hoverlap : input.lo ≤ prev.range.val.hi) :
    let left := leftResidualBefore input.lo prev hstart
    let inserted : Run Value := { range := ⟨input, hnonempty⟩, value := value }
    let right := if h : input.hi < prev.range.val.hi then
      rightResidualAfter input.hi prev h :: after else after
    runsToFunction (left :: inserted :: right) =
      overwrite (runsToFunction (prev :: after)) input value := by
  dsimp only
  split <;> rename_i hextends
  · funext key
    simp only [runsToFunction_cons]
    by_cases hleft : prev.range.val.lo ≤ key ∧ key ≤ input.lo - 1
    · have hprev : prev.range.val.lo ≤ key ∧ key ≤ prev.range.val.hi := by
        omega
      have hinput : ¬ (input.lo ≤ key ∧ key ≤ input.hi) := by omega
      simp [leftResidualBefore, hleft, hprev, hinput, overwrite]
    · by_cases hinput : input.lo ≤ key ∧ key ≤ input.hi
      · simp [leftResidualBefore, hleft, hinput, overwrite]
      · have hequiv :
            (input.hi + 1 ≤ key ∧ key ≤ prev.range.val.hi) ↔
              (prev.range.val.lo ≤ key ∧ key ≤ prev.range.val.hi) := by
          constructor <;> intro h
          · exact ⟨by omega, h.2⟩
          · exact ⟨by omega, h.2⟩
        simp [leftResidualBefore, rightResidualAfter, hleft, hinput, hequiv, overwrite]
  · funext key
    simp only [runsToFunction_cons]
    by_cases hleft : prev.range.val.lo ≤ key ∧ key ≤ input.lo - 1
    · have hprev : prev.range.val.lo ≤ key ∧ key ≤ prev.range.val.hi := by
        omega
      have hinput : ¬ (input.lo ≤ key ∧ key ≤ input.hi) := by omega
      simp [leftResidualBefore, hleft, hprev, hinput, overwrite]
    · by_cases hinput : input.lo ≤ key ∧ key ≤ input.hi
      · simp [leftResidualBefore, hleft, hinput, overwrite]
      · have hprev : ¬
            (prev.range.val.lo ≤ key ∧ key ≤ prev.range.val.hi) := by
          omega
        simp [leftResidualBefore, hleft, hinput, hprev, overwrite]

/-- Merging a touching same-valued predecessor with the input has exact
overwrite semantics. -/
private lemma mergePredecessor_toFunction {Value : Type*}
    (prev : Run Value) (after : List (Run Value))
    (input : IntRange) (value : Value) (hnonempty : input.lo ≤ input.hi)
    (hstart : prev.range.val.lo ≤ input.lo)
    (hsame : prev.value = value)
    (htouch : input.lo ≤ prev.range.val.hi + 1) :
    runsToFunction
        (mergeForward prev { range := ⟨input, hnonempty⟩, value := value } :: after) =
      overwrite (runsToFunction (prev :: after)) input value := by
  funext key
  simp only [runsToFunction_cons]
  by_cases hprev : prev.range.val.lo ≤ key ∧ key ≤ prev.range.val.hi
  · have hmerged : prev.range.val.lo ≤ key ∧
        key ≤ max prev.range.val.hi input.hi :=
      ⟨hprev.1, hprev.2.trans (le_max_left _ _)⟩
    simp [mergeForward, hprev, hmerged, overwrite, hsame]
  · by_cases hinput : input.lo ≤ key ∧ key ≤ input.hi
    · have hmerged : prev.range.val.lo ≤ key ∧
          key ≤ max prev.range.val.hi input.hi := by
        exact ⟨hstart.trans hinput.1, hinput.2.trans (le_max_right _ _)⟩
      change (if prev.range.val.lo ≤ key ∧
          key ≤ max prev.range.val.hi input.hi then
          some prev.value else runsToFunction after key) = _
      rw [if_pos hmerged]
      simp [overwrite, hinput, hsame]
    · have hmerged : ¬ (prev.range.val.lo ≤ key ∧
          key ≤ max prev.range.val.hi input.hi) := by
        intro h
        rcases le_max_iff.mp h.2 with hhi | hhi
        · exact hprev ⟨h.1, hhi⟩
        · by_cases hlo : input.lo ≤ key
          · exact hinput ⟨hlo, hhi⟩
          · exact hprev ⟨h.1, by omega⟩
      change (if prev.range.val.lo ≤ key ∧
          key ≤ max prev.range.val.hi input.hi then
          some prev.value else runsToFunction after key) = _
      rw [if_neg hmerged]
      simp [overwrite, hinput, hprev]

/-- Pure list model of the production cursor insertion path. -/
private def internalAddCMapRuns {Value : Type*} [DecidableEq Value]
    (runs : List (Run Value)) (input : IntRange) (value : Value)
    (hnonempty : input.lo ≤ input.hi) : List (Run Value) :=
  let split := List.span (fun run => decide (run.range.val.lo < input.lo)) runs
  let before := split.fst
  let after := split.snd
  let inserted : Run Value := { range := ⟨input, hnonempty⟩, value := value }
  match hprev : before.getLast? with
  | none => scanForward inserted after
  | some prev =>
      let init := before.dropLast
      if hsame : prev.value = value then
        if htouch : input.lo ≤ prev.range.val.hi + 1 then
          if input.hi ≤ prev.range.val.hi then
            runs
          else
            init ++ scanForward (mergeForward prev inserted) after
        else
          before ++ scanForward inserted after
      else if hoverlap : input.lo ≤ prev.range.val.hi then
        have hstarts : prev.range.val.lo < input.lo := by
          have hmem : prev ∈ before := List.mem_of_mem_getLast? (by simp [hprev])
          have hmem' : prev ∈
              runs.takeWhile (fun run => decide (run.range.val.lo < input.lo)) := by
            simpa only [before, split, List.span_eq_takeWhile_dropWhile] using hmem
          have hpred := List.mem_takeWhile_imp hmem'
          exact of_decide_eq_true hpred
        let left := leftResidualBefore input.lo prev hstarts
        if hextends : input.hi < prev.range.val.hi then
          init ++ left :: inserted :: rightResidualAfter input.hi prev hextends :: after
        else
          init ++ left :: scanForward inserted after
      else
        before ++ scanForward inserted after

/-- The complete list-level insertion contract.  Its proof is the sole
remaining composition obligation: it derives the predecessor/suffix facts from
the canonical input and dispatches each executable branch to the local
residual and forward-scan contracts. -/
private theorem internalAddCMapRuns_spec {Value : Type*} [DecidableEq Value]
    (runs : List (Run Value)) (input : IntRange) (value : Value)
    (hnonempty : input.lo ≤ input.hi) (hcanonical : Canonical runs) :
    let output := internalAddCMapRuns runs input value hnonempty
    Canonical output ∧
      runsToFunction output =
        overwrite (runsToFunction runs) input value := by
  unfold internalAddCMapRuns
  dsimp only
  split <;> rename_i hprev
  · let split := List.span
        (fun run => decide (run.range.val.lo < input.lo)) runs
    let before := split.fst
    let after := split.snd
    let inserted : Run Value := { range := ⟨input, hnonempty⟩, value := value }
    have hdecomp : before ++ after = runs := by
      simp [split, before, after, List.span_eq_takeWhile_dropWhile]
    have hbeforeEmpty : before = [] := by
      apply List.getLast?_eq_none_iff.mp
      simpa [split, before] using hprev
    have hafterRuns : after = runs := by
      simpa [hbeforeEmpty] using hdecomp
    have hcanonicalAfter : Canonical after := by simpa [hafterRuns] using hcanonical
    have hlowerAfter : ∀ run ∈ after, input.lo ≤ run.range.val.lo := by
      simpa [split, after] using
        strictStartSuffix_lower_bound runs input.lo hcanonical
    have hscan := scanForward_spec inserted after hcanonicalAfter (by
      simpa [inserted] using hlowerAfter)
    refine ⟨hscan.1, hscan.2.trans ?_⟩
    simpa [inserted, hafterRuns] using
      insertedSuffix_toFunction after input value hnonempty hlowerAfter
  · rename_i prev
    set before :=
      (List.span (fun run => decide (run.range.val.lo < input.lo)) runs).fst with hbeforeEq
    set after :=
      (List.span (fun run => decide (run.range.val.lo < input.lo)) runs).snd with hafterEq
    simp only [← hbeforeEq] at hprev ⊢
    let inserted : Run Value := { range := ⟨input, hnonempty⟩, value := value }
    have hdecomp : before ++ after = runs := by
      simp [before, after, List.span_eq_takeWhile_dropWhile]
    have hwholeCanonical : Canonical (before ++ after) := by
      simpa [hdecomp] using hcanonical
    have hcanonicalBefore : Canonical before :=
      (List.pairwise_append.mp hwholeCanonical).1
    have hcanonicalAfter : Canonical after :=
      (List.pairwise_append.mp hwholeCanonical).2.1
    have hcross : ∀ left ∈ before, ∀ right ∈ after, Run.before left right :=
      (List.pairwise_append.mp hwholeCanonical).2.2
    have hlowerAfter : ∀ run ∈ after, input.lo ≤ run.range.val.lo := by
      simpa [after] using strictStartSuffix_lower_bound runs input.lo hcanonical
    have hprevMem : prev ∈ before :=
      List.mem_of_mem_getLast? (by simp [hprev])
    have hprevStart : prev.range.val.lo < input.lo := by
      have hmem : prev ∈ runs.takeWhile
          (fun run => decide (run.range.val.lo < input.lo)) := by
        simpa [before, List.span_eq_takeWhile_dropWhile] using hprevMem
      have hp : decide (prev.range.val.lo < input.lo) = true :=
        List.mem_takeWhile_imp
          (p := fun run : Run Value => decide (run.range.val.lo < input.lo)) hmem
      exact of_decide_eq_true hp
    have hbeforeInit : before.dropLast ++ [prev] = before :=
      List.dropLast_append_getLast? prev (by simp [hprev])
    have hfull : before.dropLast ++ prev :: after = runs := by
      have h := congrArg (fun xs => xs ++ after) hbeforeInit
      have h' : before.dropLast ++ prev :: after = before ++ after := by
        simpa [List.append_assoc] using h
      exact h'.trans hdecomp
    have hcanonicalInitPrev : Canonical (before.dropLast ++ [prev]) := by
      simpa [hbeforeInit] using hcanonicalBefore
    have hcanonicalInit : Canonical before.dropLast :=
      (List.pairwise_append.mp hcanonicalInitPrev).1
    have hinitBeforePrev : ∀ run ∈ before.dropLast, Run.before run prev := by
      intro run hrun
      exact (List.pairwise_append.mp hcanonicalInitPrev).2.2 run hrun prev (by simp)
    have hprevAfter : ∀ run ∈ after, Run.before prev run :=
      fun run hrun => hcross prev hprevMem run hrun
    have hinitLeftOfInput : ∀ run ∈ before.dropLast,
        run.range.val.hi < input.lo := by
      intro run hrun
      exact (Run.before_hi_lt (hinitBeforePrev run hrun)).trans hprevStart
    by_cases hsame : prev.value = value
    · simp only [hsame, ↓reduceDIte]
      by_cases htouch : input.lo ≤ prev.range.val.hi + 1
      · simp only [htouch, ↓reduceDIte]
        by_cases hcovered : input.hi ≤ prev.range.val.hi
        · simp only [hcovered, ↓reduceIte]
          refine ⟨hcanonical, ?_⟩
          have htail : runsToFunction (prev :: after) =
              overwrite (runsToFunction (prev :: after)) input value := by
            funext key
            by_cases hin : input.lo ≤ key ∧ key ≤ input.hi
            · have hprevContains :
                  prev.range.val.lo ≤ key ∧ key ≤ prev.range.val.hi := by
                omega
              simp [runsToFunction_cons, overwrite, hin, hprevContains, hsame]
            · simp [overwrite, hin]
          have hall := prepend_left_of_overwrite before.dropLast
            (prev :: after) (prev :: after) input value hinitLeftOfInput htail
          simpa [hfull] using hall
        · simp only [hcovered, ↓reduceIte]
          have hextends : prev.range.val.hi < input.hi := by omega
          let merged := mergeForward prev inserted
          have hscan := scanForward_spec merged after hcanonicalAfter (by
            intro run hrun
            simpa [merged, mergeForward] using
              (hprevStart.le.trans (hlowerAfter run hrun)))
          have hinitBeforeScan : ∀ left ∈ before.dropLast,
              ∀ right ∈ scanForward merged after, Run.before left right := by
            intro left hleft
            have hleftMerged : Run.before left merged := by
              have hleftPrev := hinitBeforePrev left hleft
              constructor
              · simpa [merged, mergeForward, Run.disjointBefore] using hleftPrev.1
              · intro hvalue
                apply hleftPrev.2
                simpa [merged, mergeForward] using hvalue
            apply scanForward_preserves_left_boundary left merged after hleftMerged
            intro run hrun
            apply hcross left
            · rw [← hbeforeInit]
              simp [hleft]
            · exact hrun
          refine ⟨List.pairwise_append.mpr
            ⟨hcanonicalInit, hscan.1, hinitBeforeScan⟩, ?_⟩
          have htail : runsToFunction (scanForward merged after) =
              overwrite (runsToFunction (prev :: after)) input value :=
            hscan.2.trans (by
              simpa [merged, inserted] using
                mergePredecessor_toFunction prev after input value hnonempty
                  hprevStart.le hsame htouch)
          have hall := prepend_left_of_overwrite before.dropLast
            (prev :: after) (scanForward merged after) input value
              hinitLeftOfInput htail
          simpa [merged, inserted, hfull] using hall
      · simp only [htouch, ↓reduceDIte]
        have hprevInserted : Run.before prev inserted := by
          constructor
          · unfold Run.disjointBefore
            change prev.range.val.hi < input.lo
            omega
          · intro _
            unfold IntRange.NR.before
            change prev.range.val.hi + 1 < input.lo
            omega
        have hscan := scanForward_spec inserted after hcanonicalAfter (by
          simpa [inserted] using hlowerAfter)
        have hprevBeforeScan := scanForward_preserves_left_boundary
          prev inserted after hprevInserted hprevAfter
        have hbeforeScan : ∀ left ∈ before,
            ∀ right ∈ scanForward inserted after, Run.before left right := by
          intro left hleft right hright
          rw [← hbeforeInit] at hleft
          rcases List.mem_append.mp hleft with hleft | hleft
          · exact Run.before_trans (hinitBeforePrev left hleft)
              (hprevBeforeScan right hright)
          · simp only [List.mem_singleton] at hleft
            subst left
            exact hprevBeforeScan right hright
        refine ⟨List.pairwise_append.mpr
          ⟨hcanonicalBefore, hscan.1, hbeforeScan⟩, ?_⟩
        have hbeforeLeft : ∀ run ∈ before,
            run.range.val.hi < input.lo := by
          intro run hrun
          rw [← hbeforeInit] at hrun
          rcases List.mem_append.mp hrun with hrun | hrun
          · exact hinitLeftOfInput run hrun
          · simp only [List.mem_singleton] at hrun
            subst run
            omega
        have htail : runsToFunction (scanForward inserted after) =
            overwrite (runsToFunction after) input value :=
          hscan.2.trans (by
            simpa [inserted] using
              insertedSuffix_toFunction after input value hnonempty hlowerAfter)
        have hall := prepend_left_of_overwrite before after
          (scanForward inserted after) input value hbeforeLeft htail
        simpa [inserted, hdecomp] using hall
    · simp only [hsame, ↓reduceDIte]
      by_cases hoverlap : input.lo ≤ prev.range.val.hi
      · simp only [hoverlap, ↓reduceDIte]
        by_cases hextends : input.hi < prev.range.val.hi
        · simp only [hextends, ↓reduceDIte]
          let left := leftResidualBefore input.lo prev hprevStart
          let residual := rightResidualAfter input.hi prev hextends
          have hleftInserted : Run.before left inserted := by
            constructor
            · simp [left, leftResidualBefore, inserted, Run.disjointBefore]
            · intro hvalue
              exact (hsame (by
                simpa [left, leftResidualBefore, inserted] using hvalue)).elim
          have hinsertedResidual : Run.before inserted residual := by
            constructor
            · simp [inserted, residual, rightResidualAfter, Run.disjointBefore]
            · intro hvalue
              exact (hsame (by
                simpa [inserted, residual, rightResidualAfter] using hvalue.symm)).elim
          have hresidualAfter : ∀ run ∈ after, Run.before residual run := by
            intro run hrun
            have hpr := hprevAfter run hrun
            constructor
            · simpa [residual, rightResidualAfter, Run.disjointBefore] using hpr.1
            · intro hvalue
              apply hpr.2
              simpa [residual, rightResidualAfter] using hvalue
          have htailCanonical : Canonical (left :: inserted :: residual :: after) := by
            have hresidualCanonical : Canonical (residual :: after) :=
              List.pairwise_cons.mpr ⟨hresidualAfter, hcanonicalAfter⟩
            have hinsertedAfter : ∀ run ∈ residual :: after,
                Run.before inserted run := by
              intro run hrun
              rcases List.mem_cons.mp hrun with rfl | hrun
              · exact hinsertedResidual
              · exact Run.before_trans hinsertedResidual (hresidualAfter run hrun)
            have hinsertedCanonical : Canonical (inserted :: residual :: after) :=
              List.pairwise_cons.mpr ⟨hinsertedAfter, hresidualCanonical⟩
            apply List.pairwise_cons.mpr
            constructor
            · intro run hrun
              rcases List.mem_cons.mp hrun with rfl | hrun
              · exact hleftInserted
              · exact Run.before_trans hleftInserted
                  (List.rel_of_pairwise_cons hinsertedCanonical hrun)
            · exact hinsertedCanonical
          have hinitBeforeLeft : ∀ run ∈ before.dropLast, Run.before run left := by
            intro run hrun
            have hrp := hinitBeforePrev run hrun
            constructor
            · simpa [left, leftResidualBefore, Run.disjointBefore] using hrp.1
            · intro hvalue
              apply hrp.2
              simpa [left, leftResidualBefore] using hvalue
          have hinitTail : ∀ run ∈ before.dropLast,
              ∀ following ∈ left :: inserted :: residual :: after,
                Run.before run following := by
            intro run hrun following hfollowing
            rcases List.mem_cons.mp hfollowing with rfl | hfollowing
            · exact hinitBeforeLeft run hrun
            · exact Run.before_trans (hinitBeforeLeft run hrun)
                (List.rel_of_pairwise_cons htailCanonical hfollowing)
          refine ⟨List.pairwise_append.mpr
            ⟨hcanonicalInit, htailCanonical, hinitTail⟩, ?_⟩
          have htail : runsToFunction (left :: inserted :: residual :: after) =
              overwrite (runsToFunction (prev :: after)) input value := by
            simpa [left, residual, inserted, hextends] using
              replacePredecessor_toFunction prev after input value hnonempty
                hprevStart hoverlap
          have hall := prepend_left_of_overwrite before.dropLast
            (prev :: after) (left :: inserted :: residual :: after)
              input value hinitLeftOfInput htail
          simpa [left, residual, inserted, hfull] using hall
        · simp only [hextends, ↓reduceDIte]
          let left := leftResidualBefore input.lo prev hprevStart
          have hscan := scanForward_spec inserted after hcanonicalAfter (by
            simpa [inserted] using hlowerAfter)
          have hleftInserted : Run.before left inserted := by
            constructor
            · simp [left, leftResidualBefore, inserted, Run.disjointBefore]
            · intro hvalue
              exact (hsame (by
                simpa [left, leftResidualBefore, inserted] using hvalue)).elim
          have hleftAfter : ∀ run ∈ after, Run.before left run := by
            intro run hrun
            have hpr := hprevAfter run hrun
            constructor
            · unfold Run.disjointBefore
              simp only [left, leftResidualBefore]
              have hlower := hlowerAfter run hrun
              omega
            · intro hvalue
              have hgap := hpr.2 (by
                simpa [left, leftResidualBefore] using hvalue)
              unfold IntRange.NR.before at hgap ⊢
              simp only [left, leftResidualBefore]
              omega
          have hleftScan := scanForward_preserves_left_boundary
            left inserted after hleftInserted hleftAfter
          have htailCanonical : Canonical (left :: scanForward inserted after) :=
            List.pairwise_cons.mpr ⟨hleftScan, hscan.1⟩
          have hinitBeforeLeft : ∀ run ∈ before.dropLast, Run.before run left := by
            intro run hrun
            have hrp := hinitBeforePrev run hrun
            constructor
            · simpa [left, leftResidualBefore, Run.disjointBefore] using hrp.1
            · intro hvalue
              apply hrp.2
              simpa [left, leftResidualBefore] using hvalue
          have hinitTail : ∀ run ∈ before.dropLast,
              ∀ following ∈ left :: scanForward inserted after,
                Run.before run following := by
            intro run hrun following hfollowing
            rcases List.mem_cons.mp hfollowing with rfl | hfollowing
            · exact hinitBeforeLeft run hrun
            · exact Run.before_trans (hinitBeforeLeft run hrun)
                (hleftScan following hfollowing)
          refine ⟨List.pairwise_append.mpr
            ⟨hcanonicalInit, htailCanonical, hinitTail⟩, ?_⟩
          have hleftScanFunction :
              runsToFunction (left :: scanForward inserted after) =
                runsToFunction (left :: inserted :: after) := by
            funext key
            simp only [runsToFunction_cons]
            split
            · rfl
            · simpa only [runsToFunction_cons] using congrFun hscan.2 key
          have hreplace : runsToFunction (left :: inserted :: after) =
              overwrite (runsToFunction (prev :: after)) input value := by
            simpa [left, inserted, hextends] using
              replacePredecessor_toFunction prev after input value hnonempty
                hprevStart hoverlap
          have htail := hleftScanFunction.trans hreplace
          have hall := prepend_left_of_overwrite before.dropLast
            (prev :: after) (left :: scanForward inserted after)
              input value hinitLeftOfInput htail
          simpa [left, inserted, hfull] using hall
      · simp only [hoverlap, ↓reduceDIte]
        have hprevInserted : Run.before prev inserted := by
          constructor
          · unfold Run.disjointBefore
            change prev.range.val.hi < input.lo
            omega
          · intro hvalue
            exact (hsame (by simpa [inserted] using hvalue)).elim
        have hscan := scanForward_spec inserted after hcanonicalAfter (by
          simpa [inserted] using hlowerAfter)
        have hprevBeforeScan := scanForward_preserves_left_boundary
          prev inserted after hprevInserted hprevAfter
        have hbeforeScan : ∀ left ∈ before,
            ∀ right ∈ scanForward inserted after, Run.before left right := by
          intro left hleft right hright
          rw [← hbeforeInit] at hleft
          rcases List.mem_append.mp hleft with hleft | hleft
          · exact Run.before_trans (hinitBeforePrev left hleft)
              (hprevBeforeScan right hright)
          · simp only [List.mem_singleton] at hleft
            subst left
            exact hprevBeforeScan right hright
        refine ⟨List.pairwise_append.mpr
          ⟨hcanonicalBefore, hscan.1, hbeforeScan⟩, ?_⟩
        have hbeforeLeft : ∀ run ∈ before,
            run.range.val.hi < input.lo := by
          intro run hrun
          rw [← hbeforeInit] at hrun
          rcases List.mem_append.mp hrun with hrun | hrun
          · exact hinitLeftOfInput run hrun
          · simp only [List.mem_singleton] at hrun
            subst run
            omega
        have htail : runsToFunction (scanForward inserted after) =
            overwrite (runsToFunction after) input value :=
          hscan.2.trans (by
            simpa [inserted] using
              insertedSuffix_toFunction after input value hnonempty hlowerAfter)
        have hall := prepend_left_of_overwrite before after
          (scanForward inserted after) input value hbeforeLeft htail
        simpa [inserted, hdecomp] using hall

/-- Insert one labeled inclusive range by the production predecessor/forward
scan algorithm. -/
def internalAddCMap {Value : Type*} [DecidableEq Value]
    (map : RangeMapBlaze Value) (input : IntRange) (value : Value) : RangeMapBlaze Value := by
  if h : input.hi < input.lo then
    exact map
  else
    have hnonempty : input.lo ≤ input.hi := by omega
    let output := internalAddCMapRuns map.runs input value hnonempty
    refine ⟨output, ?_⟩
    exact (internalAddCMapRuns_spec map.runs input value hnonempty map.canonical).1

/-- Production-shaped insertion has exact pointwise overwrite semantics. -/
theorem internalAddCMap_toFunction {Value : Type*} [DecidableEq Value]
    (map : RangeMapBlaze Value) (input : IntRange) (value : Value) :
    (internalAddCMap map input value).toFunction =
      overwrite map.toFunction input value := by
  unfold internalAddCMap
  split <;> rename_i h
  · exact (overwrite_eq_of_hi_lt_lo map.toFunction input value h).symm
  · dsimp only [toFunction]
    exact (internalAddCMapRuns_spec map.runs input value (by omega) map.canonical).2

end RangeMapBlaze
