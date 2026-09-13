import RangeSetBlaze.Basic

namespace RangeMapBlaze

open IntRange (NR)

/-!
## Algo D map: a cursor-local production model

The executable model below represents the Rust `BTreeMap` cursor by a gap in a
canonical run list.  `left` is the finalized side of the cursor and `right` is
the untouched side visible through `peek_next`.  The model keeps the Rust
control flow—one predecessor classification, local predecessor mutation, and
a forward remove/merge scan—without pretending that a functional list is a
mutable B-tree.

Cached cardinality and iterator validity are representation facts of the Rust
container.  They are recorded in the proof sketch, but are not part of this
semantic model.
-/

private structure CursorGap (Value : Type*) where
  left : List (Run Value)
  right : List (Run Value)

private def lowerBoundGap {Value : Type*} (start : Int) (runs : List (Run Value)) :
    CursorGap Value :=
  let split := List.span (fun run => decide (run.range.val.lo < start)) runs
  { left := split.fst, right := split.snd }

private def CursorGap.peekPrev {Value : Type*} (gap : CursorGap Value) :
    Option (Run Value) := gap.left.getLast?

private def CursorGap.peekNext {Value : Type*} (gap : CursorGap Value) :
    Option (Run Value) := gap.right.head?

private def leftResidualBefore {Value : Type*}
    (start : Int) (run : Run Value) (h : run.range.val.lo < start) : Run Value :=
  { range := ⟨⟨run.range.val.lo, start - 1⟩, by
      exact (le_sub_iff_add_le).mpr (Int.add_one_le_iff.mpr h)⟩, value := run.value }

private def rightResidualAfter {Value : Type*}
    (stop : Int) (run : Run Value) (h : stop < run.range.val.hi) : Run Value :=
  { range := ⟨⟨stop + 1, run.range.val.hi⟩, by
      exact Int.add_one_le_iff.mpr h⟩, value := run.value }

private def mergeForward {Value : Type*} (left right : Run Value) : Run Value :=
  { range := ⟨⟨left.range.val.lo, max left.range.val.hi right.range.val.hi⟩,
      left.range.property.trans (le_max_left _ _)⟩, value := left.value }

private inductive PredecessorAction (Value : Type*) where
  | unaffected
  | mergeSame
  | trimDifferent (left : Run Value) (rightResidual : Option (Run Value))

private def classifyPredecessor {Value : Type*} [DecidableEq Value]
    (pendingStart pendingEnd : Int) (pendingValue : Value)
    (stored : Run Value) : PredecessorAction Value :=
  let overlaps := stored.range.val.hi ≥ pendingStart
  let touches := stored.range.val.hi + 1 = pendingStart
  if !(overlaps || touches && stored.value = pendingValue) then
    .unaffected
  else if stored.value = pendingValue then
    .mergeSame
  else if hleft : stored.range.val.lo < pendingStart then
    .trimDifferent (leftResidualBefore pendingStart stored hleft)
      (if h : pendingEnd < stored.range.val.hi then
        some (rightResidualAfter pendingEnd stored h)
       else none)
  else .unaffected

private inductive ForwardAction (Value : Type*) where
  | mergeSame
  | deleteOverwritten
  | keepRightResidual (residual : Run Value)

private def classifyForward {Value : Type*} [DecidableEq Value]
    (pendingEnd : Int) (pendingValue : Value) (stored : Run Value) :
    Option (ForwardAction Value) :=
  let overlaps := stored.range.val.lo ≤ pendingEnd
  let touches := pendingEnd + 1 = stored.range.val.lo
  if !(overlaps || touches && stored.value = pendingValue) then none
  else if stored.value = pendingValue then some .mergeSame
  else if h : pendingEnd < stored.range.val.hi then
    some (.keepRightResidual (rightResidualAfter pendingEnd stored h))
  else some .deleteOverwritten

private structure ScanResult {Value : Type*} where
  pending : Run Value
  rightResidual : Option (Run Value)
  remaining : List (Run Value)
  unchanged : Bool

/- The `stored` flag is the Lean counterpart of Rust's `pending_is_stored`.
   It controls the exact-start cover fast path; all other branches consume the
   same right-side cursor operation. -/
private def scanForward {Value : Type*} [DecidableEq Value]
    (pending : Run Value) (stored : Bool) : List (Run Value) →
      ScanResult (Value := Value)
  | [] => { pending, rightResidual := none, remaining := [], unchanged := false }
  | next :: rest =>
      if !stored && next.range.val.lo = pending.range.val.lo &&
          next.value = pending.value && pending.range.val.hi ≤ next.range.val.hi then
        { pending, rightResidual := none, remaining := next :: rest, unchanged := true }
      else
        match classifyForward pending.range.val.hi pending.value next with
        | none => { pending, rightResidual := none, remaining := next :: rest, unchanged := false }
        | some .mergeSame =>
            scanForward (mergeForward pending next) stored rest
        | some .deleteOverwritten =>
            scanForward pending stored rest
        | some (.keepRightResidual residual) =>
            { pending, rightResidual := some residual,
              remaining := rest,
              unchanged := false }
termination_by suffix => suffix.length

private def scanOutput {Value : Type*} (scan : ScanResult (Value := Value)) :
    List (Run Value) :=
  if scan.unchanged then scan.remaining
  else scan.pending :: scan.rightResidual.toList ++ scan.remaining

private def internalAddDMapRuns {Value : Type*} [DecidableEq Value]
    (runs : List (Run Value)) (input : IntRange) (value : Value)
    (hinput : input.lo ≤ input.hi) : List (Run Value) :=
  let gap := lowerBoundGap input.lo runs
  let fresh : Run Value := ⟨⟨input, hinput⟩, value⟩
  match gap.peekPrev with
  | none =>
      let scan := scanForward fresh false gap.right
      if scan.unchanged then runs else
        gap.left ++ scanOutput scan
  | some predecessor =>
      match classifyPredecessor input.lo input.hi value predecessor with
      | .unaffected =>
          let scan := scanForward fresh false gap.right
          if scan.unchanged then runs else
            gap.left ++ scanOutput scan
      | .mergeSame =>
          if input.hi ≤ predecessor.range.val.hi then runs
          else
            let grown := mergeForward predecessor fresh
            let scan := scanForward grown true gap.right
            if scan.unchanged then runs
            else gap.left.dropLast ++ scanOutput scan
      | .trimDifferent left rightResidual =>
          match rightResidual with
          | some residual => gap.left.dropLast ++ left :: fresh :: residual :: gap.right
          | none =>
              let scan := scanForward fresh false gap.right
              if scan.unchanged then gap.left.dropLast ++ left :: gap.right
              else gap.left.dropLast ++ left :: scanOutput scan

/-- Runs in the right side of the cursor gap start at or after its lower
bound. -/
private lemma strictStartSuffix_lowerBound {Value : Type*}
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

private theorem lowerBoundGap_decomposition
    {Value : Type*} (runs : List (Run Value)) (start : Int)
    (hcanonical : Canonical runs) :
    let gap := lowerBoundGap start runs
    runs = gap.left ++ gap.right ∧
      (∀ run ∈ gap.left, run.range.val.lo < start) ∧
      (∀ run ∈ gap.right, start ≤ run.range.val.lo) := by
  dsimp only [lowerBoundGap]
  let split := List.span (fun run => decide (run.range.val.lo < start)) runs
  have hdecomp : split.fst ++ split.snd = runs := by
    simp [split, List.span_eq_takeWhile_dropWhile]
  have hleft : ∀ run ∈ split.fst, run.range.val.lo < start := by
    intro run hrun
    have hrun' : run ∈ runs.takeWhile
        (fun candidate => decide (candidate.range.val.lo < start)) := by
      simpa [split, List.span_eq_takeWhile_dropWhile] using hrun
    exact of_decide_eq_true
      (List.mem_takeWhile_imp (p := fun candidate : Run Value =>
        decide (candidate.range.val.lo < start)) hrun')
  have hright : ∀ run ∈ split.snd, start ≤ run.range.val.lo := by
    simpa [split, List.span_eq_takeWhile_dropWhile] using
      strictStartSuffix_lowerBound runs start hcanonical
  exact ⟨hdecomp.symm, hleft, hright⟩

private theorem predecessorTrim_preserves_toFunction
    {Value : Type*}
    (predecessor : Run Value) (input : IntRange) (value : Value)
    (hinput : input.lo ≤ input.hi)
    (hleft : predecessor.range.val.lo < input.lo)
    (hnoGap : ¬ IntRange.NR.before predecessor.range (⟨input, hinput⟩ : NR))
    (hcover : predecessor.range.val.hi ≤ input.hi) :
    runsToFunction
        ([leftResidualBefore input.lo predecessor hleft,
          ⟨⟨input, hinput⟩, value⟩] : List (Run Value)) =
      overwrite (runsToFunction ([predecessor] : List (Run Value))) input value := by
  funext key
  simp only [runsToFunction_cons]
  by_cases hleftResidual :
      predecessor.range.val.lo ≤ key ∧ key ≤ input.lo - 1
  · have hpredecessor :
        predecessor.range.val.lo ≤ key ∧ key ≤ predecessor.range.val.hi := by
      change ¬ (predecessor.range.val.hi + 1 < input.lo) at hnoGap
      omega
    have hinputRange : ¬ (input.lo ≤ key ∧ key ≤ input.hi) := by omega
    simp [leftResidualBefore, hleftResidual, hpredecessor, hinputRange, overwrite]
  · by_cases hinputRange : input.lo ≤ key ∧ key ≤ input.hi
    · simp [leftResidualBefore, hleftResidual, hinputRange, overwrite]
    · have hpredecessor : ¬
          (predecessor.range.val.lo ≤ key ∧ key ≤ predecessor.range.val.hi) := by
        change ¬ (predecessor.range.val.hi + 1 < input.lo) at hnoGap
        omega
      simp [leftResidualBefore, hleftResidual, hinputRange, hpredecessor, overwrite]

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
        rcases le_max_iff.mp h.2 with hhi | hhi
        · exact hpending ⟨h.1, hhi⟩
        · by_cases hk : key ≤ pending.range.val.hi
          · exact hpending ⟨h.1, hk⟩
          · exact hnext ⟨by omega, hhi⟩
      change (if pending.range.val.lo ≤ key ∧
          key ≤ max pending.range.val.hi next.range.val.hi then
          some pending.value else runsToFunction rest key) = _
      rw [if_neg hmerged, if_neg hpending, if_neg hnext]

/-- The unstored exact-start fast path preserves the pending function. -/
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

/-- Deleting a later run covered by pending preserves first-match semantics. -/
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

/-- Replacing an overlapping suffix run by its right residual preserves the
pending-first function. -/
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

private theorem scanForward_preserves_canonical_and_overwrite
    {Value : Type*} [DecidableEq Value]
    (pending : Run Value) (suffix : List (Run Value)) (stored : Bool)
    (hcanonical : Canonical suffix)
    (hlower : ∀ run ∈ suffix, pending.range.val.lo ≤ run.range.val.lo) :
    Canonical (scanOutput (scanForward pending stored suffix)) ∧
      runsToFunction (scanOutput (scanForward pending stored suffix)) =
        runsToFunction (pending :: suffix) := by
  induction suffix generalizing pending stored with
  | nil => simp [scanForward, scanOutput, Canonical]
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
      have hcontinue : ∀ stored : Bool,
          Canonical (scanOutput
            (match classifyForward pending.range.val.hi pending.value next with
            | none =>
                { pending, rightResidual := none,
                  remaining := next :: rest, unchanged := false }
            | some .mergeSame => scanForward (mergeForward pending next) stored rest
            | some .deleteOverwritten => scanForward pending stored rest
            | some (.keepRightResidual residual) =>
                { pending, rightResidual := some residual,
                  remaining := rest, unchanged := false })) ∧
          runsToFunction (scanOutput
            (match classifyForward pending.range.val.hi pending.value next with
            | none =>
                { pending, rightResidual := none,
                  remaining := next :: rest, unchanged := false }
            | some .mergeSame => scanForward (mergeForward pending next) stored rest
            | some .deleteOverwritten => scanForward pending stored rest
            | some (.keepRightResidual residual) =>
                { pending, rightResidual := some residual,
                  remaining := rest, unchanged := false })) =
            runsToFunction (pending :: next :: rest) := by
        intro stored
        by_cases hsame : pending.value = next.value
        · by_cases htouch : next.range.val.lo ≤ pending.range.val.hi + 1
          · have hclass : classifyForward pending.range.val.hi pending.value next =
                some .mergeSame := by
              by_cases hoverlap : next.range.val.lo ≤ pending.range.val.hi
              · simp [classifyForward, hsame.symm, hoverlap]
              · have htoucheq : pending.range.val.hi + 1 = next.range.val.lo := by
                  omega
                simp [classifyForward, hsame.symm, hoverlap, htoucheq]
            have hlowerMerged : ∀ run ∈ rest,
                (mergeForward pending next).range.val.lo ≤ run.range.val.lo := by
              simpa [mergeForward] using hlowerRest
            have hspec := ih (mergeForward pending next) stored
              hcanonicalRest hlowerMerged
            rw [hclass]
            refine ⟨hspec.1, ?_⟩
            exact hspec.2.trans
              (mergeForward_toFunction pending next rest hlowerNext htouch hsame)
          · have hbeforeNext : Run.before pending next := by
              have hgap : pending.range.val.hi + 1 < next.range.val.lo := by omega
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
            have hnotOverlap : ¬ next.range.val.lo ≤ pending.range.val.hi := by omega
            have hnotTouches : ¬ pending.range.val.hi + 1 = next.range.val.lo := by omega
            have hclass : classifyForward pending.range.val.hi pending.value next =
                none := by
              simp [classifyForward, hnotOverlap, hnotTouches]
            rw [hclass]
            simpa [scanOutput]
              using (show Canonical (pending :: next :: rest) ∧
                runsToFunction (pending :: next :: rest) =
                  runsToFunction (pending :: next :: rest) from
                ⟨List.pairwise_cons.mpr ⟨hbeforeAll, hcanonical⟩, rfl⟩)
        · by_cases hoverlap : next.range.val.lo ≤ pending.range.val.hi
          · by_cases hextends : pending.range.val.hi < next.range.val.hi
            · let residual := rightResidualAfter pending.range.val.hi next hextends
              have hpendingResidual : Run.before pending residual := by
                refine ⟨?_, ?_⟩
                · simp [residual, rightResidualAfter, Run.disjointBefore]
                · intro heq
                  exact False.elim (hsame (by
                    simpa [residual, rightResidualAfter] using heq))
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
              have hresult : Canonical (pending :: residual :: rest) ∧
                  runsToFunction (pending :: residual :: rest) =
                    runsToFunction (pending :: next :: rest) := by
                refine ⟨List.pairwise_cons.mpr ⟨?_, hresidualCanonical⟩, ?_⟩
                · intro run hrun
                  rcases List.mem_cons.mp hrun with rfl | hrun
                  · exact hpendingResidual
                  · exact Run.before_trans hpendingResidual (hresidualAll run hrun)
                · exact rightResidualSplit_toFunction
                    pending next rest hlowerNext hoverlap hextends
              have hclass : classifyForward pending.range.val.hi pending.value next =
                  some (.keepRightResidual residual) := by
                have hsameNext : ¬ next.value = pending.value :=
                  fun h => hsame h.symm
                simp [classifyForward, hsameNext, hoverlap, hextends, residual]
              rw [hclass]
              simpa [scanOutput] using hresult
            · have hspec := ih pending stored hcanonicalRest hlowerRest
              have hcovered : next.range.val.hi ≤ pending.range.val.hi := by omega
              have hclass : classifyForward pending.range.val.hi pending.value next =
                  some .deleteOverwritten := by
                have hsameNext : ¬ next.value = pending.value :=
                  fun h => hsame h.symm
                simp [classifyForward, hsameNext, hoverlap, hextends]
              rw [hclass]
              refine ⟨hspec.1, ?_⟩
              exact hspec.2.trans
                (coveredRunDeletion_toFunction pending next rest hlowerNext hcovered)
          · have hbeforeNext : Run.before pending next := by
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
            have hclass : classifyForward pending.range.val.hi pending.value next =
                none := by
              have hsameNext : ¬ next.value = pending.value :=
                fun h => hsame h.symm
              simp [classifyForward, hsameNext, hoverlap]
            rw [hclass]
            simpa [scanOutput] using
              (show Canonical (pending :: next :: rest) ∧
                runsToFunction (pending :: next :: rest) =
                  runsToFunction (pending :: next :: rest) from
                ⟨List.pairwise_cons.mpr ⟨hbeforeAll, hcanonical⟩, rfl⟩)
      cases stored with
      | false =>
          by_cases hexact : (next.range.val.lo = pending.range.val.lo ∧
              next.value = pending.value) ∧ pending.range.val.hi ≤ next.range.val.hi
          · simpa [scanForward, hexact, scanOutput] using
              (show Canonical (next :: rest) ∧
                runsToFunction (next :: rest) =
                  runsToFunction (pending :: next :: rest) from
                ⟨hcanonical, sameValueExactCover_toFunction pending next rest
                  hexact.1.1 hexact.1.2.symm hexact.2⟩)
          · simpa [scanForward, hexact] using hcontinue false
      | true =>
          simpa [scanForward] using hcontinue true

/-- A finalized run before pending and the untouched suffix remains before
everything emitted by the cursor scan. -/
private lemma scanForward_preserves_left_boundary {Value : Type*} [DecidableEq Value]
    (left pending : Run Value) (suffix : List (Run Value)) (stored : Bool)
    (hpending : Run.before left pending)
    (hsuffix : ∀ run ∈ suffix, Run.before left run) :
    ∀ run ∈ scanOutput (scanForward pending stored suffix), Run.before left run := by
  induction suffix generalizing pending stored with
  | nil => simpa [scanForward, scanOutput] using
      (show ∀ run ∈ [pending], Run.before left run by simp [hpending])
  | cons next rest ih =>
      have hnext : Run.before left next := hsuffix next (by simp)
      have hrest : ∀ run ∈ rest, Run.before left run := by
        intro run hrun
        exact hsuffix run (by simp [hrun])
      have hcontinue : ∀ stored : Bool,
          ∀ run ∈ scanOutput
            (match classifyForward pending.range.val.hi pending.value next with
            | none =>
                { pending, rightResidual := none,
                  remaining := next :: rest, unchanged := false }
            | some .mergeSame => scanForward (mergeForward pending next) stored rest
            | some .deleteOverwritten => scanForward pending stored rest
            | some (.keepRightResidual residual) =>
                { pending, rightResidual := some residual,
                  remaining := rest, unchanged := false }),
            Run.before left run := by
        intro stored
        by_cases hsame : pending.value = next.value
        · by_cases htouch : next.range.val.lo ≤ pending.range.val.hi + 1
          · have hclass : classifyForward pending.range.val.hi pending.value next =
                some .mergeSame := by
              by_cases hoverlap : next.range.val.lo ≤ pending.range.val.hi
              · simp [classifyForward, hsame.symm, hoverlap]
              · have htoucheq : pending.range.val.hi + 1 = next.range.val.lo := by
                  omega
                simp [classifyForward, hsame.symm, hoverlap, htoucheq]
            rw [hclass]
            apply ih (mergeForward pending next) stored
            · constructor
              · simpa [mergeForward, Run.disjointBefore] using hpending.1
              · intro hvalue
                apply hpending.2
                simpa [mergeForward] using hvalue
            · exact hrest
          · have hclass : classifyForward pending.range.val.hi pending.value next =
                none := by
              have hnotOverlap : ¬ next.range.val.lo ≤ pending.range.val.hi := by omega
              have hnotTouches : ¬ pending.range.val.hi + 1 = next.range.val.lo := by omega
              simp [classifyForward, hnotOverlap, hnotTouches]
            rw [hclass]
            simpa [scanOutput] using
              (show ∀ run ∈ pending :: next :: rest, Run.before left run by
                intro run hrun
                rcases List.mem_cons.mp hrun with rfl | hrun
                · exact hpending
                · exact hsuffix run hrun)
        · by_cases hoverlap : next.range.val.lo ≤ pending.range.val.hi
          · by_cases hextends : pending.range.val.hi < next.range.val.hi
            · let residual := rightResidualAfter pending.range.val.hi next hextends
              have hresidual : Run.before left residual := by
                constructor
                · change left.range.val.hi < pending.range.val.hi + 1
                  have hleftPending : left.range.val.hi < pending.range.val.lo :=
                    hpending.1
                  have hpendingNonempty : pending.range.val.lo ≤ pending.range.val.hi :=
                    pending.range.property
                  omega
                · intro hvalue
                  have hgap := hnext.2 (by
                    simpa [residual, rightResidualAfter] using hvalue)
                  unfold IntRange.NR.before at hgap ⊢
                  simp only [residual, rightResidualAfter]
                  omega
              have hclass : classifyForward pending.range.val.hi pending.value next =
                  some (.keepRightResidual residual) := by
                have hsameNext : ¬ next.value = pending.value :=
                  fun h => hsame h.symm
                simp [classifyForward, hsameNext, hoverlap, hextends, residual]
              rw [hclass]
              intro run hrun
              change run ∈ pending :: residual :: rest at hrun
              rcases List.mem_cons.mp hrun with rfl | hrun
              · exact hpending
              · rcases List.mem_cons.mp hrun with rfl | hrun
                · exact hresidual
                · exact hrest run hrun
            · have hclass : classifyForward pending.range.val.hi pending.value next =
                  some .deleteOverwritten := by
                have hsameNext : ¬ next.value = pending.value :=
                  fun h => hsame h.symm
                simp [classifyForward, hsameNext, hoverlap, hextends]
              rw [hclass]
              exact ih pending stored hpending hrest
          · have hclass : classifyForward pending.range.val.hi pending.value next =
                none := by
              have hsameNext : ¬ next.value = pending.value :=
                fun h => hsame h.symm
              simp [classifyForward, hsameNext, hoverlap]
            rw [hclass]
            simpa [scanOutput] using
              (show ∀ run ∈ pending :: next :: rest, Run.before left run by
                intro run hrun
                rcases List.mem_cons.mp hrun with rfl | hrun
                · exact hpending
                · exact hsuffix run hrun)
      cases stored with
      | false =>
          by_cases hexact : (next.range.val.lo = pending.range.val.lo ∧
              next.value = pending.value) ∧ pending.range.val.hi ≤ next.range.val.hi
          · simpa [scanForward, hexact, scanOutput] using hsuffix
          · simpa [scanForward, hexact] using hcontinue false
      | true => simpa [scanForward] using hcontinue true

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

private lemma insertedSuffix_toFunction {Value : Type*}
    (suffix : List (Run Value)) (input : IntRange) (value : Value)
    (hinput : input.lo ≤ input.hi)
    (hlower : ∀ run ∈ suffix, input.lo ≤ run.range.val.lo) :
    runsToFunction ({ range := ⟨input, hinput⟩, value := value } :: suffix) =
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

private lemma prependLeft_preserves_overwrite {Value : Type*}
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
      · have hnotInput : ¬ (input.lo ≤ key ∧ key ≤ input.hi) := by omega
        simp [hcontains, overwrite, hnotInput]
      · simp only [hcontains, ↓reduceIte]
        rw [congrFun ih' key]
        simp [overwrite, hcontains]

private lemma predecessorMerge_preserves_overwrite {Value : Type*}
    (predecessor : Run Value) (suffix : List (Run Value))
    (input : IntRange) (value : Value) (hinput : input.lo ≤ input.hi)
    (hstart : predecessor.range.val.lo ≤ input.lo)
    (hsame : predecessor.value = value)
    (hnoGap : input.lo ≤ predecessor.range.val.hi + 1) :
    runsToFunction
        (mergeForward predecessor
          { range := ⟨input, hinput⟩, value := value } :: suffix) =
      overwrite (runsToFunction (predecessor :: suffix)) input value := by
  funext key
  simp only [runsToFunction_cons]
  by_cases hpredecessor :
      predecessor.range.val.lo ≤ key ∧ key ≤ predecessor.range.val.hi
  · have hmerged : predecessor.range.val.lo ≤ key ∧
        key ≤ max predecessor.range.val.hi input.hi :=
      ⟨hpredecessor.1, hpredecessor.2.trans (le_max_left _ _)⟩
    simp [mergeForward, hpredecessor, hmerged, overwrite, hsame]
  · by_cases hinputRange : input.lo ≤ key ∧ key ≤ input.hi
    · have hmerged : predecessor.range.val.lo ≤ key ∧
          key ≤ max predecessor.range.val.hi input.hi :=
        ⟨hstart.trans hinputRange.1, hinputRange.2.trans (le_max_right _ _)⟩
      change (if predecessor.range.val.lo ≤ key ∧
          key ≤ max predecessor.range.val.hi input.hi then
          some predecessor.value else runsToFunction suffix key) = _
      rw [if_pos hmerged]
      simp [overwrite, hinputRange, hsame]
    · have hmerged : ¬ (predecessor.range.val.lo ≤ key ∧
          key ≤ max predecessor.range.val.hi input.hi) := by
        intro h
        rcases le_max_iff.mp h.2 with hhi | hhi
        · exact hpredecessor ⟨h.1, hhi⟩
        · by_cases hlo : input.lo ≤ key
          · exact hinputRange ⟨hlo, hhi⟩
          · exact hpredecessor ⟨h.1, by omega⟩
      change (if predecessor.range.val.lo ≤ key ∧
          key ≤ max predecessor.range.val.hi input.hi then
          some predecessor.value else runsToFunction suffix key) = _
      rw [if_neg hmerged]
      simp [overwrite, hinputRange, hpredecessor]

private lemma predecessorSplit_preserves_overwrite {Value : Type*}
    (predecessor : Run Value) (suffix : List (Run Value))
    (input : IntRange) (value : Value) (hinput : input.lo ≤ input.hi)
    (hstart : predecessor.range.val.lo < input.lo)
    (_hoverlap : input.lo ≤ predecessor.range.val.hi)
    (hextends : input.hi < predecessor.range.val.hi) :
    runsToFunction
        (leftResidualBefore input.lo predecessor hstart ::
          { range := ⟨input, hinput⟩, value := value } ::
          rightResidualAfter input.hi predecessor hextends :: suffix) =
      overwrite (runsToFunction (predecessor :: suffix)) input value := by
  funext key
  simp only [runsToFunction_cons]
  by_cases hleft : predecessor.range.val.lo ≤ key ∧ key ≤ input.lo - 1
  · have hpredecessor :
        predecessor.range.val.lo ≤ key ∧ key ≤ predecessor.range.val.hi := by omega
    have hinputRange : ¬ (input.lo ≤ key ∧ key ≤ input.hi) := by omega
    simp [leftResidualBefore, hleft, hpredecessor, hinputRange, overwrite]
  · by_cases hinputRange : input.lo ≤ key ∧ key ≤ input.hi
    · simp [leftResidualBefore, hleft, hinputRange, overwrite]
    · have hequiv :
          (input.hi + 1 ≤ key ∧ key ≤ predecessor.range.val.hi) ↔
            (predecessor.range.val.lo ≤ key ∧ key ≤ predecessor.range.val.hi) := by
        constructor <;> intro h
        · exact ⟨by omega, h.2⟩
        · exact ⟨by omega, h.2⟩
      simp [leftResidualBefore, rightResidualAfter, hleft, hinputRange,
        hequiv, overwrite]

private lemma predecessorTrim_preserves_overwrite {Value : Type*}
    (predecessor : Run Value) (suffix : List (Run Value))
    (input : IntRange) (value : Value) (hinput : input.lo ≤ input.hi)
    (hstart : predecessor.range.val.lo < input.lo)
    (hnoGap : ¬ IntRange.NR.before predecessor.range (⟨input, hinput⟩ : NR))
    (hcover : predecessor.range.val.hi ≤ input.hi) :
    runsToFunction
        (leftResidualBefore input.lo predecessor hstart ::
          { range := ⟨input, hinput⟩, value := value } :: suffix) =
      overwrite (runsToFunction (predecessor :: suffix)) input value := by
  have hmutation := predecessorTrim_preserves_toFunction predecessor input value
    hinput hstart hnoGap hcover
  funext key
  simp only [runsToFunction_cons]
  by_cases hleft : predecessor.range.val.lo ≤ key ∧ key ≤ input.lo - 1
  · have hpredecessor :
        predecessor.range.val.lo ≤ key ∧ key ≤ predecessor.range.val.hi := by
      change ¬ (predecessor.range.val.hi + 1 < input.lo) at hnoGap
      omega
    have hinputRange : ¬ (input.lo ≤ key ∧ key ≤ input.hi) := by omega
    convert congrFun hmutation key using 1 <;>
      simp [runsToFunction_cons, leftResidualBefore, hleft, hpredecessor,
        hinputRange, overwrite]
  · by_cases hinputRange : input.lo ≤ key ∧ key ≤ input.hi
    · convert congrFun hmutation key using 1 <;>
        simp [runsToFunction_cons, leftResidualBefore, hleft, hinputRange,
          overwrite]
    · have hpredecessor : ¬
          (predecessor.range.val.lo ≤ key ∧ key ≤ predecessor.range.val.hi) := by
        change ¬ (predecessor.range.val.hi + 1 < input.lo) at hnoGap
        omega
      simp [leftResidualBefore, hleft, hinputRange, hpredecessor, overwrite]

private lemma scanForward_unchanged_false_of_strict_lower
    {Value : Type*} [DecidableEq Value]
    (pending : Run Value) (suffix : List (Run Value)) (stored : Bool)
    (hstrict : ∀ run ∈ suffix, pending.range.val.lo < run.range.val.lo) :
    (scanForward pending stored suffix).unchanged = false := by
  induction suffix generalizing pending with
  | nil => simp [scanForward]
  | cons next rest ih =>
      have hnext : pending.range.val.lo < next.range.val.lo :=
        hstrict next (by simp)
      have hrest : ∀ run ∈ rest, pending.range.val.lo < run.range.val.lo := by
        intro run hrun
        exact hstrict run (by simp [hrun])
      rw [scanForward]
      simp only [show ¬ next.range.val.lo = pending.range.val.lo by omega,
        decide_false, Bool.and_false]
      generalize haction : classifyForward pending.range.val.hi pending.value next = action
      cases action with
      | none => rfl
      | some action =>
          cases action with
          | mergeSame =>
              apply ih (mergeForward pending next)
              simpa [mergeForward] using hrest
          | deleteOverwritten => exact ih pending hrest
          | keepRightResidual residual => rfl

private lemma scanForward_unchanged_toFunction {Value : Type*} [DecidableEq Value]
    (pending : Run Value) (suffix : List (Run Value))
    (hcanonical : Canonical suffix)
    (hlower : ∀ run ∈ suffix, pending.range.val.lo ≤ run.range.val.lo)
    (hunchanged : (scanForward pending false suffix).unchanged = true) :
    runsToFunction suffix = runsToFunction (pending :: suffix) := by
  cases suffix with
  | nil => simp [scanForward] at hunchanged
  | cons next rest =>
      have hlowerNext : pending.range.val.lo ≤ next.range.val.lo :=
        hlower next (by simp)
      have hstrictRest : ∀ run ∈ rest,
          pending.range.val.lo < run.range.val.lo := by
        intro run hrun
        exact hlowerNext.trans_lt
          (Run.before_lo_lt (List.rel_of_pairwise_cons hcanonical hrun))
      by_cases hexact : (next.range.val.lo = pending.range.val.lo ∧
          next.value = pending.value) ∧ pending.range.val.hi ≤ next.range.val.hi
      · exact sameValueExactCover_toFunction pending next rest
          hexact.1.1 hexact.1.2.symm hexact.2
      · simp [scanForward, hexact] at hunchanged
        generalize haction : classifyForward pending.range.val.hi pending.value next = action
          at hunchanged
        cases action with
        | none => simp at hunchanged
        | some action =>
            cases action with
            | mergeSame =>
                have hfalse := scanForward_unchanged_false_of_strict_lower
                  (mergeForward pending next) rest false (by
                    simpa [mergeForward] using hstrictRest)
                simp [hfalse] at hunchanged
            | deleteOverwritten =>
                have hfalse := scanForward_unchanged_false_of_strict_lower
                  pending rest false hstrictRest
                simp [hfalse] at hunchanged
            | keepRightResidual residual => simp at hunchanged

private lemma gapInsertion_preserves_canonical_and_overwrite
    {Value : Type*} [DecidableEq Value]
    (left right : List (Run Value)) (input : IntRange) (value : Value)
    (hinput : input.lo ≤ input.hi)
    (hcanonicalLeft : Canonical left) (hcanonicalRight : Canonical right)
    (hleftFresh : ∀ run ∈ left,
      Run.before run { range := ⟨input, hinput⟩, value := value })
    (hleftRight : ∀ l ∈ left, ∀ r ∈ right, Run.before l r)
    (hlowerRight : ∀ run ∈ right, input.lo ≤ run.range.val.lo)
    (hleftOfInput : ∀ run ∈ left, run.range.val.hi < input.lo) :
    let fresh : Run Value := { range := ⟨input, hinput⟩, value := value }
    let scan := scanForward fresh false right
    let output := if scan.unchanged then left ++ right
      else left ++ scanOutput scan
    Canonical output ∧
      runsToFunction output =
        overwrite (runsToFunction (left ++ right)) input value := by
  dsimp only
  let fresh : Run Value := { range := ⟨input, hinput⟩, value := value }
  have hscan := scanForward_preserves_canonical_and_overwrite fresh right false
    hcanonicalRight (by simpa [fresh] using hlowerRight)
  change Canonical
      (if (scanForward fresh false right).unchanged then left ++ right
       else left ++ scanOutput (scanForward fresh false right)) ∧
    runsToFunction
      (if (scanForward fresh false right).unchanged then left ++ right
       else left ++ scanOutput (scanForward fresh false right)) =
      overwrite (runsToFunction (left ++ right)) input value
  by_cases hunchanged : (scanForward fresh false right).unchanged = true
  · simp only [hunchanged, ↓reduceIte]
    refine ⟨List.pairwise_append.mpr
      ⟨hcanonicalLeft, hcanonicalRight, hleftRight⟩, ?_⟩
    have htail : runsToFunction right =
        overwrite (runsToFunction right) input value :=
      (scanForward_unchanged_toFunction fresh right hcanonicalRight
        (by simpa [fresh] using hlowerRight) hunchanged).trans (by
          simpa [fresh] using
            insertedSuffix_toFunction right input value hinput hlowerRight)
    exact prependLeft_preserves_overwrite left right right input value
      hleftOfInput htail
  · simp only [hunchanged, Bool.false_eq_true, ↓reduceIte]
    have hleftScan : ∀ l ∈ left,
        ∀ r ∈ scanOutput (scanForward fresh false right), Run.before l r := by
      intro l hl
      apply scanForward_preserves_left_boundary l fresh right false
      · exact hleftFresh l hl
      · exact hleftRight l hl
    refine ⟨List.pairwise_append.mpr
      ⟨hcanonicalLeft, hscan.1, hleftScan⟩, ?_⟩
    have htail : runsToFunction (scanOutput (scanForward fresh false right)) =
        overwrite (runsToFunction right) input value :=
      hscan.2.trans (by
        simpa [fresh] using
          insertedSuffix_toFunction right input value hinput hlowerRight)
    exact prependLeft_preserves_overwrite left right
      (scanOutput (scanForward fresh false right)) input value hleftOfInput htail

private theorem internalAddDMapRuns_preserves_canonical_and_overwrite
    {Value : Type*} [DecidableEq Value]
    (runs : List (Run Value)) (input : IntRange) (value : Value)
    (hinput : input.lo ≤ input.hi) (hcanonical : Canonical runs) :
    Canonical (internalAddDMapRuns runs input value hinput) ∧
      runsToFunction (internalAddDMapRuns runs input value hinput) =
        overwrite (runsToFunction runs) input value := by
  unfold internalAddDMapRuns
  dsimp only
  split <;> rename_i hprev
  · let gap := lowerBoundGap input.lo runs
    let fresh : Run Value := { range := ⟨input, hinput⟩, value := value }
    have hgap := lowerBoundGap_decomposition runs input.lo hcanonical
    have hdecomp : runs = gap.left ++ gap.right := by
      simpa [gap] using hgap.1
    have hleftEmpty : gap.left = [] := by
      apply List.getLast?_eq_none_iff.mp
      simpa [gap, CursorGap.peekPrev] using hprev
    have hrightRuns : gap.right = runs := by
      simpa [hleftEmpty] using hdecomp.symm
    have hcanonicalRight : Canonical gap.right := by
      simpa [hrightRuns] using hcanonical
    have hlowerRight : ∀ run ∈ gap.right, input.lo ≤ run.range.val.lo :=
      hgap.2.2
    have hresult := gapInsertion_preserves_canonical_and_overwrite
      gap.left gap.right input value hinput
      (by simp [hleftEmpty]) hcanonicalRight
      (by simp [hleftEmpty]) (by simp [hleftEmpty]) hlowerRight
      (by simp [hleftEmpty])
    simpa [gap, fresh, hprev, CursorGap.peekPrev, hleftEmpty, hrightRuns]
      using hresult
  · rename_i predecessor
    let gap := lowerBoundGap input.lo runs
    let fresh : Run Value := { range := ⟨input, hinput⟩, value := value }
    have hgap := lowerBoundGap_decomposition runs input.lo hcanonical
    have hdecomp : runs = gap.left ++ gap.right := by
      simpa [gap] using hgap.1
    have hcanonicalWhole : Canonical (gap.left ++ gap.right) := by
      simpa [hdecomp] using hcanonical
    have hcanonicalLeft : Canonical gap.left :=
      (List.pairwise_append.mp hcanonicalWhole).1
    have hcanonicalRight : Canonical gap.right :=
      (List.pairwise_append.mp hcanonicalWhole).2.1
    have hcross : ∀ left ∈ gap.left, ∀ right ∈ gap.right,
        Run.before left right :=
      (List.pairwise_append.mp hcanonicalWhole).2.2
    have hlowerRight : ∀ run ∈ gap.right, input.lo ≤ run.range.val.lo :=
      hgap.2.2
    have hpredecessorMem : predecessor ∈ gap.left :=
      List.mem_of_mem_getLast? (by simpa [gap, CursorGap.peekPrev] using hprev)
    have hpredecessorStart : predecessor.range.val.lo < input.lo :=
      hgap.2.1 predecessor hpredecessorMem
    have hleftDecomp : gap.left.dropLast ++ [predecessor] = gap.left :=
      List.dropLast_append_getLast? predecessor
        (by simpa [gap, CursorGap.peekPrev] using hprev)
    have hrunsDecomp : gap.left.dropLast ++ predecessor :: gap.right = runs := by
      calc
        gap.left.dropLast ++ predecessor :: gap.right = gap.left ++ gap.right := by
          rw [← hleftDecomp]
          simp [List.append_assoc]
        _ = runs := hdecomp.symm
    have hcanonicalInitPredecessor :
        Canonical (gap.left.dropLast ++ [predecessor]) := by
      simpa [hleftDecomp] using hcanonicalLeft
    have hcanonicalInit : Canonical gap.left.dropLast :=
      (List.pairwise_append.mp hcanonicalInitPredecessor).1
    have hinitBeforePredecessor : ∀ run ∈ gap.left.dropLast,
        Run.before run predecessor := by
      intro run hrun
      exact (List.pairwise_append.mp hcanonicalInitPredecessor).2.2
        run hrun predecessor (by simp)
    have hpredecessorRight : ∀ run ∈ gap.right,
        Run.before predecessor run :=
      fun run hrun => hcross predecessor hpredecessorMem run hrun
    have hinitLeftOfInput : ∀ run ∈ gap.left.dropLast,
        run.range.val.hi < input.lo := by
      intro run hrun
      exact (Run.before_hi_lt (hinitBeforePredecessor run hrun)).trans
        hpredecessorStart
    have hinsertion (hpredecessorFresh : Run.before predecessor fresh) :
        let scan := scanForward fresh false gap.right
        Canonical (if scan.unchanged then runs
          else gap.left ++ scanOutput scan) ∧
        runsToFunction (if scan.unchanged then runs
          else gap.left ++ scanOutput scan) =
          overwrite (runsToFunction runs) input value := by
      have hleftFresh : ∀ run ∈ gap.left, Run.before run fresh := by
        intro run hrun
        rw [← hleftDecomp] at hrun
        rcases List.mem_append.mp hrun with hrun | hrun
        · exact Run.before_trans (hinitBeforePredecessor run hrun)
            hpredecessorFresh
        · simp only [List.mem_singleton] at hrun
          subst run
          exact hpredecessorFresh
      have hleftOfInput : ∀ run ∈ gap.left,
          run.range.val.hi < input.lo := by
        intro run hrun
        simpa [fresh] using Run.before_hi_lt (hleftFresh run hrun)
      have hresult := gapInsertion_preserves_canonical_and_overwrite
        gap.left gap.right input value hinput hcanonicalLeft hcanonicalRight
        (by simpa [fresh] using hleftFresh) hcross hlowerRight hleftOfInput
      simpa [hdecomp] using hresult
    have hcoveredResult (hsame : predecessor.value = value)
        (hnoGap : input.lo ≤ predecessor.range.val.hi + 1)
        (hcovered : input.hi ≤ predecessor.range.val.hi) :
        Canonical runs ∧ runsToFunction runs =
          overwrite (runsToFunction runs) input value := by
      refine ⟨hcanonical, ?_⟩
      have htail : runsToFunction (predecessor :: gap.right) =
          overwrite (runsToFunction (predecessor :: gap.right)) input value := by
        funext key
        by_cases hin : input.lo ≤ key ∧ key ≤ input.hi
        · have hpredecessorContains :
              predecessor.range.val.lo ≤ key ∧ key ≤ predecessor.range.val.hi := by
            omega
          simp [runsToFunction_cons, overwrite, hin, hpredecessorContains, hsame]
        · simp [overwrite, hin]
      have hall := prependLeft_preserves_overwrite gap.left.dropLast
        (predecessor :: gap.right) (predecessor :: gap.right)
        input value hinitLeftOfInput htail
      simpa [hrunsDecomp] using hall
    have hmergeResult (hsame : predecessor.value = value)
        (hnoGap : input.lo ≤ predecessor.range.val.hi + 1)
        (hnotCovered : ¬ input.hi ≤ predecessor.range.val.hi) :
        let grown := mergeForward predecessor fresh
        let scan := scanForward grown true gap.right
        Canonical (if scan.unchanged then runs
          else gap.left.dropLast ++ scanOutput scan) ∧
        runsToFunction (if scan.unchanged then runs
          else gap.left.dropLast ++ scanOutput scan) =
          overwrite (runsToFunction runs) input value := by
      dsimp only
      let grown := mergeForward predecessor fresh
      have hlowerGrown : ∀ run ∈ gap.right,
          grown.range.val.lo ≤ run.range.val.lo := by
        intro run hrun
        simpa [grown, mergeForward] using
          hpredecessorStart.le.trans (hlowerRight run hrun)
      have hscan := scanForward_preserves_canonical_and_overwrite
        grown gap.right true hcanonicalRight hlowerGrown
      have hstrictRight : ∀ run ∈ gap.right,
          grown.range.val.lo < run.range.val.lo := by
        intro run hrun
        simpa [grown, mergeForward] using
          hpredecessorStart.trans_le (hlowerRight run hrun)
      have hnotUnchanged := scanForward_unchanged_false_of_strict_lower
        grown gap.right true hstrictRight
      change Canonical
          (if (scanForward grown true gap.right).unchanged then runs
           else gap.left.dropLast ++ scanOutput (scanForward grown true gap.right)) ∧
        runsToFunction
          (if (scanForward grown true gap.right).unchanged then runs
           else gap.left.dropLast ++ scanOutput (scanForward grown true gap.right)) =
          overwrite (runsToFunction runs) input value
      simp only [hnotUnchanged, Bool.false_eq_true, ↓reduceIte]
      have hinitGrown : ∀ run ∈ gap.left.dropLast,
          Run.before run grown := by
        intro run hrun
        have hip := hinitBeforePredecessor run hrun
        constructor
        · simpa [grown, mergeForward, Run.disjointBefore] using hip.1
        · intro hvalue
          apply hip.2
          simpa [grown, mergeForward] using hvalue
      have hinitScan : ∀ left ∈ gap.left.dropLast,
          ∀ right ∈ scanOutput (scanForward grown true gap.right),
            Run.before left right := by
        intro left hleft
        apply scanForward_preserves_left_boundary left grown gap.right true
        · exact hinitGrown left hleft
        · intro run hrun
          exact hcross left (by
            rw [← hleftDecomp]
            simp [hleft]) run hrun
      refine ⟨List.pairwise_append.mpr
        ⟨hcanonicalInit, hscan.1, hinitScan⟩, ?_⟩
      have htail :
          runsToFunction (scanOutput (scanForward grown true gap.right)) =
            overwrite (runsToFunction (predecessor :: gap.right)) input value :=
        hscan.2.trans (by
          simpa [grown, fresh] using
            predecessorMerge_preserves_overwrite predecessor gap.right input value
              hinput hpredecessorStart.le hsame hnoGap)
      have hall := prependLeft_preserves_overwrite gap.left.dropLast
        (predecessor :: gap.right)
        (scanOutput (scanForward grown true gap.right))
        input value hinitLeftOfInput htail
      simpa [grown, hrunsDecomp] using hall
    by_cases hoverlap : input.lo ≤ predecessor.range.val.hi
    · by_cases hsame : predecessor.value = value
      · by_cases hcovered : input.hi ≤ predecessor.range.val.hi
        · simpa [gap, fresh, hprev, CursorGap.peekPrev, classifyPredecessor,
            hoverlap, hsame, hcovered] using
            hcoveredResult hsame (by omega) hcovered
        · simpa [gap, fresh, hprev, CursorGap.peekPrev, classifyPredecessor,
            hoverlap, hsame, hcovered] using
            hmergeResult hsame (by omega) hcovered
      · by_cases hextends : input.hi < predecessor.range.val.hi
        · let left := leftResidualBefore input.lo predecessor hpredecessorStart
          let residual := rightResidualAfter input.hi predecessor hextends
          have hleftFresh : Run.before left fresh := by
            constructor
            · simp [left, leftResidualBefore, fresh, Run.disjointBefore]
            · intro hvalue
              exact False.elim (hsame (by
                simpa [left, leftResidualBefore, fresh] using hvalue))
          have hfreshResidual : Run.before fresh residual := by
            constructor
            · simp [fresh, residual, rightResidualAfter, Run.disjointBefore]
            · intro hvalue
              exact False.elim (hsame (by
                simpa [fresh, residual, rightResidualAfter] using hvalue.symm))
          have hresidualRight : ∀ run ∈ gap.right,
              Run.before residual run := by
            intro run hrun
            have hpr := hpredecessorRight run hrun
            constructor
            · simpa [residual, rightResidualAfter, Run.disjointBefore] using hpr.1
            · intro hvalue
              apply hpr.2
              simpa [residual, rightResidualAfter] using hvalue
          have htailCanonical :
              Canonical (left :: fresh :: residual :: gap.right) := by
            have hresidualCanonical : Canonical (residual :: gap.right) :=
              List.pairwise_cons.mpr ⟨hresidualRight, hcanonicalRight⟩
            have hfreshFollowing : ∀ run ∈ residual :: gap.right,
                Run.before fresh run := by
              intro run hrun
              rcases List.mem_cons.mp hrun with rfl | hrun
              · exact hfreshResidual
              · exact Run.before_trans hfreshResidual (hresidualRight run hrun)
            have hfreshCanonical : Canonical (fresh :: residual :: gap.right) :=
              List.pairwise_cons.mpr ⟨hfreshFollowing, hresidualCanonical⟩
            apply List.pairwise_cons.mpr
            refine ⟨?_, hfreshCanonical⟩
            intro run hrun
            rcases List.mem_cons.mp hrun with rfl | hrun
            · exact hleftFresh
            · exact Run.before_trans hleftFresh
                (List.rel_of_pairwise_cons hfreshCanonical hrun)
          have hinitLeft : ∀ run ∈ gap.left.dropLast, Run.before run left := by
            intro run hrun
            have hip := hinitBeforePredecessor run hrun
            constructor
            · simpa [left, leftResidualBefore, Run.disjointBefore] using hip.1
            · intro hvalue
              apply hip.2
              simpa [left, leftResidualBefore] using hvalue
          have hinitTail : ∀ run ∈ gap.left.dropLast,
              ∀ following ∈ left :: fresh :: residual :: gap.right,
                Run.before run following := by
            intro run hrun following hfollowing
            rcases List.mem_cons.mp hfollowing with rfl | hfollowing
            · exact hinitLeft run hrun
            · exact Run.before_trans (hinitLeft run hrun)
                (List.rel_of_pairwise_cons htailCanonical hfollowing)
          have hcanonicalOutput :
              Canonical (gap.left.dropLast ++ left :: fresh :: residual :: gap.right) :=
            List.pairwise_append.mpr
              ⟨hcanonicalInit, htailCanonical, hinitTail⟩
          have htail :
              runsToFunction (left :: fresh :: residual :: gap.right) =
                overwrite (runsToFunction (predecessor :: gap.right)) input value := by
            simpa [left, residual, fresh] using
              predecessorSplit_preserves_overwrite predecessor gap.right input value hinput
                hpredecessorStart hoverlap hextends
          have hall := prependLeft_preserves_overwrite gap.left.dropLast
            (predecessor :: gap.right) (left :: fresh :: residual :: gap.right)
            input value hinitLeftOfInput htail
          simpa [gap, left, residual, fresh, hprev, CursorGap.peekPrev,
            classifyPredecessor, hoverlap, hsame, hextends, hpredecessorStart,
            hrunsDecomp] using
            And.intro hcanonicalOutput hall
        · let left := leftResidualBefore input.lo predecessor hpredecessorStart
          have hnoGap : ¬ IntRange.NR.before predecessor.range
              (⟨input, hinput⟩ : NR) := by
            change ¬ (predecessor.range.val.hi + 1 < input.lo)
            omega
          have hleftFresh : Run.before left fresh := by
            constructor
            · simp [left, leftResidualBefore, fresh, Run.disjointBefore]
            · intro hvalue
              exact False.elim (hsame (by
                simpa [left, leftResidualBefore, fresh] using hvalue))
          have hleftRight : ∀ run ∈ gap.right, Run.before left run := by
            intro run hrun
            have hpr := hpredecessorRight run hrun
            constructor
            · unfold Run.disjointBefore
              simp only [left, leftResidualBefore]
              have := hlowerRight run hrun
              omega
            · intro hvalue
              have hgapValue := hpr.2 (by
                simpa [left, leftResidualBefore] using hvalue)
              unfold IntRange.NR.before at hgapValue ⊢
              simp only [left, leftResidualBefore]
              omega
          have hscan := scanForward_preserves_canonical_and_overwrite
            fresh gap.right false hcanonicalRight
              (by simpa [fresh] using hlowerRight)
          by_cases hunchanged :
              (scanForward fresh false gap.right).unchanged = true
          · have htailCanonical : Canonical (left :: gap.right) :=
              List.pairwise_cons.mpr ⟨hleftRight, hcanonicalRight⟩
            have hinitLeft : ∀ run ∈ gap.left.dropLast, Run.before run left := by
              intro run hrun
              have hip := hinitBeforePredecessor run hrun
              constructor
              · simpa [left, leftResidualBefore, Run.disjointBefore] using hip.1
              · intro hvalue
                apply hip.2
                simpa [left, leftResidualBefore] using hvalue
            have hinitTail : ∀ run ∈ gap.left.dropLast,
                ∀ following ∈ left :: gap.right, Run.before run following := by
              intro run hrun following hfollowing
              rcases List.mem_cons.mp hfollowing with rfl | hfollowing
              · exact hinitLeft run hrun
              · exact Run.before_trans (hinitLeft run hrun)
                  (hleftRight following hfollowing)
            refine ⟨?_, ?_⟩
            · simpa [gap, fresh, hprev, CursorGap.peekPrev, classifyPredecessor,
                hoverlap, hsame, hextends, hpredecessorStart, hunchanged, left] using
                (List.pairwise_append.mpr
                  ⟨hcanonicalInit, htailCanonical, hinitTail⟩)
            · have hrightNoChange := scanForward_unchanged_toFunction
                fresh gap.right hcanonicalRight
                  (by simpa [fresh] using hlowerRight) hunchanged
              have hleftRightFunction : runsToFunction (left :: gap.right) =
                  runsToFunction (left :: fresh :: gap.right) := by
                funext key
                simp only [runsToFunction_cons]
                split
                · rfl
                · simpa only [runsToFunction_cons] using congrFun hrightNoChange key
              have hreplace := predecessorTrim_preserves_overwrite predecessor gap.right
                input value hinput hpredecessorStart hnoGap (by omega)
              have htail := hleftRightFunction.trans hreplace
              have hall := prependLeft_preserves_overwrite gap.left.dropLast
                (predecessor :: gap.right) (left :: gap.right)
                input value hinitLeftOfInput htail
              simpa [gap, fresh, hprev, CursorGap.peekPrev, classifyPredecessor,
                hoverlap, hsame, hextends, hpredecessorStart, hunchanged, left,
                hrunsDecomp] using hall
          · have hleftScan := scanForward_preserves_left_boundary
              left fresh gap.right false hleftFresh hleftRight
            have htailCanonical :
                Canonical (left :: scanOutput (scanForward fresh false gap.right)) :=
              List.pairwise_cons.mpr ⟨hleftScan, hscan.1⟩
            have hinitLeft : ∀ run ∈ gap.left.dropLast, Run.before run left := by
              intro run hrun
              have hip := hinitBeforePredecessor run hrun
              constructor
              · simpa [left, leftResidualBefore, Run.disjointBefore] using hip.1
              · intro hvalue
                apply hip.2
                simpa [left, leftResidualBefore] using hvalue
            have hinitTail : ∀ run ∈ gap.left.dropLast,
                ∀ following ∈ left :: scanOutput (scanForward fresh false gap.right),
                  Run.before run following := by
              intro run hrun following hfollowing
              rcases List.mem_cons.mp hfollowing with rfl | hfollowing
              · exact hinitLeft run hrun
              · exact Run.before_trans (hinitLeft run hrun)
                  (hleftScan following hfollowing)
            have hleftScanFunction :
                runsToFunction
                    (left :: scanOutput (scanForward fresh false gap.right)) =
                  runsToFunction (left :: fresh :: gap.right) := by
              funext key
              simp only [runsToFunction_cons]
              split
              · rfl
              · simpa only [runsToFunction_cons] using congrFun hscan.2 key
            have hreplace := predecessorTrim_preserves_overwrite predecessor gap.right
              input value hinput hpredecessorStart hnoGap (by omega)
            have htail := hleftScanFunction.trans hreplace
            have hall := prependLeft_preserves_overwrite gap.left.dropLast
              (predecessor :: gap.right)
              (left :: scanOutput (scanForward fresh false gap.right))
              input value hinitLeftOfInput htail
            simpa [gap, fresh, hprev, CursorGap.peekPrev, classifyPredecessor,
              hoverlap, hsame, hextends, hpredecessorStart, hunchanged, left,
              hrunsDecomp] using
              And.intro (List.pairwise_append.mpr
                ⟨hcanonicalInit, htailCanonical, hinitTail⟩) hall
    · by_cases htouch : predecessor.range.val.hi + 1 = input.lo
      · by_cases hsame : predecessor.value = value
        · by_cases hcovered : input.hi ≤ predecessor.range.val.hi
          · simpa [gap, fresh, hprev, CursorGap.peekPrev, classifyPredecessor,
              hoverlap, htouch, hsame, hcovered] using
              hcoveredResult hsame (by omega) hcovered
          · simpa [gap, fresh, hprev, CursorGap.peekPrev, classifyPredecessor,
              hoverlap, htouch, hsame, hcovered] using
              hmergeResult hsame (by omega) hcovered
        · have hpredecessorFresh : Run.before predecessor fresh := by
            refine ⟨?_, ?_⟩
            · unfold Run.disjointBefore
              change predecessor.range.val.hi < input.lo
              omega
            · intro heq
              exact False.elim (hsame (by simpa [fresh] using heq))
          simpa [gap, fresh, hprev, CursorGap.peekPrev, classifyPredecessor,
            hoverlap, htouch, hsame] using hinsertion hpredecessorFresh
      · have hpredecessorFresh : Run.before predecessor fresh := by
          have hgapStrict : predecessor.range.val.hi + 1 < input.lo := by omega
          refine ⟨?_, ?_⟩
          · unfold Run.disjointBefore
            change predecessor.range.val.hi < input.lo
            omega
          · intro _
            simpa [fresh, IntRange.NR.before] using hgapStrict
        have hnotTouchSame : ¬
            (predecessor.range.val.hi + 1 = input.lo ∧ predecessor.value = value) := by
          simp [htouch]
        simpa [gap, fresh, hprev, CursorGap.peekPrev, classifyPredecessor,
          hoverlap, htouch, hnotTouchSame] using hinsertion hpredecessorFresh

/-- Cursor-shaped map insertion, with canonicality proved at construction. -/
def internalAddDMap {Value : Type*} [DecidableEq Value]
    (map : RangeMapBlaze Value) (input : IntRange) (value : Value) :
    RangeMapBlaze Value := by
  if h : input.hi < input.lo then
    exact map
  else
    have hinput : input.lo ≤ input.hi := by omega
    exact ⟨internalAddDMapRuns map.runs input value hinput,
      (internalAddDMapRuns_preserves_canonical_and_overwrite
        map.runs input value hinput map.canonical).1⟩

/-- Cursor-shaped insertion has exact pointwise overwrite semantics. -/
theorem internalAddDMap_toFunction {Value : Type*} [DecidableEq Value]
    (map : RangeMapBlaze Value) (input : IntRange) (value : Value) :
    (internalAddDMap map input value).toFunction =
      overwrite map.toFunction input value := by
  unfold internalAddDMap
  split <;> rename_i h
  · exact (overwrite_eq_of_hi_lt_lo map.toFunction input value h).symm
  · dsimp only [toFunction]
    exact (internalAddDMapRuns_preserves_canonical_and_overwrite
      map.runs input value (by omega) map.canonical).2

/-! ## Algo DMap with cached length -/

/- DMapLen keeps represented-key cardinalities as `Nat` throughout.  The
cache invariant supplies the non-underflow facts needed by each subtraction. -/

/-- The public result of cursor-shaped map insertion with explicit cached key
cardinality. -/
structure DMapLenResult (Value : Type*) where
  mapResult : RangeMapBlaze Value
  cachedLength : Nat

/-- Proof-free run-list output used by the cached cursor model. -/
private structure DMapLenRawResult (Value : Type*) where
  runs : List (Run Value)
  cachedLength : Nat

/-- The cursor scan state plus the absolute cache after all removed successors
have been subtracted. The pending and optional residual are counted later only
when the production cursor inserts them. -/
private structure DMapLenScanResult (Value : Type*) where
  pending : Run Value
  rightResidual : Option (Run Value)
  remaining : List (Run Value)
  unchanged : Bool
  cachedLength : Nat

/-- Count the pending run exactly when it is not already stored to the left of
the cursor. -/
private def countPendingIfFresh {Value : Type*}
    (pendingIsStored : Bool) (cachedLength : Nat) (pending : Run Value) : Nat :=
  if pendingIsStored then cachedLength
  else cachedLength + pending.cardinality

/-- Cursor-local forward scan with the production add/subtract ordering.

Every consumed successor is subtracted in full. A stored pending run receives
only a right-extension addition; a fresh pending run and a returned right
residual remain uncounted until final cursor insertion. -/
private def scanForwardDMapLen {Value : Type*} [DecidableEq Value]
    (pending : Run Value) (pendingIsStored : Bool) (cachedLength : Nat) :
    List (Run Value) → DMapLenScanResult Value
  | [] =>
      { pending, rightResidual := none, remaining := [], unchanged := false,
        cachedLength }
  | next :: rest =>
      if !pendingIsStored && next.range.val.lo = pending.range.val.lo &&
          next.value = pending.value && pending.range.val.hi ≤ next.range.val.hi then
        { pending, rightResidual := none, remaining := next :: rest,
          unchanged := true, cachedLength }
      else
        match classifyForward pending.range.val.hi pending.value next with
        | none =>
            { pending, rightResidual := none, remaining := next :: rest,
              unchanged := false, cachedLength }
        | some .mergeSame =>
            let merged := mergeForward pending next
            let afterRemoval := cachedLength - next.cardinality
            let afterExtension :=
              if pendingIsStored && pending.range.val.hi < next.range.val.hi then
                afterRemoval + IntRange.rightExtensionCardinality
                  pending.range.val.hi next.range.val.hi
              else afterRemoval
            scanForwardDMapLen merged pendingIsStored afterExtension rest
        | some .deleteOverwritten =>
            scanForwardDMapLen pending pendingIsStored
              (cachedLength - next.cardinality) rest
        | some (.keepRightResidual residual) =>
            { pending, rightResidual := some residual, remaining := rest,
              unchanged := false,
              cachedLength := cachedLength - next.cardinality }
termination_by suffix => suffix.length

/-- Perform the cursor insertions that follow a completed forward scan. -/
private def finishDMapLenScan {Value : Type*}
    (pendingIsStored : Bool) (scan : DMapLenScanResult Value) :
    DMapLenRawResult Value :=
  if scan.unchanged then
    ⟨scan.remaining, scan.cachedLength⟩
  else
    let afterPending := countPendingIfFresh
      pendingIsStored scan.cachedLength scan.pending
    let afterResidual := scan.rightResidual.elim afterPending
      (fun residual => afterPending + residual.cardinality)
    ⟨scanOutput {
        pending := scan.pending
        rightResidual := scan.rightResidual
        remaining := scan.remaining
        unchanged := scan.unchanged },
      afterResidual⟩

/-- Proof-free DMapLen control flow. This is `internalAddDMapRuns` plus the
absolute cache mutations of the production Rust cursor path. -/
private def internalAddDMapLenRaw {Value : Type*} [DecidableEq Value]
    (runs : List (Run Value)) (cachedLength : Nat)
    (input : IntRange) (value : Value) (hinput : input.lo ≤ input.hi) :
    DMapLenRawResult Value :=
  let gap := lowerBoundGap input.lo runs
  let fresh : Run Value := ⟨⟨input, hinput⟩, value⟩
  match gap.peekPrev with
  | none =>
      let scan := scanForwardDMapLen fresh false cachedLength gap.right
      if scan.unchanged then ⟨runs, cachedLength⟩
      else
        let finished := finishDMapLenScan false scan
        ⟨gap.left ++ finished.runs, finished.cachedLength⟩
  | some predecessor =>
      match classifyPredecessor input.lo input.hi value predecessor with
      | .unaffected =>
          let scan := scanForwardDMapLen fresh false cachedLength gap.right
          if scan.unchanged then ⟨runs, cachedLength⟩
          else
            let finished := finishDMapLenScan false scan
            ⟨gap.left ++ finished.runs, finished.cachedLength⟩
      | .mergeSame =>
          if input.hi ≤ predecessor.range.val.hi then ⟨runs, cachedLength⟩
          else
            let grown := mergeForward predecessor fresh
            let afterExtension := cachedLength +
              IntRange.rightExtensionCardinality predecessor.range.val.hi input.hi
            let scan := scanForwardDMapLen grown true afterExtension gap.right
            if scan.unchanged then ⟨runs, cachedLength⟩
            else
              let finished := finishDMapLenScan true scan
              ⟨gap.left.dropLast ++ finished.runs, finished.cachedLength⟩
      | .trimDifferent left rightResidual =>
          let afterTrim := cachedLength -
            IntRange.cardinality { lo := input.lo, hi := predecessor.range.val.hi }
          match rightResidual with
          | some residual =>
              ⟨gap.left.dropLast ++ left :: fresh :: residual :: gap.right,
                afterTrim + fresh.cardinality +
                  residual.cardinality⟩
          | none =>
              let scan := scanForwardDMapLen fresh false afterTrim gap.right
              if scan.unchanged then
                ⟨gap.left.dropLast ++ left :: gap.right, afterTrim⟩
              else
                let finished := finishDMapLenScan false scan
                ⟨gap.left.dropLast ++ left :: finished.runs,
                  finished.cachedLength⟩

/-- Trimming a predecessor removes exactly the overwritten tail and retains
the left residual. -/
private lemma leftResidualBefore_cardinality
    {Value : Type*} (start : Int) (run : Run Value)
    (hstart : run.range.val.lo < start) (hoverlap : start ≤ run.range.val.hi) :
    run.cardinality =
      (leftResidualBefore start run hstart).cardinality +
        IntRange.cardinality { lo := start, hi := run.range.val.hi } := by
  simpa [Run.cardinality, leftResidualBefore] using
    IntRange.cardinality_eq_left_residual_add_tail
      run.range.val.lo start run.range.val.hi hstart hoverlap

/-- Removing an overhanging successor and reinserting its right residual
partitions the old successor into overwritten and retained cardinalities. -/
private lemma rightResidualAfter_cardinality
    {Value : Type*} (stop : Int) (run : Run Value)
    (hlower : run.range.val.lo ≤ stop) (hextends : stop < run.range.val.hi) :
    run.cardinality =
      IntRange.cardinality { lo := run.range.val.lo, hi := stop } +
        (rightResidualAfter stop run hextends).cardinality := by
  simpa [Run.cardinality, rightResidualAfter] using
    IntRange.cardinality_eq_prefix_add_right_residual
      run.range.val.lo stop run.range.val.hi hlower hextends

/-- A predecessor surrounding the input is partitioned into its left residual,
the overwritten input, and its right residual. -/
private lemma twoSidedPredecessorSplit_cardinality
    {Value : Type*} (input : IntRange) (run : Run Value)
    (hstart : run.range.val.lo < input.lo)
    (hnonempty : input.lo ≤ input.hi) (hextends : input.hi < run.range.val.hi) :
    run.cardinality =
      (leftResidualBefore input.lo run hstart).cardinality + input.cardinality +
        (rightResidualAfter input.hi run hextends).cardinality := by
  simpa [Run.cardinality, leftResidualBefore, rightResidualAfter] using
    IntRange.cardinality_eq_left_add_middle_add_right
      run.range.val.lo run.range.val.hi input hstart hnonempty hextends

/-- The cached forward cursor scan erases exactly to Algo DMap's scan, stops at
the same continuation flag, and preserves an absolute-cache decomposition over
the untouched base.

The `unchanged` agreement is what lets the raw dispatcher align its own
early-return branches with `internalAddDMapRuns`: the exact same-value cover
short-circuit is the only place the two recursions can stop differently. The
cache invariant says that above the untouched `base`, the running cache counts
exactly the suffix plus the pending run when that run is already stored. Rust's
documented cursor invariant that a stored pending starts strictly before every
suffix run is not needed here, because the fast path is already guarded by
`!pendingIsStored`. -/
private theorem scanForwardDMapLen_preserves_correspondence_and_cardinality
    {Value : Type*} [DecidableEq Value]
    (pending : Run Value) (pendingIsStored : Bool)
    (suffix : List (Run Value)) (cachedLength : Nat) :
    let scan := scanForwardDMapLen
      pending pendingIsStored cachedLength suffix
    let algo := scanForward pending pendingIsStored suffix
    let finished := finishDMapLenScan pendingIsStored scan
    scan.unchanged = algo.unchanged ∧
      finished.runs = scanOutput algo ∧
      ∀ base, cachedLength = base +
          (if pendingIsStored then pending.cardinality else 0) +
            runsCardinality suffix →
        finished.cachedLength = base +
          runsCardinality finished.runs := by
  induction suffix generalizing pending cachedLength with
  | nil =>
      cases pendingIsStored <;>
        simp [scanForwardDMapLen, scanForward, finishDMapLenScan,
          countPendingIfFresh, scanOutput]
  | cons next rest ih =>
      unfold scanForwardDMapLen scanForward
      split <;> rename_i hfast
      · cases hstored : pendingIsStored <;>
          simp [hstored, finishDMapLenScan, scanOutput] at hfast ⊢
      · generalize haction :
          classifyForward pending.range.val.hi pending.value next = action
        cases action with
        | none =>
            cases hstored : pendingIsStored <;>
              simp [finishDMapLenScan, countPendingIfFresh,
                scanOutput, runsCardinality_cons] <;>
              omega
        | some action =>
            cases action with
            | mergeSame =>
                simp only
                let merged := mergeForward pending next
                let afterRemoval := cachedLength - next.cardinality
                let afterExtension :=
                  if pendingIsStored && pending.range.val.hi < next.range.val.hi then
                    afterRemoval + IntRange.rightExtensionCardinality
                      pending.range.val.hi next.range.val.hi
                  else afterRemoval
                have hrec := ih merged afterExtension
                refine ⟨hrec.1, hrec.2.1, ?_⟩
                intro base hcache
                have hremoved : next.cardinality ≤ cachedLength := by
                  simp only [runsCardinality_cons] at hcache
                  omega
                apply hrec.2.2 base
                cases hstored : pendingIsStored
                · simp [afterExtension, afterRemoval, hstored,
                    runsCardinality_cons] at hcache ⊢
                  omega
                · simp only [hstored, if_true] at hcache ⊢
                  by_cases hextend : pending.range.val.hi < next.range.val.hi
                  · have hmergedCard : merged.cardinality = pending.cardinality +
                        IntRange.rightExtensionCardinality
                          pending.range.val.hi next.range.val.hi := by
                      simpa [merged, mergeForward, Run.cardinality,
                        max_eq_right hextend.le] using
                        (IntRange.NR.cardinality_eq_add_right_extension
                          pending.range merged.range (by simp [merged, mergeForward])
                          (by simpa [merged, mergeForward,
                            max_eq_right hextend.le]))
                    simp [afterExtension, afterRemoval, hstored, hextend,
                      hmergedCard, runsCardinality_cons] at hcache ⊢
                    omega
                  · have hmergedCard : merged.cardinality = pending.cardinality := by
                      simp [merged, mergeForward, Run.cardinality,
                        max_eq_left (not_lt.mp hextend)]
                    simp [afterExtension, afterRemoval, hstored, hextend,
                      hmergedCard, runsCardinality_cons] at hcache ⊢
                    omega
            | deleteOverwritten =>
                simp only
                have hrec := ih pending
                  (cachedLength - next.cardinality)
                refine ⟨hrec.1, hrec.2.1, ?_⟩
                intro base hcache
                have hremoved : next.cardinality ≤ cachedLength := by
                  simp only [runsCardinality_cons] at hcache
                  omega
                apply hrec.2.2 base
                simp only [runsCardinality_cons] at hcache ⊢
                omega
            | keepRightResidual residual =>
                simp only
                refine ⟨True.intro, rfl, ?_⟩
                intro base hcache
                have hremoved : next.cardinality ≤ cachedLength := by
                  simp only [runsCardinality_cons] at hcache
                  omega
                simp only [runsCardinality_cons] at hcache
                have hafterRemoval : cachedLength - next.cardinality =
                      (base + if pendingIsStored then pending.cardinality else 0) +
                        runsCardinality rest := by
                  apply (Nat.sub_eq_iff_eq_add hremoved).mpr
                  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcache
                cases hstored : pendingIsStored <;>
                  simp [finishDMapLenScan, countPendingIfFresh,
                    scanOutput, runsCardinality_cons, hafterRemoval,
                    hstored] <;>
                  omega

/-- Erasing DMapLen bookkeeping gives exactly Algo DMap's raw run output. -/
private theorem internalAddDMapLenRaw_corresponds
    {Value : Type*} [DecidableEq Value]
    (runs : List (Run Value)) (cachedLength : Nat)
    (input : IntRange) (value : Value) (hinput : input.lo ≤ input.hi) :
    (internalAddDMapLenRaw runs cachedLength input value hinput).runs =
      internalAddDMapRuns runs input value hinput := by
  unfold internalAddDMapLenRaw internalAddDMapRuns
  dsimp only
  split <;> rename_i hprev
  · have hscan := scanForwardDMapLen_preserves_correspondence_and_cardinality
      ({ range := ⟨input, hinput⟩, value := value } : Run Value)
        false (lowerBoundGap input.lo runs).right cachedLength
    rw [hscan.1, hscan.2.1]
    split <;> rfl
  · rename_i predecessor
    generalize haction :
      classifyPredecessor input.lo input.hi value predecessor = action
    cases action with
    | unaffected =>
        simp only
        have hscan := scanForwardDMapLen_preserves_correspondence_and_cardinality
          ({ range := ⟨input, hinput⟩, value := value } : Run Value)
            false (lowerBoundGap input.lo runs).right cachedLength
        simp only [hscan.1, hscan.2.1]
        split <;> rfl
    | mergeSame =>
        simp only
        by_cases hcovered : input.hi ≤ predecessor.range.val.hi
        · simp [hcovered]
        · simp only [hcovered, if_false]
          have hscan := scanForwardDMapLen_preserves_correspondence_and_cardinality
            (mergeForward predecessor
              ({ range := ⟨input, hinput⟩, value := value } : Run Value))
              true (lowerBoundGap input.lo runs).right
                (cachedLength +
                IntRange.rightExtensionCardinality predecessor.range.val.hi input.hi)
          rw [hscan.1, hscan.2.1]
          split <;> rfl
    | trimDifferent left rightResidual =>
        simp only
        cases rightResidual with
        | some residual => rfl
        | none =>
            simp only
            have hscan := scanForwardDMapLen_preserves_correspondence_and_cardinality
              ({ range := ⟨input, hinput⟩, value := value } : Run Value)
                false (lowerBoundGap input.lo runs).right
                  (cachedLength - IntRange.cardinality
                  { lo := input.lo, hi := predecessor.range.val.hi })
            rw [hscan.1, hscan.2.1]
            split <;> rfl

/-- Branch-local cursor bookkeeping computes the raw output cardinality when
the incoming absolute cache is valid. -/
private theorem internalAddDMapLenRaw_preserves_cardinality
    {Value : Type*} [DecidableEq Value]
    (runs : List (Run Value)) (cachedLength : Nat)
    (input : IntRange) (value : Value) (hinput : input.lo ≤ input.hi)
    (hcanonical : Canonical runs)
    (hlength : cachedLength = runsCardinality runs) :
    (internalAddDMapLenRaw runs cachedLength input value hinput).cachedLength =
      runsCardinality
        (internalAddDMapLenRaw runs cachedLength input value hinput).runs := by
  unfold internalAddDMapLenRaw
  dsimp only
  let gap := lowerBoundGap input.lo runs
  let fresh : Run Value := { range := ⟨input, hinput⟩, value := value }
  have hgap := lowerBoundGap_decomposition runs input.lo hcanonical
  have hdecomp : runs = gap.left ++ gap.right := by
    simpa [gap] using hgap.1
  have hleftStarts : ∀ run ∈ gap.left, run.range.val.lo < input.lo := by
    simpa [gap] using hgap.2.1
  cases hprev : gap.peekPrev with
  | none =>
      have hleftEmpty : gap.left = [] :=
        List.getLast?_eq_none_iff.mp (by
          simpa [CursorGap.peekPrev] using hprev)
      have hrightRuns : gap.right = runs := by
        simpa [hleftEmpty] using hdecomp.symm
      have hscan := scanForwardDMapLen_preserves_correspondence_and_cardinality
        fresh false gap.right cachedLength
      have hscanCache := hscan.2.2 0 (by
        simp [hrightRuns, hlength])
      by_cases hunchanged :
          (scanForwardDMapLen fresh false cachedLength gap.right).unchanged = true
      · simpa [fresh, gap, hunchanged] using hlength
      · simpa [fresh, gap, hunchanged, hleftEmpty,
          runsCardinality_append] using hscanCache
  | some predecessor =>
      have hpredecessorMem : predecessor ∈ gap.left :=
        List.mem_of_mem_getLast? (by
          simpa [CursorGap.peekPrev] using hprev)
      have hpredecessorStart : predecessor.range.val.lo < input.lo :=
        hleftStarts predecessor hpredecessorMem
      let init := gap.left.dropLast
      have hleftDecomp : init ++ [predecessor] = gap.left := by
        simpa [init] using List.dropLast_append_getLast? predecessor
          (by simpa [CursorGap.peekPrev] using hprev)
      have hlengthParts : cachedLength =
          runsCardinality init + predecessor.cardinality +
            runsCardinality gap.right := by
        rw [hlength, hdecomp, ← hleftDecomp,
          runsCardinality_append, runsCardinality_append]
        simp [Nat.add_assoc]
      generalize haction :
        classifyPredecessor input.lo input.hi value predecessor = action
      cases action with
      | unaffected =>
          simp only [haction]
          have hscan := scanForwardDMapLen_preserves_correspondence_and_cardinality
            fresh false gap.right cachedLength
          have hscanCache := hscan.2.2
            (runsCardinality gap.left) (by
              rw [hlength, hdecomp, runsCardinality_append]
              simp)
          by_cases hunchanged :
              (scanForwardDMapLen fresh false cachedLength gap.right).unchanged = true
          · simpa [fresh, gap, hunchanged] using hlength
          · simpa [fresh, gap, hunchanged,
              runsCardinality_append] using hscanCache
      | mergeSame =>
          simp only [haction]
          by_cases hcovered : input.hi ≤ predecessor.range.val.hi
          · simpa [hcovered] using hlength
          · simp only [hcovered, if_false]
            let grown := mergeForward predecessor fresh
            let afterExtension := cachedLength +
              IntRange.rightExtensionCardinality predecessor.range.val.hi input.hi
            have hextends : predecessor.range.val.hi < input.hi :=
              not_le.mp hcovered
            have hgrownCard : grown.cardinality = predecessor.cardinality +
                IntRange.rightExtensionCardinality predecessor.range.val.hi input.hi := by
              simpa [grown, fresh, mergeForward, Run.cardinality,
                max_eq_right hextends.le] using
                (IntRange.NR.cardinality_eq_add_right_extension
                  predecessor.range grown.range (by simp [grown, mergeForward])
                  (by simpa [grown, fresh, mergeForward,
                    max_eq_right hextends.le]))
            have hscan := scanForwardDMapLen_preserves_correspondence_and_cardinality
              grown true gap.right afterExtension
            have hscanCache := hscan.2.2 (runsCardinality init) (by
              simp [afterExtension, hgrownCard, hlengthParts]
              omega)
            by_cases hunchanged :
                (scanForwardDMapLen grown true afterExtension gap.right).unchanged = true
            · have hunchanged' : (scanForwardDMapLen
                  (mergeForward predecessor
                    ({ range := ⟨input, hinput⟩, value := value } : Run Value)) true
                  (cachedLength + IntRange.rightExtensionCardinality
                    predecessor.range.val.hi input.hi)
                  (lowerBoundGap input.lo runs).right).unchanged = true := by
                simpa [grown, fresh, afterExtension, gap] using hunchanged
              simp only [hunchanged', if_true]
              exact hlength
            · have hunchanged' : ¬ (scanForwardDMapLen
                  (mergeForward predecessor
                    ({ range := ⟨input, hinput⟩, value := value } : Run Value)) true
                  (cachedLength + IntRange.rightExtensionCardinality
                    predecessor.range.val.hi input.hi)
                  (lowerBoundGap input.lo runs).right).unchanged = true := by
                simpa [grown, fresh, afterExtension, gap] using hunchanged
              simp only [hunchanged']
              simpa [fresh, grown, afterExtension, gap, init,
                runsCardinality_append] using hscanCache
      | trimDifferent left rightResidual =>
          simp only [haction]
          let removed := IntRange.cardinality
            { lo := input.lo, hi := predecessor.range.val.hi }
          have htrim : predecessor.cardinality = left.cardinality + removed := by
            unfold classifyPredecessor at haction
            dsimp only at haction
            split at haction <;> try contradiction
            split at haction <;> try contradiction
            split at haction <;> try contradiction
            all_goals
              rename_i htop hsame hextends
              have hoverlap : input.lo ≤ predecessor.range.val.hi := by
                simp [hsame] at htop
                exact htop
              injection haction with hleftEq hresidualEq
              subst left
              simpa [removed] using leftResidualBefore_cardinality
                input.lo predecessor hpredecessorStart hoverlap
          have hremoved : removed ≤ cachedLength := by
            omega
          let afterTrim := cachedLength - removed
          cases rightResidual with
          | some residual =>
              simp only
              have hthree : predecessor.cardinality =
                  left.cardinality + fresh.cardinality + residual.cardinality := by
                unfold classifyPredecessor at haction
                dsimp only at haction
                split at haction <;> try contradiction
                split at haction <;> try contradiction
                by_cases hextends : input.hi < predecessor.range.val.hi
                · simp [hextends] at haction
                  rcases haction with ⟨hleftEq, hresidualEq⟩
                  subst left
                  subst residual
                  simpa [fresh, Run.cardinality] using
                    twoSidedPredecessorSplit_cardinality input predecessor
                      hpredecessorStart hinput hextends
                · simp [hextends] at haction
              change afterTrim + fresh.cardinality + residual.cardinality =
                runsCardinality (init ++ left :: fresh :: residual :: gap.right)
              simp only [runsCardinality_append, runsCardinality_cons]
              simp only [afterTrim] at hlengthParts hthree ⊢
              omega
          | none =>
              simp only
              have htrimCache : afterTrim =
                  (runsCardinality init + left.cardinality) +
                    runsCardinality gap.right := by
                apply (Nat.sub_eq_iff_eq_add hremoved).mpr
                omega
              have hscan := scanForwardDMapLen_preserves_correspondence_and_cardinality
                fresh false gap.right afterTrim
              have hscanCache := hscan.2.2
                (runsCardinality init + left.cardinality)
                (by simpa using htrimCache)
              by_cases hunchanged :
                  (scanForwardDMapLen fresh false afterTrim gap.right).unchanged = true
              · have hunchanged' : (scanForwardDMapLen
                    ({ range := ⟨input, hinput⟩, value := value } : Run Value) false
                    (cachedLength - IntRange.cardinality
                      { lo := input.lo, hi := predecessor.range.val.hi })
                    (lowerBoundGap input.lo runs).right).unchanged = true := by
                  simpa [fresh, afterTrim, removed, gap] using hunchanged
                simp only [hunchanged', if_true]
                change afterTrim = runsCardinality (init ++ left :: gap.right)
                simp only [runsCardinality_append, runsCardinality_cons]
                simpa [Nat.add_assoc] using htrimCache
              · have hunchanged' : ¬ (scanForwardDMapLen
                    ({ range := ⟨input, hinput⟩, value := value } : Run Value) false
                    (cachedLength - IntRange.cardinality
                      { lo := input.lo, hi := predecessor.range.val.hi })
                    (lowerBoundGap input.lo runs).right).unchanged = true := by
                  simpa [fresh, afterTrim, removed, gap] using hunchanged
                simp only [hunchanged']
                change (finishDMapLenScan false
                    (scanForwardDMapLen fresh false afterTrim gap.right)).cachedLength =
                  runsCardinality (init ++ left :: (finishDMapLenScan false
                    (scanForwardDMapLen fresh false afterTrim gap.right)).runs)
                simpa [runsCardinality_append, Nat.add_assoc] using hscanCache

/-- Cursor-shaped map insertion with production explicit cached key count. -/
def internalAddDMapLen {Value : Type*} [DecidableEq Value]
    (map : RangeMapBlaze Value) (cachedLength : Nat)
    (input : IntRange) (value : Value) : DMapLenResult Value := by
  if h : input.hi < input.lo then
    exact ⟨map, cachedLength⟩
  else
    have hinput : input.lo ≤ input.hi := by omega
    let raw := internalAddDMapLenRaw map.runs cachedLength
      input value hinput
    have hruns : raw.runs = internalAddDMapRuns map.runs input value hinput :=
      internalAddDMapLenRaw_corresponds
        map.runs cachedLength input value hinput
    have hcanonical : Canonical raw.runs := by
      rw [hruns]
      exact (internalAddDMapRuns_preserves_canonical_and_overwrite
        map.runs input value hinput map.canonical).1
    exact ⟨⟨raw.runs, hcanonical⟩, raw.cachedLength⟩

/-- DMapLen's map component is exactly Algo DMap's result representation. -/
theorem internalAddDMapLen_mapResult {Value : Type*} [DecidableEq Value]
    (map : RangeMapBlaze Value) (cachedLength : Nat)
    (input : IntRange) (value : Value) :
    (internalAddDMapLen map cachedLength input value).mapResult =
      internalAddDMap map input value := by
  unfold internalAddDMapLen internalAddDMap
  by_cases hempty : input.hi < input.lo
  · simp [hempty]
  · simp only [dif_neg hempty]
    rw [RangeMapBlaze.mk.injEq]
    exact internalAddDMapLenRaw_corresponds
      map.runs cachedLength input value (by omega)

/-- A valid incoming cached key count remains valid after DMapLen insertion. -/
theorem internalAddDMapLen_cachedLength {Value : Type*} [DecidableEq Value]
    (map : RangeMapBlaze Value) (cachedLength : Nat)
    (input : IntRange) (value : Value)
    (hlength : cachedLength = map.cardinality) :
    (internalAddDMapLen map cachedLength input value).cachedLength =
      (internalAddDMapLen map cachedLength input value).mapResult.cardinality := by
  unfold internalAddDMapLen
  by_cases hempty : input.hi < input.lo
  · simpa [hempty, RangeMapBlaze.cardinality] using hlength
  · simp only [dif_neg hempty]
    have hraw := internalAddDMapLenRaw_preserves_cardinality map.runs
      cachedLength
      input value (by omega) map.canonical
      (by simpa [RangeMapBlaze.cardinality] using hlength)
    simpa [RangeMapBlaze.cardinality] using hraw

/-- DMapLen inherits Algo DMap's exact pointwise overwrite semantics. -/
theorem internalAddDMapLen_toFunction {Value : Type*} [DecidableEq Value]
    (map : RangeMapBlaze Value) (cachedLength : Nat)
    (input : IntRange) (value : Value) :
    (internalAddDMapLen map cachedLength input value).mapResult.toFunction =
      overwrite map.toFunction input value := by
  rw [internalAddDMapLen_mapResult]
  exact internalAddDMap_toFunction map input value

end RangeMapBlaze
