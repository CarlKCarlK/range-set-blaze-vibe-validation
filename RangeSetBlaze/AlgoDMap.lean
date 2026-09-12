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

private def insertBefore {Value : Type*}
    (gap : CursorGap Value) (pending : Run Value) (right : List (Run Value)) :
    List (Run Value) := gap.left ++ pending :: right

private def replaceStoredPredecessor {Value : Type*}
    (gap : CursorGap Value) (pending : Run Value) (right : List (Run Value)) :
    List (Run Value) := gap.left.dropLast ++ pending :: right

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

private theorem lowerBoundGap_spec
    {Value : Type*} (runs : List (Run Value)) (start : Int)
    (hcanonical : Canonical runs) :
    let gap := lowerBoundGap start runs
    runs = gap.left ++ gap.right ∧
      (∀ run ∈ gap.left, run.range.val.lo < start) ∧
      (∀ run ∈ gap.right, start ≤ run.range.val.lo) := by
  sorry

private theorem cursor_predecessor_mutation_spec
    {Value : Type*} [DecidableEq Value]
    (predecessor : Run Value) (input : IntRange) (value : Value)
    (hinput : input.lo ≤ input.hi)
    (hleft : predecessor.range.val.lo < input.lo)
    (hcover : predecessor.range.val.hi ≤ input.hi) :
    runsToFunction
        ([leftResidualBefore input.lo predecessor hleft,
          ⟨⟨input, hinput⟩, value⟩] : List (Run Value)) =
      overwrite (runsToFunction ([predecessor] : List (Run Value))) input value := by
  sorry

private theorem scanForward_preserves_canonical_and_overwrite
    {Value : Type*} [DecidableEq Value]
    (pending : Run Value) (suffix : List (Run Value)) (stored : Bool)
    (hcanonical : Canonical suffix)
    (hlower : ∀ run ∈ suffix, pending.range.val.lo ≤ run.range.val.lo) :
    Canonical (scanOutput (scanForward pending stored suffix)) ∧
      runsToFunction (scanOutput (scanForward pending stored suffix)) =
        runsToFunction (pending :: suffix) := by
  sorry

private theorem internalAddDMapRuns_preserves_canonical_and_overwrite
    {Value : Type*} [DecidableEq Value]
    (runs : List (Run Value)) (input : IntRange) (value : Value)
    (hinput : input.lo ≤ input.hi) (hcanonical : Canonical runs) :
    Canonical (internalAddDMapRuns runs input value hinput) ∧
      runsToFunction (internalAddDMapRuns runs input value hinput) =
        overwrite (runsToFunction runs) input value := by
  sorry

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

end RangeMapBlaze
