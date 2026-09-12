import RangeSetBlaze.AlgoC

namespace RangeSetBlaze

open IntRange
open IntRange.NR
open scoped IntRange.NR

/-!
Algo CLen is Algo C with the production cached element count made explicit.
The input `cachedLength` models the `RangeSetBlaze::len` field before insertion;
the result carries both the new set and the branch-locally updated count.

The executable code intentionally uses `Nat` subtraction in the same order as
Rust: swallowed stored ranges are subtracted before newly represented pieces
are added. Phase 2 will prove that canonical inputs make every subtraction
valid and that the result is the mathematical cardinality.
-/

/-- The externally useful result of cached-length insertion. -/
structure CLenResult where
  setResult : RangeSetBlaze
  cachedLength : Nat
  deriving Repr

/-- Proof-free output used while constructing the canonical result. -/
private structure CLenRawResult where
  ranges : List NR
  cachedLength : Nat

/-- A small local constructor for a proved-nonempty range. -/
private def mkNR (lo hi : Int) (h : lo ≤ hi) : NR :=
  ⟨{ lo := lo, hi := hi }, h⟩

/-- The production expression `safe_len(old_end..=new_end - 1)`. Under the
strict endpoint inequalities at its call sites, this equals `new_end-old_end`.
-/
private def extensionCardinality (oldEnd newEnd : Int) : Nat :=
  IntRange.cardinality { lo := oldEnd, hi := newEnd - 1 }

/-- Forward merge state. `cachedLength` has already had every swallowed stored
range subtracted, but does not yet include the final extension beyond the
original pending end. -/
private structure ForwardCLenResult where
  current : NR
  pending : List NR
  cachedLength : Nat

/-- Scan and swallow touching/overlapping successors. This is the CLen form of
Algo C's `deleteExtraNRs_loop`; each swallowed old range is immediately removed
from the cached element count, as in Rust's `delete_extra`. -/
private def deleteExtraCLenLoop
    (current : NR) (pending : List NR) (cachedLength : Nat) : ForwardCLenResult :=
  match pending with
  | [] => ⟨current, [], cachedLength⟩
  | next :: tail =>
      if next.val.lo ≤ current.val.hi + 1 then
        let newHi := max current.val.hi next.val.hi
        let merged := mkNR current.val.lo newHi
          (current.property.trans (le_max_left _ _))
        deleteExtraCLenLoop merged tail
          (cachedLength - next.val.cardinality)
      else
        ⟨current, next :: tail, cachedLength⟩

/-- Finish Rust's `delete_extra` accounting by adding the part by which the
merged range extends beyond the end passed to that helper. -/
private def finishDeleteExtraCLen
    (current : NR) (pending : List NR) (originalEnd : Int)
    (cachedLength : Nat) : ForwardCLenResult :=
  let scanned := deleteExtraCLenLoop current pending cachedLength
  if originalEnd < scanned.current.val.hi then
    { scanned with
      cachedLength := scanned.cachedLength +
        extensionCardinality originalEnd scanned.current.val.hi }
  else
    scanned

/-- The `internal_add2` path: insert the new range, run `delete_extra`, then
add the inserted range's inclusive length. -/
private def freshInsertCLen
    (ranges : List NR) (input : NR) (cachedLength : Nat) : CLenRawResult :=
  let split := List.span (fun nr => decide (nr.val.lo < input.val.lo)) ranges
  let before := split.fst
  let after := split.snd
  let scanned := finishDeleteExtraCLen input after input.val.hi cachedLength
  ⟨before ++ scanned.current :: scanned.pending,
    scanned.cachedLength + input.val.cardinality⟩

/-- The predecessor-extension path. The first addition is exactly Rust's
`safe_len(end_before..=end-1)` update; successor deletion and final extension
are then handled by `finishDeleteExtraCLen`. -/
private def extendPredecessorCLen
    (before after : List NR) (predecessor input : NR)
    (cachedLength : Nat) : CLenRawResult :=
  let extendedHi := max predecessor.val.hi input.val.hi
  let extended := mkNR predecessor.val.lo extendedHi
    (predecessor.property.trans (le_max_left _ _))
  let lengthAfterExtension := cachedLength +
    extensionCardinality predecessor.val.hi input.val.hi
  let scanned := finishDeleteExtraCLen extended after input.val.hi lengthAfterExtension
  ⟨before.dropLast ++ scanned.current :: scanned.pending, scanned.cachedLength⟩

/-- Proof-free CLen control flow. It mirrors Algo C's empty, no-predecessor,
gap, covered, and extend-predecessor branches while threading the cached count.
-/
private def internalAddCLenRaw
    (ranges : List NR) (cachedLength : Nat) (r : IntRange) : CLenRawResult :=
  if hempty : r.hi < r.lo then
    ⟨ranges, cachedLength⟩
  else
    let input : NR := ⟨r, not_lt.mp hempty⟩
    let split := List.span (fun nr => decide (nr.val.lo ≤ r.lo)) ranges
    let before := split.fst
    let after := split.snd
    match before.getLast? with
    | none => freshInsertCLen ranges input cachedLength
    | some predecessor =>
        if predecessor.val.hi + 1 < r.lo then
          freshInsertCLen ranges input cachedLength
        else if r.hi ≤ predecessor.val.hi then
          ⟨ranges, cachedLength⟩
        else
          extendPredecessorCLen before after predecessor input cachedLength

/-! ## Phase 1 proof skeleton

The two branch-local theorems isolate the new arithmetic. The correspondence
theorem isolates executable equality with Algo C. The top-level cardinality
theorem will compose the branch-local results in Phase 2.
-/

/-- Fresh insertion's subtract-then-add bookkeeping computes the cardinality
of its output when entered at a genuine canonical insertion boundary. -/
private theorem freshInsertCLen_preserves_cardinality
    (ranges : List NR) (input : NR) (cachedLength : Nat)
    (hcanonical : List.Pairwise NR.before ranges)
    (hgap :
      let before := (List.span
        (fun nr => decide (nr.val.lo < input.val.lo)) ranges).fst
      before = [] ∨
        ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < input.val.lo)
    (hlength : cachedLength = rangesCardinality ranges) :
    (freshInsertCLen ranges input cachedLength).cachedLength =
      rangesCardinality (freshInsertCLen ranges input cachedLength).ranges := by
  sorry

/-- Extending a selected predecessor, deleting swallowed successors, and
adding only newly exposed tails computes the cardinality of the output. -/
private theorem extendPredecessorCLen_preserves_cardinality
    (ranges before after : List NR) (predecessor input : NR)
    (cachedLength : Nat)
    (hcanonical : List.Pairwise NR.before ranges)
    (hdecomp : List.span (fun nr => decide (nr.val.lo ≤ input.val.lo)) ranges =
      (before, after))
    (hlast : before.getLast? = some predecessor)
    (hnogap : ¬ (predecessor.val.hi + 1 < input.val.lo))
    (hextend : predecessor.val.hi < input.val.hi)
    (hlength : cachedLength = rangesCardinality ranges) :
    (extendPredecessorCLen before after predecessor input cachedLength).cachedLength =
      rangesCardinality
        (extendPredecessorCLen before after predecessor input cachedLength).ranges := by
  sorry

/-- Erasing CLen's bookkeeping yields exactly the existing Algo C list result.
This is representation equality, not merely equality of represented sets. -/
private theorem internalAddCLenRaw_corresponds
    (s : RangeSetBlaze) (cachedLength : Nat) (r : IntRange) :
    (internalAddCLenRaw s.ranges cachedLength r).ranges =
      (internalAddC s r).ranges := by
  sorry

/-- The top-level bookkeeping contract, assuming the incoming cache is valid. -/
private theorem internalAddCLenRaw_preserves_cardinality
    (s : RangeSetBlaze) (cachedLength : Nat) (r : IntRange)
    (hlength : cachedLength = s.cardinality) :
    (internalAddCLenRaw s.ranges cachedLength r).cachedLength =
      rangesCardinality (internalAddCLenRaw s.ranges cachedLength r).ranges := by
  sorry

/-- Algo CLen insertion with an explicit incoming cached element count. -/
def internalAddCLen
    (s : RangeSetBlaze) (cachedLength : Nat) (r : IntRange) : CLenResult :=
  let raw := internalAddCLenRaw s.ranges cachedLength r
  let setResult : RangeSetBlaze :=
    ⟨raw.ranges, by
      rw [internalAddCLenRaw_corresponds s cachedLength r]
      exact (internalAddC s r).canonical⟩
  ⟨setResult, raw.cachedLength⟩

/-- CLen's set component is exactly Algo C's result. -/
theorem internalAddCLen_setResult
    (s : RangeSetBlaze) (cachedLength : Nat) (r : IntRange) :
    (internalAddCLen s cachedLength r).setResult = internalAddC s r := by
  unfold internalAddCLen
  dsimp only
  rw [RangeSetBlaze.mk.injEq]
  exact internalAddCLenRaw_corresponds s cachedLength r

/-- A valid incoming cached count remains valid after CLen insertion. -/
theorem internalAddCLen_cachedLength
    (s : RangeSetBlaze) (cachedLength : Nat) (r : IntRange)
    (hlength : cachedLength = s.cardinality) :
    (internalAddCLen s cachedLength r).cachedLength =
      (internalAddCLen s cachedLength r).setResult.cardinality := by
  exact internalAddCLenRaw_preserves_cardinality s cachedLength r hlength

/-- CLen inherits Algo C's already-proved set semantics. -/
theorem internalAddCLen_toSet
    (s : RangeSetBlaze) (cachedLength : Nat) (r : IntRange) :
    (internalAddCLen s cachedLength r).setResult.toSet = s.toSet ∪ r.toSet := by
  rw [internalAddCLen_setResult]
  exact internalAddC_toSet s r

end RangeSetBlaze
