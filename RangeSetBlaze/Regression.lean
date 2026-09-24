import RangeSetBlaze.AlgoA
import RangeSetBlaze.AlgoB
import RangeSetBlaze.AlgoC
import RangeSetBlaze.AlgoD
import RangeSetBlaze.AlgoE
import RangeSetBlaze.PyIntRangeSet
import RangeSetBlaze.PyIntRangeSetState
import RangeSetBlaze.PyIntRangeSetCases

namespace RangeSetBlaze

open IntRange
open IntRange.NR
open scoped IntRange.NR

/-!
Executable regression examples are kept outside the algorithm modules so they
do not create conceptual dependencies between implementations.
The first examples assert concrete results without relying on Algo C.  The
remaining examples compare the concrete range lists of Algos A through E, and
the cached counts of CLen and ELen, across the insertion situations: empty
input, empty set, disjoint before/after, exact overlap, contained, containing,
left/right merge, adjacency on either side, and bridging several ranges.
-/

private def testNR (lo hi : Int) (h : lo ≤ hi := by omega) : NR :=
  ⟨{ lo := lo, hi := hi }, h⟩

private def testSet (ranges : List NR)
    (canonical : List.Pairwise NR.before ranges := by native_decide) : RangeSetBlaze :=
  ⟨ranges, canonical⟩

private def sameAcrossAlgorithms (s : RangeSetBlaze) (r : IntRange) : Bool :=
  (internalAddA s r).ranges == (internalAddB s r).ranges &&
  (internalAddB s r).ranges == (internalAddC s r).ranges &&
  (internalAddC s r).ranges == (internalAddD s r).ranges &&
  (internalAddD s r).ranges == (internalAddE s r).ranges

/-- Every implementation must agree, while ELen must also match the explicit
canonical ranges and cardinality, CLen's count, and its own result cardinality. -/
private def agrees (s : RangeSetBlaze) (r : IntRange)
    (expectedRanges : List NR) (expectedLength : Nat) : Bool :=
  let eLen := internalAddELen s s.cardinality r
  sameAcrossAlgorithms s r &&
    eLen.setResult.ranges == expectedRanges &&
    eLen.setResult.ranges == (internalAddE s r).ranges &&
    eLen.cachedLength == expectedLength &&
    eLen.cachedLength == (internalAddCLen s s.cardinality r).cachedLength &&
    eLen.cachedLength == eLen.setResult.cardinality

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

example : agrees (testSet [testNR 10 12]) { lo := 5, hi := 4 }
    [testNR 10 12] 3 := by native_decide
example : agrees (testSet []) { lo := 5, hi := 7 }
    [testNR 5 7] 3 := by native_decide
example : agrees (testSet [testNR 10 12]) { lo := 1, hi := 3 }
    [testNR 1 3, testNR 10 12] 6 := by native_decide
example : agrees (testSet [testNR 10 12]) { lo := 20, hi := 22 }
    [testNR 10 12, testNR 20 22] 6 := by native_decide
example : agrees (testSet [testNR 1 5, testNR 10 20]) { lo := 12, hi := 15 }
    [testNR 1 5, testNR 10 20] 16 := by native_decide
example : agrees (testSet [testNR 10 20, testNR 30 35]) { lo := 10, hi := 15 }
    [testNR 10 20, testNR 30 35] 17 := by native_decide
example : agrees (testSet [testNR 1 3, testNR 10 12]) { lo := 5, hi := 7 }
    [testNR 1 3, testNR 5 7, testNR 10 12] 9 := by native_decide
example : agrees (testSet [testNR 10 12, testNR 20 22]) { lo := 7, hi := 9 }
    [testNR 7 12, testNR 20 22] 9 := by native_decide
example : agrees
    (testSet [testNR 10 12, testNR 14 16, testNR 18 20, testNR 30 35])
    { lo := 7, hi := 18 } [testNR 7 20, testNR 30 35] 20 := by native_decide
example : agrees (testSet [testNR 1 5, testNR 10 12]) { lo := 4, hi := 7 }
    [testNR 1 7, testNR 10 12] 10 := by native_decide
example : agrees (testSet [testNR 1 5, testNR 8 10, testNR 20 22]) { lo := 4, hi := 7 }
    [testNR 1 10, testNR 20 22] 13 := by native_decide
example : agrees
    (testSet [testNR 1 5, testNR 8 10, testNR 13 15, testNR 30 35])
    { lo := 4, hi := 13 } [testNR 1 15, testNR 30 35] 21 := by native_decide
example : agrees (testSet [testNR 10 12]) { lo := 10, hi := 12 }
    [testNR 10 12] 3 := by native_decide
example : agrees (testSet [testNR 10 12]) { lo := 13, hi := 15 }
    [testNR 10 15] 6 := by native_decide
example : agrees (testSet [testNR 10 12, testNR 20 22]) { lo := 5, hi := 30 }
    [testNR 5 30] 26 := by native_decide
example : agrees (testSet [testNR 10 12, testNR 16 18]) { lo := 13, hi := 15 }
    [testNR 10 18] 9 := by native_decide

/-! ## PySnpTools `IntRangeSet._internal_add`

The generated cases record the real Python state after `_internal_add` —
`ranges()`, `_start_items`, and `_start_to_length` — for every
`(start, length)` in a window around several base sets, and after every call
of seeded random call sequences from `IntRangeSet()`.  Each call is checked
against both Lean models: the list model `internalAddPy` must produce Python's
`ranges()`, and the two-field model `PyIntRangeSet.internalAdd` must not raise
and must produce Python's `_start_items` and `_start_to_length`, and the
abstraction `storedRanges` of its result must be the list model's result.
Base-set cases start the two-field model from Python's own fields; sequences
run both Lean models in lockstep with Python.  The list model must also agree
with Algos A, C, and D on the inclusive input `[start, start + length - 1]`.
-/

-- BEGIN python-differential
-- `scripts/mutate_py_intrangeset_state.py` appends this region verbatim to
-- mutants of `PyIntRangeSetState.lean`, so it may use only the Python models
-- and the generated cases.
section PythonDifferential

open PyIntRangeSetCases

/-- The canonical range set for Python half-open ranges, if they are canonical. -/
private def ofHalfOpen (ranges : List (Int × Int)) : Option RangeSetBlaze :=
  let nrs := ranges.filterMap fun (start, stop) =>
    if h : start < stop then some (NR.ofStartStop start stop h) else none
  if h : nrs.length = ranges.length ∧ List.Pairwise NR.before nrs then
    some ⟨nrs, h.2⟩
  else
    none

/-- Python's `ranges()` view: half-open `(start, stop)` pairs. -/
private def toHalfOpen (s : RangeSetBlaze) : List (Int × Int) :=
  s.ranges.map fun nr => (nr.val.lo, nr.stop)

/-- Pair up a flattened `start stop start stop ...` list. -/
private def pairUp? : List Int → Option (List (Int × Int))
  | [] => some []
  | start :: stop :: rest => ((start, stop) :: ·) <$> pairUp? rest
  | [_] => none

/-- Space-separated integers; `none` if any token is not an integer. -/
private def parseInts? (text : String) : Option (List Int) :=
  if text.isEmpty then some [] else (text.splitOn " ").mapM String.toInt?

/-- A Python `IntRangeSet` state as generated: `ranges | items | dict`. -/
private structure PyObserved where
  ranges : List (Int × Int)
  items : List Int
  dict : List (Int × Int)

private def parseObserved? (text : String) : Option PyObserved :=
  match text.splitOn " | " with
  | [ranges, items, dict] => do
      pure ⟨← pairUp? (← parseInts? ranges), ← parseInts? items, ← pairUp? (← parseInts? dict)⟩
  | _ => none

/-- A case line `start length | ranges | items | dict`. -/
private def parseCase? (line : String) : Option (Int × Int × PyObserved) :=
  match line.splitOn " | " with
  | call :: state => do
      let [start, length] ← parseInts? call | none
      pure (start, length, ← parseObserved? (" | ".intercalate state))
  | [] => none

/-- Python's `self._start_to_length.get(k)`. -/
private def lookup (dict : List (Int × Int)) (k : Int) : Option Int :=
  (dict.find? (·.1 == k)).map (·.2)

/-- Python's two fields, as the two-field model's state. -/
private def PyObserved.toState (observed : PyObserved) : PyIntRangeSet :=
  ⟨observed.items, lookup observed.dict⟩

/-- The model's fields equal Python's: the same `_start_items`, and the same
`_start_to_length` at every key either could hold.  A model key outside
Python's is either an earlier key or one the call wrote, which is `start`
or an earlier key, so `earlierKeys` must include those. -/
private def fieldsMatch (py : PyIntRangeSet) (observed : PyObserved)
    (earlierKeys : List Int) : Bool :=
  py.startItems == observed.items &&
    (earlierKeys ++ observed.dict.map (·.1)).all fun k =>
      py.startToLength k == lookup observed.dict k

/-- One `_internal_add(start, length)` on both Lean models, checked against
Python's resulting state; returns the new Lean states. -/
private def pyStep (s : RangeSetBlaze) (py : PyIntRangeSet) (start length : Int)
    (observed : PyObserved) : Option (RangeSetBlaze × PyIntRangeSet) :=
  if h : 0 < length then
    let s' := internalAddPy s start length h
    match py.internalAdd start length with
    | none => none
    | some py' =>
        if toHalfOpen s' == observed.ranges &&
            fieldsMatch py' observed (start :: py.startItems) &&
            py'.storedRanges == s'.ranges then
          some (s', py')
        else
          none
  else
    none

/-- Every generated line of `cases` agrees, each starting from `base`. -/
private def pyCasesAgree (base cases : String) : Bool :=
  match parseObserved? base with
  | none => false
  | some observed =>
      match ofHalfOpen observed.ranges with
      | none => false
      | some s =>
          let lines := (cases.splitOn "\n").filter (· ≠ "")
          !lines.isEmpty && lines.all fun line =>
            match parseCase? line with
            | some (start, length, result) =>
                (pyStep s observed.toState start length result).isSome
            | none => false

/-- Run generated call sequences in lockstep; `new` restarts both Lean models
from `IntRangeSet()`. -/
private def pySequencesAgree : List String → RangeSetBlaze × PyIntRangeSet → Bool
  | [], _ => true
  | "new" :: rest, _ => pySequencesAgree rest (⟨[], .nil⟩, PyIntRangeSet.empty)
  | line :: rest, (s, py) =>
      match parseCase? line >>= fun (start, length, result) => pyStep s py start length result with
      | some next => pySequencesAgree rest next
      | none => false

example : pyCasesAgree pyBase0 pyCases0 ∧ pyCasesAgree pyBase1 pyCases1 ∧
    pyCasesAgree pyBase2 pyCases2 ∧ pyCasesAgree pyBase3 pyCases3 ∧
    pyCasesAgree pyBase4 pyCases4 := by native_decide

example : let lines := (pySequences.splitOn "\n").filter (· ≠ "")
    lines.head? = some "new" ∧ pySequencesAgree lines (⟨[], .nil⟩, PyIntRangeSet.empty) := by
  native_decide

end PythonDifferential
-- END python-differential

/-- The list model agrees with Algos A, C, and D on every generated case. -/
private def pyCrossAgrees (base cases : String) : Bool :=
  match parseObserved? base >>= fun observed => ofHalfOpen observed.ranges with
  | none => false
  | some s =>
      ((cases.splitOn "\n").filter (· ≠ "")).all fun line =>
        match parseCase? line with
        | some (start, length, _) =>
            if h : 0 < length then
              let input : IntRange := { lo := start, hi := start + length - 1 }
              let py := internalAddPy s start length h
              py.ranges == (internalAddA s input).ranges &&
                py.ranges == (internalAddC s input).ranges &&
                py.ranges == (internalAddD s input).ranges
            else
              false
        | none => false

open PyIntRangeSetCases in
example : pyCrossAgrees pyBase0 pyCases0 ∧ pyCrossAgrees pyBase1 pyCases1 ∧
    pyCrossAgrees pyBase2 pyCases2 ∧ pyCrossAgrees pyBase3 pyCases3 ∧
    pyCrossAgrees pyBase4 pyCases4 := by native_decide

/-- Python `IntRangeSet(...)` construction without `_static_ranges`
pre-coalescing: `_internal_add` each nonempty half-open range in turn. -/
private def pyFromRanges (ranges : List (Int × Int)) : RangeSetBlaze :=
  ranges.foldl (init := ⟨[], List.Pairwise.nil⟩) fun s (start, stop) =>
    if h : 0 < stop - start then internalAddPy s start (stop - start) h else s

-- The successive single-element adds of Python `IntRangeSet._test()`.
example :
    let adds : List Int := [0, 1, 4, 5, 7, 2, 3, 6, -10, -5]
    (List.range adds.length).map (fun n =>
        toHalfOpen (pyFromRanges ((adds.take (n + 1)).map fun x => (x, x + 1)))) =
      [[(0, 1)], [(0, 2)], [(0, 2), (4, 5)], [(0, 2), (4, 6)],
        [(0, 2), (4, 6), (7, 8)], [(0, 3), (4, 6), (7, 8)], [(0, 6), (7, 8)],
        [(0, 8)], [(-10, -9), (0, 8)], [(-10, -9), (-5, -4), (0, 8)]] := by
  native_decide

-- `IntRangeSet("-10:-4,-3,-2:2,1:6,7:13,13:16,14:17,20:26,22:24")`.
example : toHalfOpen (pyFromRanges [(-10, -4), (-3, -2), (-2, 2), (1, 6), (7, 13),
    (13, 16), (14, 17), (20, 26), (22, 24)]) =
    [(-10, -4), (-3, 6), (7, 17), (20, 26)] := by native_decide

-- `IntRangeSet("1:6,0,4:11,-10:-4,-12:-2,15:21,12:22,-13")`.
example : toHalfOpen (pyFromRanges [(1, 6), (0, 1), (4, 11), (-10, -4), (-12, -2),
    (15, 21), (12, 22), (-13, -12)]) =
    [(-13, -2), (0, 11), (12, 22)] := by native_decide

end RangeSetBlaze
