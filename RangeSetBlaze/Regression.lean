import RangeSetBlaze.AlgoA
import RangeSetBlaze.AlgoB
import RangeSetBlaze.AlgoC
import RangeSetBlaze.AlgoD
import RangeSetBlaze.AlgoE
import RangeSetBlaze.PyIntRangeSet
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

The Python model works with half-open `(start, stop)` pairs.  The generated
cases record the real Python results for every `(start, length)` in a window
around several base sets; each must match the Lean model exactly and agree
with Algos A, C, and D on the inclusive input `[start, start + length - 1]`.
-/

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

/-- Python `_internal_add(start, length)` on `base` yields `expected`, and the
other algorithms produce the same canonical ranges. -/
private def pyAgrees (base : List (Int × Int)) (start length : Int)
    (expected : List (Int × Int)) : Bool :=
  match ofHalfOpen base with
  | none => false
  | some s =>
      if h : 0 < length then
        let input : IntRange := { lo := start, hi := start + length - 1 }
        let py := internalAddPy s start length h
        toHalfOpen py == expected &&
          py.ranges == (internalAddA s input).ranges &&
          py.ranges == (internalAddC s input).ranges &&
          py.ranges == (internalAddD s input).ranges
      else
        false

/-- Pair up a flattened `start stop start stop ...` list. -/
private def pairUp : List Int → List (Int × Int)
  | start :: stop :: rest => (start, stop) :: pairUp rest
  | _ => []

private def parseInts (line : String) : List Int :=
  (line.splitOn " ").filterMap String.toInt?

/-- Check every generated `start length ranges...` line against `base`. -/
private def pyAgreesAll (base cases : String) : Bool :=
  let baseRanges := pairUp (parseInts base)
  let lines := (cases.splitOn "\n").filter (· ≠ "")
  !lines.isEmpty && lines.all fun line =>
    match parseInts line with
    | start :: length :: expected =>
        (parseInts line).length == (line.splitOn " ").length &&
          pyAgrees baseRanges start length (pairUp expected)
    | _ => false

open PyIntRangeSetCases in
example : pyAgreesAll pyBase0 pyCases0 ∧ pyAgreesAll pyBase1 pyCases1 ∧
    pyAgreesAll pyBase2 pyCases2 ∧ pyAgreesAll pyBase3 pyCases3 ∧
    pyAgreesAll pyBase4 pyCases4 := by native_decide

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
