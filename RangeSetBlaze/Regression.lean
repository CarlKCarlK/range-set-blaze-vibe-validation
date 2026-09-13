import RangeSetBlaze.AlgoA
import RangeSetBlaze.AlgoB
import RangeSetBlaze.AlgoC
import RangeSetBlaze.AlgoD
import RangeSetBlaze.AlgoE

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

/-- Starting from the true cardinality, ELen must reproduce Algo E, agree with
CLen's cached count, and cache exactly the result cardinality. -/
private def sameCachedLength (s : RangeSetBlaze) (r : IntRange) : Bool :=
  let eLen := internalAddELen s s.cardinality r
  eLen.setResult.ranges == (internalAddE s r).ranges &&
  eLen.cachedLength == (internalAddCLen s s.cardinality r).cachedLength &&
  eLen.cachedLength == eLen.setResult.cardinality

private def agrees (s : RangeSetBlaze) (r : IntRange) : Bool :=
  sameAcrossAlgorithms s r && sameCachedLength s r

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

example : agrees (testSet [testNR 10 12]) { lo := 5, hi := 4 } := by native_decide
example : agrees (testSet []) { lo := 5, hi := 7 } := by native_decide
example : agrees (testSet [testNR 10 12]) { lo := 1, hi := 3 } := by native_decide
example : agrees (testSet [testNR 10 12]) { lo := 20, hi := 22 } := by native_decide
example : agrees (testSet [testNR 1 5, testNR 10 20]) { lo := 12, hi := 15 } := by native_decide
example : agrees (testSet [testNR 10 20, testNR 30 35]) { lo := 10, hi := 15 } := by native_decide
example : agrees (testSet [testNR 1 3, testNR 10 12]) { lo := 5, hi := 7 } := by native_decide
example : agrees (testSet [testNR 10 12, testNR 20 22]) { lo := 7, hi := 9 } := by native_decide
example : agrees (testSet [testNR 10 12, testNR 14 16, testNR 18 20, testNR 30 35]) { lo := 7, hi := 18 } := by native_decide
example : agrees (testSet [testNR 1 5, testNR 10 12]) { lo := 4, hi := 7 } := by native_decide
example : agrees (testSet [testNR 1 5, testNR 8 10, testNR 20 22]) { lo := 4, hi := 7 } := by native_decide
example : agrees (testSet [testNR 1 5, testNR 8 10, testNR 13 15, testNR 30 35]) { lo := 4, hi := 13 } := by native_decide
example : agrees (testSet [testNR 10 12]) { lo := 10, hi := 12 } := by native_decide
example : agrees (testSet [testNR 10 12]) { lo := 13, hi := 15 } := by native_decide
example : agrees (testSet [testNR 10 12, testNR 20 22]) { lo := 5, hi := 30 } := by native_decide
example : agrees (testSet [testNR 10 12, testNR 16 18]) { lo := 13, hi := 15 } := by native_decide

end RangeSetBlaze
