import RangeSetBlaze.Canonical
import RangeSetBlaze.AlgoA
import RangeSetBlaze.AlgoB
import RangeSetBlaze.AlgoC
import RangeSetBlaze.AlgoD
import RangeSetBlaze.AlgoAMap
import RangeSetBlaze.AlgoCMap
import RangeSetBlaze.AlgoDMap
import RangeSetBlaze.AlgoE
import RangeSetBlaze.PyIntRangeSet

namespace RangeSetBlaze

/-- Algo B produces the same canonical representation as reference Algo A. -/
theorem internalAddB_eq_internalAddA (set : RangeSetBlaze) (input : IntRange) :
    internalAddB set input = internalAddA set input := by
  apply RangeSetBlaze.ext
  rw [internalAddB_toSet, internalAddA_toSet]

/-- Production-shaped Algo C produces the same canonical representation as
reference Algo A. -/
theorem internalAddC_eq_internalAddA (set : RangeSetBlaze) (input : IntRange) :
    internalAddC set input = internalAddA set input := by
  apply RangeSetBlaze.ext
  rw [internalAddC_toSet, internalAddA_toSet]

/-- Cursor-shaped Algo D produces the same canonical representation as
reference Algo A. -/
theorem internalAddD_eq_internalAddA (set : RangeSetBlaze) (input : IntRange) :
    internalAddD set input = internalAddA set input := by
  apply RangeSetBlaze.ext
  rw [internalAddD_toSet, internalAddA_toSet]

/-- Map-derived Algo E produces the same canonical representation as
reference Algo A. -/
theorem internalAddE_eq_internalAddA (set : RangeSetBlaze) (input : IntRange) :
    internalAddE set input = internalAddA set input := by
  apply RangeSetBlaze.ext
  rw [internalAddE_toSet, internalAddA_toSet]

/-- PySnpTools-shaped `internalAddPy` produces the same canonical
representation as reference Algo A given the inclusive form
`[start, start + length - 1]` of Python's half-open input. -/
theorem internalAddPy_eq_internalAddA (set : RangeSetBlaze) (start length : Int)
    (hlength : 0 < length) :
    internalAddPy set start length hlength =
      internalAddA set { lo := start, hi := start + length - 1 } := by
  apply RangeSetBlaze.ext
  -- The inclusive input is definitionally Python's stored range `[start, start + length)`.
  rw [internalAddPy_toSet, internalAddA_toSet,
    ← IntRange.NR.ofStartStop_toSet start (start + length) (by omega)]
  rfl

end RangeSetBlaze

namespace RangeMapBlaze

/-- Production-shaped map Algo C produces the same canonical representation
as reference map Algo A. -/
theorem internalAddCMap_eq_internalAddAMap {Value : Type*} [DecidableEq Value]
    (map : RangeMapBlaze Value) (input : IntRange) (value : Value) :
    internalAddCMap map input value = internalAddAMap map input value := by
  apply RangeMapBlaze.ext
  rw [internalAddCMap_toFunction, internalAddAMap_toFunction]

/-- Cursor-shaped map Algo D produces the same canonical representation as
reference map Algo A. -/
theorem internalAddDMap_eq_internalAddAMap {Value : Type*} [DecidableEq Value]
    (map : RangeMapBlaze Value) (input : IntRange) (value : Value) :
    internalAddDMap map input value = internalAddAMap map input value := by
  apply RangeMapBlaze.ext
  rw [internalAddDMap_toFunction, internalAddAMap_toFunction]

end RangeMapBlaze
