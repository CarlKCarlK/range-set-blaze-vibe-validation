import RangeSetBlaze.AlgoE

namespace RangeSetBlaze

structure AlgoELenResult where
  setResult : RangeSetBlaze
  cachedLength : Nat

/-- Algo E with an explicit cache of the represented element count. -/
def internalAddELen (s : RangeSetBlaze) (cachedLength : Nat)
    (input : IntRange) : AlgoELenResult :=
  let result := RangeMapBlaze.internalAddCMapLen
    (asUnitMap s) cachedLength input ()
  ⟨eraseUnitMap result.mapResult, result.cachedLength⟩

theorem internalAddELen_setResult (s : RangeSetBlaze) (cachedLength : Nat)
    (input : IntRange) :
    (internalAddELen s cachedLength input).setResult = internalAddE s input := by
  unfold internalAddELen internalAddE
  dsimp
  rw [RangeMapBlaze.internalAddCMapLen_mapResult]

theorem internalAddELen_cachedLength (s : RangeSetBlaze) (cachedLength : Nat)
    (input : IntRange) (hlength : cachedLength = s.cardinality) :
    (internalAddELen s cachedLength input).cachedLength =
      (internalAddELen s cachedLength input).setResult.cardinality := by
  unfold internalAddELen
  have hmap : cachedLength = (asUnitMap s).cardinality := by
    simpa [asUnitMap, RangeMapBlaze.cardinality, RangeSetBlaze.cardinality,
      RangeMapBlaze.runsCardinality, RangeMapBlaze.Run.cardinality,
      rangesCardinality] using hlength
  have h := RangeMapBlaze.internalAddCMapLen_cachedLength
    (asUnitMap s) cachedLength input () hmap
  rw [eraseUnitMap_cardinality]
  exact h

theorem internalAddELen_toSet (s : RangeSetBlaze) (cachedLength : Nat)
    (input : IntRange) :
    (internalAddELen s cachedLength input).setResult.toSet =
      s.toSet ∪ input.toSet := by
  rw [internalAddELen_setResult, internalAddE_toSet]

end RangeSetBlaze
