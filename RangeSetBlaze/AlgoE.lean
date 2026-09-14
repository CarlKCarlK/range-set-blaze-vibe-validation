import RangeSetBlaze.AlgoCMap

/-!
## Algo E: set insertion through the `Unit`-valued map algorithm

Algo E inserts a range into a range set by viewing the set as a `Unit`-valued
range map, running production-shaped map Algo C with the value `()`, and
forgetting the values again. Its set semantics are Algo CMap's overwrite
semantics: overwriting with `()` adds exactly the input keys to the support.
The cached-length variant is likewise Algo CMapLen transported across the same
bridge, so no insertion arithmetic is re-proved here.
-/

namespace RangeSetBlaze

open RangeMapBlaze

/-- Insert one inclusive range by map Algo C at `Unit`. -/
def internalAddE (s : RangeSetBlaze) (input : IntRange) : RangeSetBlaze :=
  (internalAddCMap s.toUnitMap input ()).toRangeSet

/-- Algo E represents exactly the union of the old set and the input interval. -/
theorem internalAddE_toSet (s : RangeSetBlaze) (input : IntRange) :
    (internalAddE s input).toSet = s.toSet ∪ input.toSet := by
  rw [internalAddE, toRangeSet_toSet, ← toUnitMap_support]
  ext key
  by_cases h : key ∈ input.toSet <;> simp [support, internalAddCMap_toFunction, h]

/-- The result of Algo E insertion with an explicit cached element count. -/
structure ELenResult where
  setResult : RangeSetBlaze
  cachedLength : Nat
  deriving Repr

/-- Algo E insertion with an explicit incoming cached element count, carried
by Algo CMapLen at `Unit`. -/
def internalAddELen
    (s : RangeSetBlaze) (cachedLength : Nat) (input : IntRange) : ELenResult :=
  let result := internalAddCMapLen s.toUnitMap cachedLength input ()
  ⟨result.mapResult.toRangeSet, result.cachedLength⟩

/-- ELen's set component is exactly Algo E's result. -/
theorem internalAddELen_setResult
    (s : RangeSetBlaze) (cachedLength : Nat) (input : IntRange) :
    (internalAddELen s cachedLength input).setResult = internalAddE s input :=
  congrArg toRangeSet (internalAddCMapLen_mapResult s.toUnitMap cachedLength input ())

/-- A valid incoming cached count remains valid after Algo E insertion. -/
theorem internalAddELen_cachedLength
    (s : RangeSetBlaze) (cachedLength : Nat) (input : IntRange)
    (hlength : cachedLength = s.cardinality) :
    (internalAddELen s cachedLength input).cachedLength =
      (internalAddELen s cachedLength input).setResult.cardinality := by
  simp only [internalAddELen, toRangeSet_cardinality]
  exact internalAddCMapLen_cachedLength s.toUnitMap cachedLength input ()
    (by rw [hlength, ← toRangeSet_cardinality, toRangeSet_toUnitMap])

end RangeSetBlaze
