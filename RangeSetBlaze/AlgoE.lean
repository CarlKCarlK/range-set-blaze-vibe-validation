import RangeSetBlaze.AlgoDMap

open IntRange (NR)

namespace RangeSetBlaze

/-!
## Range-set insertion through a Unit-valued range map

Algo E represents a range set as a `RangeMapBlaze Unit`, delegates insertion
to the cursor-shaped map algorithm, and then erases the uninformative values.
Its cached-length variant delegates the bookkeeping to DMapLen as well, so no
set-specific insertion arithmetic is duplicated here.
-/

/-- Regard a canonical range set as a range map carrying `Unit` at every key. -/
def toUnitMap (set : RangeSetBlaze) : RangeMapBlaze Unit :=
  ⟨set.ranges.map (fun range => ⟨range, ()⟩), by
    change List.Pairwise RangeMapBlaze.Run.before
      (set.ranges.map fun range => ⟨range, ()⟩)
    rw [List.pairwise_map]
    exact set.canonical.imp fun h => by
      unfold NR.before at h
      exact ⟨by simp only [RangeMapBlaze.Run.disjointBefore]; omega,
        fun _ => h⟩⟩

/-- Erase the values of a canonical `Unit`-valued range map. -/
def unitMapToSet (map : RangeMapBlaze Unit) : RangeSetBlaze :=
  ⟨map.runs.map (fun run => run.range), by
    change List.Pairwise NR.before (map.runs.map fun run => run.range)
    rw [List.pairwise_map]
    exact map.canonical.imp fun h => h.2 rfl⟩

private lemma erasedUnitRuns_cardinality
    (runs : List (RangeMapBlaze.Run Unit)) :
    rangesCardinality (runs.map fun run => run.range) =
      RangeMapBlaze.runsCardinality runs := by
  induction runs with
  | nil => rfl
  | cons run runs ih =>
      change run.range.val.cardinality + rangesCardinality
          (runs.map fun run => run.range) =
        run.cardinality + RangeMapBlaze.runsCardinality runs
      rw [ih]
      rfl

/-- Erasing `Unit` values preserves represented scalar cardinality. -/
@[simp] lemma unitMapToSet_cardinality (map : RangeMapBlaze Unit) :
    (unitMapToSet map).cardinality = map.cardinality :=
  erasedUnitRuns_cardinality map.runs

private lemma mem_erasedUnitRuns_iff
    (runs : List (RangeMapBlaze.Run Unit)) (key : Int) :
    key ∈ rangesToSet (runs.map fun run => run.range) ↔
      RangeMapBlaze.runsToFunction runs key = some () := by
  induction runs with
  | nil => simp
  | cons run runs ih =>
      cases run.value
      by_cases hcontains : run.range.val.lo ≤ key ∧ key ≤ run.range.val.hi
      · simp [RangeMapBlaze.runsToFunction_cons, hcontains]
      · simp [RangeMapBlaze.runsToFunction_cons, hcontains, ih,
          IntRange.mem_toSet_iff]

/-- Erasing a `Unit` map turns its defined keys into set membership. -/
lemma mem_unitMapToSet_iff (map : RangeMapBlaze Unit) (key : Int) :
    key ∈ (unitMapToSet map).toSet ↔ map.toFunction key = some () :=
  mem_erasedUnitRuns_iff map.runs key

/-- Adding `Unit` values and immediately erasing them is the identity. -/
@[simp] lemma unitMapToSet_toUnitMap (set : RangeSetBlaze) :
    unitMapToSet (toUnitMap set) = set := by
  cases set
  simp [unitMapToSet, toUnitMap, List.map_map, Function.comp_def]

/-- Adding `Unit` values preserves represented scalar cardinality. -/
@[simp] lemma toUnitMap_cardinality (set : RangeSetBlaze) :
    (toUnitMap set).cardinality = set.cardinality := by
  rw [← unitMapToSet_cardinality]
  simp

/-- Range-set insertion implemented by cursor-shaped map insertion with
`Unit` values. -/
def internalAddE (set : RangeSetBlaze) (input : IntRange) : RangeSetBlaze :=
  unitMapToSet (RangeMapBlaze.internalAddDMap (toUnitMap set) input ())

/-- Algo E insertion together with its explicit represented-element count. -/
structure ELenResult where
  setResult : RangeSetBlaze
  cachedLength : Nat

/-- Algo E insertion whose cached count is maintained by DMapLen. -/
def internalAddELen
    (set : RangeSetBlaze) (cachedLength : Nat) (input : IntRange) : ELenResult :=
  let result := RangeMapBlaze.internalAddDMapLen
    (toUnitMap set) cachedLength input ()
  ⟨unitMapToSet result.mapResult, result.cachedLength⟩

/-- Algo E represents insertion as set union. -/
theorem internalAddE_toSet (set : RangeSetBlaze) (input : IntRange) :
    (internalAddE set input).toSet = set.toSet ∪ input.toSet := by
  ext key
  unfold internalAddE
  rw [mem_unitMapToSet_iff]
  have hoverwrite := congrFun
    (RangeMapBlaze.internalAddDMap_toFunction (toUnitMap set) input ()) key
  rw [hoverwrite]
  by_cases hinput : key ∈ input.toSet
  · simp [RangeMapBlaze.overwrite, hinput]
  · have hold := mem_unitMapToSet_iff (toUnitMap set) key
    simp [RangeMapBlaze.overwrite, hinput, ← hold]

/-- AlgoELen erases to Algo E and preserves a valid represented-element
count. -/
theorem internalAddELen_correct
    (set : RangeSetBlaze) (cachedLength : Nat) (input : IntRange)
    (hlength : cachedLength = set.cardinality) :
    (internalAddELen set cachedLength input).setResult = internalAddE set input ∧
      (internalAddELen set cachedLength input).cachedLength =
        (internalAddELen set cachedLength input).setResult.cardinality := by
  dsimp only [internalAddELen]
  constructor
  · simp only [internalAddE]
    rw [RangeMapBlaze.internalAddDMapLen_mapResult]
  · rw [unitMapToSet_cardinality]
    exact RangeMapBlaze.internalAddDMapLen_cachedLength
      (toUnitMap set) cachedLength input () (by simpa using hlength)

end RangeSetBlaze
