import RangeSetBlaze.AlgoCMap

namespace RangeSetBlaze

open IntRange (NR)
open RangeMapBlaze

/-!
## Algo E: range-set insertion through a Unit-valued range map

Algo E is the set view of Algo CMap with the constant value `Unit`.  The
conversion keeps exactly the run ranges and forgets the values; consequently
the map's support and the set's represented set are the same finite set.
-/

private def asUnitMap (s : RangeSetBlaze) : RangeMapBlaze Unit :=
  ⟨s.ranges.map (fun range => ⟨range, ()⟩), by
    apply List.pairwise_map.mpr
    exact s.canonical.imp (fun h => by
      simp only [Run.before, Run.disjointBefore]
      exact ⟨by unfold IntRange.NR.before at h; omega, fun _ => h⟩)⟩

private def fromUnitMap (map : RangeMapBlaze Unit) : RangeSetBlaze :=
  ⟨map.runs.map Run.range, by
    apply List.pairwise_map.mpr
    exact map.canonical.imp (fun h => h.2 (by rfl))⟩

private lemma asUnitMap_ranges (s : RangeSetBlaze) :
    (asUnitMap s).runs.map Run.range = s.ranges := by
  simp [asUnitMap, List.map_map, Function.comp_def]

private lemma unitMap_toSet (s : RangeSetBlaze) :
    (fromUnitMap (asUnitMap s)).toSet = s.toSet := by
  change RangeSetBlaze.rangesToSet ((asUnitMap s).runs.map Run.range) = _
  rw [asUnitMap_ranges]
  rfl

private lemma unitMap_cardinality (map : RangeMapBlaze Unit) :
    map.cardinality = (fromUnitMap map).cardinality := by
  change (map.runs.map (fun run => run.range.val.cardinality)).sum =
    ((map.runs.map Run.range).map (fun range => range.val.cardinality)).sum
  induction map.runs with
  | nil => rfl
  | cons run rest ih => simp [ih]

private lemma support_eq_rangesToSet {Value : Type*}
    (runs : List (Run Value)) :
    {key | runsToFunction runs key ≠ none} =
      RangeSetBlaze.rangesToSet (runs.map Run.range) := by
  induction runs with
  | nil => simp [RangeMapBlaze.runsToFunction]
  | cons run rest ih =>
      ext key
      simp only [List.map_cons, RangeSetBlaze.rangesToSet_cons,
        RangeMapBlaze.runsToFunction_cons, Set.mem_ofPred_eq, Set.mem_union]
      by_cases h : run.range.val.lo ≤ key ∧ key ≤ run.range.val.hi
      · simp [h]
      · have hi : runsToFunction rest key ≠ none ↔
            key ∈ RangeSetBlaze.rangesToSet (rest.map Run.range) := by
          simpa using congrArg (fun set : Set Int => key ∈ set) ih
        simp [h]
        exact hi

private lemma asUnitMap_support (s : RangeSetBlaze) :
    (asUnitMap s).support = s.toSet := by
  ext key
  change key ∈ {key | runsToFunction (asUnitMap s).runs key ≠ none} ↔ _
  have h := Set.ext_iff.mp (support_eq_rangesToSet (asUnitMap s).runs) key
  rw [asUnitMap_ranges] at h
  exact h

private lemma unitMap_overwrite_set
    (map : RangeMapBlaze Unit) (input : IntRange) :
    (fromUnitMap (internalAddCMap map input ())).toSet =
      map.support ∪ input.toSet := by
  have hset : (fromUnitMap (internalAddCMap map input ())).toSet =
      (internalAddCMap map input ()).support := by
    ext key
    change key ∈ RangeSetBlaze.rangesToSet
      ((internalAddCMap map input ()).runs.map Run.range) ↔ _
    simpa [RangeMapBlaze.support, RangeMapBlaze.toFunction] using
      (Set.ext_iff.mp (support_eq_rangesToSet (internalAddCMap map input ()).runs) key).symm
  rw [hset]
  ext key
  have hfunction := congrFun (internalAddCMap_toFunction map input ()) key
  change (internalAddCMap map input ()).toFunction key ≠ none ↔ _
  rw [hfunction]
  by_cases h : input.lo ≤ key ∧ key ≤ input.hi <;>
    simp [h, RangeMapBlaze.support, RangeMapBlaze.toFunction]

/- The public, set-shaped Algo E result. -/
def internalAddE (s : RangeSetBlaze) (input : IntRange) : RangeSetBlaze :=
  fromUnitMap (internalAddCMap (asUnitMap s) input ())

theorem internalAddE_toSet (s : RangeSetBlaze) (input : IntRange) :
    (internalAddE s input).toSet = s.toSet ∪ input.toSet := by
  unfold internalAddE
  rw [unitMap_overwrite_set, asUnitMap_support]

structure ELenResult where
  setResult : RangeSetBlaze
  cachedLength : Nat

/- The length-carrying Algo E result, obtained from CMapLen at `Unit`. -/
def internalAddELen (s : RangeSetBlaze) (cachedLength : Nat)
    (input : IntRange) : ELenResult :=
  let result := internalAddCMapLen (asUnitMap s) cachedLength input ()
  ⟨fromUnitMap result.mapResult, result.cachedLength⟩

theorem internalAddELen_setResult (s : RangeSetBlaze) (cachedLength : Nat)
    (input : IntRange) :
    (internalAddELen s cachedLength input).setResult = internalAddE s input := by
  unfold internalAddELen internalAddE
  dsimp
  congr 1
  exact internalAddCMapLen_mapResult (asUnitMap s) cachedLength input ()

theorem internalAddELen_cachedLength (s : RangeSetBlaze) (cachedLength : Nat)
    (input : IntRange) (hlength : cachedLength = s.cardinality) :
    (internalAddELen s cachedLength input).cachedLength =
      (internalAddELen s cachedLength input).setResult.cardinality := by
  unfold internalAddELen
  dsimp
  simpa [unitMap_cardinality] using
    internalAddCMapLen_cachedLength (asUnitMap s) cachedLength input ()
    (by simpa [asUnitMap, RangeMapBlaze.cardinality, RangeMapBlaze.runsCardinality,
      RangeSetBlaze.cardinality, RangeSetBlaze.rangesCardinality,
      RangeMapBlaze.Run.cardinality]
      using hlength)

theorem internalAddELen_toSet (s : RangeSetBlaze) (cachedLength : Nat)
    (input : IntRange) :
    (internalAddELen s cachedLength input).setResult.toSet =
      s.toSet ∪ input.toSet := by
  rw [internalAddELen_setResult]
  exact internalAddE_toSet s input

end RangeSetBlaze
