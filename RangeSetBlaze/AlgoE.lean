import RangeSetBlaze.Canonical
import RangeSetBlaze.AlgoCMap
import RangeSetBlaze.AlgoC

namespace RangeSetBlaze

open IntRange (NR)
open scoped IntRange.NR

/-- The Unit-valued map corresponding to a range set. -/
def asUnitMap (s : RangeSetBlaze) : RangeMapBlaze Unit :=
  ⟨s.ranges.map (fun range => ⟨range, ()⟩), by
    apply (List.pairwise_map).2
    exact s.canonical.imp (fun {a} {b} hab => by
      simp only [RangeMapBlaze.Run.before, RangeMapBlaze.Run.disjointBefore]
      exact ⟨by unfold IntRange.NR.before at hab; omega, fun _ => hab⟩)⟩

/-- Erasing Unit labels from a map produces a range set. -/
def eraseUnitMap (map : RangeMapBlaze Unit) : RangeSetBlaze :=
  ⟨map.runs.map (fun run => run.range), by
    apply (List.pairwise_map).2
    exact map.canonical.imp (fun {a} {b} hab => by
      exact hab.2 rfl)⟩

private theorem map_erase_unit_ranges (ranges : List NR) :
    List.map ((fun run : RangeMapBlaze.Run Unit => run.range) ∘
      (fun range : NR => ⟨range, ()⟩)) ranges = ranges := by
  induction ranges with
  | nil => rfl
  | cons range ranges ih =>
      simp only [List.map_cons, Function.comp_apply, ih]

@[simp] theorem eraseUnitMap_asUnitMap (s : RangeSetBlaze) :
    eraseUnitMap (asUnitMap s) = s := by
  apply RangeSetBlaze.ext
  simp only [asUnitMap, eraseUnitMap, RangeSetBlaze.toSet,
    rangesToSet, List.map_map]
  rw [map_erase_unit_ranges]

theorem eraseUnitMap_toSet (map : RangeMapBlaze Unit) :
    (eraseUnitMap map).toSet = map.support := by
  have aux : ∀ runs : List (RangeMapBlaze.Run Unit),
      rangesToSet (runs.map (fun run => run.range)) =
        {key | RangeMapBlaze.runsToFunction runs key ≠ none} := by
    intro runs
    induction runs with
    | nil => simp [rangesToSet]
    | cons run runs ih =>
        ext key
        change (key ∈ run.range.val.toSet ∨
          key ∈ rangesToSet (runs.map (fun run => run.range))) ↔ _
        rw [ih]
        by_cases h : run.range.val.lo ≤ key ∧ key ≤ run.range.val.hi
        · simp [IntRange.mem_toSet_iff, h]
        · simp [IntRange.mem_toSet_iff, h]
  exact aux map.runs

theorem asUnitMap_toSet (s : RangeSetBlaze) :
    (asUnitMap s).support = s.toSet := by
  rw [← eraseUnitMap_toSet, eraseUnitMap_asUnitMap]

theorem eraseUnitMap_cardinality (map : RangeMapBlaze Unit) :
    (eraseUnitMap map).cardinality = map.cardinality := by
  change RangeSetBlaze.rangesCardinality
      (map.runs.map (fun run => run.range)) =
    RangeMapBlaze.runsCardinality map.runs
  induction map.runs with
  | nil => rfl
  | cons run runs ih =>
      cases run with
      | mk range value =>
          simp only [RangeSetBlaze.rangesCardinality,
            RangeMapBlaze.runsCardinality, List.map_map] at ih
          change (List.map (fun run => run.range.val.cardinality) runs).sum =
            (List.map (fun run => run.cardinality) runs).sum at ih
          have hfun : (fun r : NR => r.val.cardinality) ∘
              (fun run : RangeMapBlaze.Run Unit => run.range) =
              (fun run => run.cardinality) := by
            funext run
            rfl
          simp only [RangeSetBlaze.rangesCardinality,
            RangeMapBlaze.runsCardinality, List.map_cons, List.sum_cons,
            List.map_map]
          rw [hfun]
          exact congrArg (fun n => range.val.cardinality + n) ih

theorem overwrite_unit_support (old : Int → Option Unit) (input : IntRange) :
    {key | (RangeMapBlaze.overwrite old input () key) ≠ none} =
      {key | old key ≠ none} ∪ input.toSet := by
  ext key
  by_cases h : input.lo ≤ key ∧ key ≤ input.hi
  · simp [RangeMapBlaze.overwrite, IntRange.mem_toSet_iff, h]
  · simp [RangeMapBlaze.overwrite, IntRange.mem_toSet_iff, h]

/-- Algo E inserts into a set through the Unit-valued map algorithm. -/
def internalAddE (s : RangeSetBlaze) (input : IntRange) : RangeSetBlaze :=
  eraseUnitMap (RangeMapBlaze.internalAddCMap (asUnitMap s) input ())

theorem internalAddE_toSet (s : RangeSetBlaze) (input : IntRange) :
    (internalAddE s input).toSet = s.toSet ∪ input.toSet := by
  rw [internalAddE, eraseUnitMap_toSet]
  change {key | (RangeMapBlaze.internalAddCMap (asUnitMap s) input ()).toFunction key ≠ none} = _
  rw [RangeMapBlaze.internalAddCMap_toFunction, overwrite_unit_support]
  change (asUnitMap s).support ∪ input.toSet = s.toSet ∪ input.toSet
  rw [asUnitMap_toSet]

end RangeSetBlaze
