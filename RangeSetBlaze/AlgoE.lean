import RangeSetBlaze.AlgoCMap
import RangeSetBlaze.Canonical

/-!
# Algo E: set insertion through the `Unit`-valued map algorithm

Algo E inserts into a `RangeSetBlaze` by viewing it as a `Unit`-valued
`RangeMapBlaze`, delegating to Algo CMap, and forgetting values again. The
bridge that makes this exact is `RangeMapBlaze.Run.before_iff_range_before`
(`Basic.lean`): since `Unit` has only one value, canonical run order and
canonical range order coincide, so no information is lost by the round trip.

Algo E's correctness is therefore inherited entirely from
`internalAddCMap_toFunction` through the `support`/`eraseValue` bridge; no
fresh induction on ranges is needed. Algo ELen inherits `internalAddCMapLen`'s
cached-cardinality invariant the same way.
-/

namespace RangeMapBlaze

/-- Forget the (necessarily unique) values of a run list, recovering the
canonical range list it represents. Valid whenever `Value` has at most one
value, since canonical run order then coincides with canonical range order. -/
def eraseValue {Value : Type*} [Subsingleton Value] (map : RangeMapBlaze Value) :
    RangeSetBlaze :=
  ⟨map.runs.map Run.range, (canonical_iff_range_canonical map.runs).mp map.canonical⟩

/-- Erasing values does not change the represented set: it is exactly the
map's support. -/
theorem eraseValue_toSet {Value : Type*} [Subsingleton Value] (map : RangeMapBlaze Value) :
    map.eraseValue.toSet = map.support :=
  (support_eq_rangesToSet map).symm

/-- Erasing values does not change the represented cardinality: `Run.cardinality`
already ignores the value. -/
theorem eraseValue_cardinality {Value : Type*} [Subsingleton Value]
    (map : RangeMapBlaze Value) :
    map.eraseValue.cardinality = map.cardinality := by
  show RangeSetBlaze.rangesCardinality (map.runs.map Run.range) = runsCardinality map.runs
  rw [RangeSetBlaze.rangesCardinality, runsCardinality, List.map_map]
  rfl

end RangeMapBlaze

namespace RangeSetBlaze

/-- Attaching the sole `Unit` value to every stored range and then forgetting
it again recovers exactly the original ranges: the raw-list form of the
`toMap`/`eraseValue` round trip. -/
private theorem toMap_runs_map_range (s : RangeSetBlaze) :
    (s.ranges.map (fun nr => (⟨nr, ()⟩ : RangeMapBlaze.Run Unit))).map RangeMapBlaze.Run.range
      = s.ranges := by
  rw [List.map_map]
  exact List.map_id _

/-- View a range set as the `Unit`-valued range map with the same represented
set: the companion direction of the Algo E bridge, supplying the one available
value at every stored range. -/
def toMap (s : RangeSetBlaze) : RangeMapBlaze Unit :=
  ⟨s.ranges.map (fun nr => (⟨nr, ()⟩ : RangeMapBlaze.Run Unit)), by
    rw [RangeMapBlaze.canonical_iff_range_canonical, toMap_runs_map_range]
    exact s.canonical⟩

/-- Attaching the sole `Unit` value to every stored range and then forgetting
it again recovers the original set: `eraseValue` undoes `toMap`. -/
theorem toMap_eraseValue (s : RangeSetBlaze) : s.toMap.eraseValue = s := by
  apply ext
  rw [RangeMapBlaze.eraseValue_toSet, RangeMapBlaze.support_eq_rangesToSet]
  show RangeSetBlaze.rangesToSet
      ((s.ranges.map (fun nr => (⟨nr, ()⟩ : RangeMapBlaze.Run Unit))).map RangeMapBlaze.Run.range)
      = s.toSet
  rw [toMap_runs_map_range, toSet_eq_rangesToSet]

@[simp] theorem toMap_support (s : RangeSetBlaze) : s.toMap.support = s.toSet := by
  rw [← RangeMapBlaze.eraseValue_toSet, toMap_eraseValue]

@[simp] theorem toMap_cardinality (s : RangeSetBlaze) : s.toMap.cardinality = s.cardinality := by
  rw [← RangeMapBlaze.eraseValue_cardinality, toMap_eraseValue]

/-- Insert by delegating to Algo CMap at `Value := Unit` and forgetting values. -/
def internalAddE (s : RangeSetBlaze) (r : IntRange) : RangeSetBlaze :=
  (RangeMapBlaze.internalAddCMap s.toMap r ()).eraseValue

/-- Algo E represents exactly the union of the old range set and the input
interval, inherited from Algo CMap's overwrite semantics. -/
theorem internalAddE_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAddE s r).toSet = s.toSet ∪ r.toSet := by
  rw [internalAddE, RangeMapBlaze.eraseValue_toSet]
  ext key
  show (RangeMapBlaze.internalAddCMap s.toMap r ()).toFunction key ≠ none ↔ _
  rw [RangeMapBlaze.internalAddCMap_toFunction, RangeMapBlaze.overwrite_ne_none_iff]
  have hmem : s.toMap.toFunction key ≠ none ↔ key ∈ s.toSet := by
    rw [← toMap_support]; rfl
  rw [hmem, Set.mem_union]

/-! ## Algo E with cached length -/

/-- The externally useful result of Algo E insertion with an explicit cached
element count, matching the shape of `CLenResult`/`DLenResult`. -/
structure ELenResult where
  setResult : RangeSetBlaze
  cachedLength : Nat
  deriving Repr

/-- Algo E insertion with an explicit incoming cached element count, obtained
by delegating to Algo CMapLen at `Value := Unit` and forgetting values. -/
def internalAddELen (s : RangeSetBlaze) (cachedLength : Nat) (r : IntRange) : ELenResult :=
  let raw := RangeMapBlaze.internalAddCMapLen s.toMap cachedLength r ()
  ⟨raw.mapResult.eraseValue, raw.cachedLength⟩

/-- ELen's set component is exactly Algo E's result. -/
theorem internalAddELen_setResult (s : RangeSetBlaze) (cachedLength : Nat) (r : IntRange) :
    (internalAddELen s cachedLength r).setResult = internalAddE s r := by
  show (RangeMapBlaze.internalAddCMapLen s.toMap cachedLength r ()).mapResult.eraseValue
      = internalAddE s r
  rw [RangeMapBlaze.internalAddCMapLen_mapResult, internalAddE]

/-- A valid incoming cached count remains valid after ELen insertion. -/
theorem internalAddELen_cachedLength (s : RangeSetBlaze) (cachedLength : Nat) (r : IntRange)
    (hlength : cachedLength = s.cardinality) :
    (internalAddELen s cachedLength r).cachedLength =
      (internalAddELen s cachedLength r).setResult.cardinality := by
  unfold internalAddELen
  dsimp only
  rw [RangeMapBlaze.eraseValue_cardinality]
  exact RangeMapBlaze.internalAddCMapLen_cachedLength s.toMap cachedLength r ()
    (by rw [hlength, toMap_cardinality])

/-- ELen inherits Algo E's already-proved set semantics. -/
theorem internalAddELen_toSet (s : RangeSetBlaze) (cachedLength : Nat) (r : IntRange) :
    (internalAddELen s cachedLength r).setResult.toSet = s.toSet ∪ r.toSet := by
  rw [internalAddELen_setResult]
  exact internalAddE_toSet s r

end RangeSetBlaze
