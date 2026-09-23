import RangeSetBlaze.AlgoC

/-!
# PySnpTools `IntRangeSet._internal_add`

This module models the insertion algorithm of the Python predecessor of
RangeSetBlaze, `pysnptools.util.intrangeset.IntRangeSet._internal_add`, and
proves it correct.  As with the Rust models, this validates the algorithm, not
Python execution semantics.

## State correspondence

Python stores a sorted list `_start_items` and a dictionary
`_start_to_length`.  Together they denote the list of half-open ranges
`[s, s + _start_to_length[s])` for `s` in `_start_items`, in order.  The model
stores that list directly as a canonical `RangeSetBlaze`: the Python range
`[start, stop)` with `length = stop - start > 0` is the inclusive `NR`
`{ lo := start, hi := stop - 1 }` (`NR.ofStartStop`).  Conversely,
`_start_items[i]` is `ranges[i].val.lo`, and `_start_to_length` maps it to
`NR.length ranges[i]`.  Python's invariant — positive lengths, sorted unique
starts, and each `stop` strictly below the next start — is exactly
`List.Pairwise NR.before` on `NR`s (`internalAddPy_python_invariants`).
Keeping the list and dictionary in sync (Python's
`len(_start_items) == len(_start_to_length)` assertion) is structural here.

## Algorithm correspondence

`internalAddPy` takes Python's `(start, length)` arguments and Python's
precondition `length > 0`.  Its comparisons are written with Python's
half-open quantities `NR.stop` and `NR.length`:

* `bisectLeft` is `bisect_left(_start_items, start)`: `left` holds the ranges
  before `index`, `right` those from `index`;
* a range already starts at `start`: return if `length <= _start_to_length`,
  otherwise lengthen it and merge from `index + 1`;
* `index == 0`: insert `[start, start + length)` and merge;
* `start <= stop` of `previous = _start_items[index - 1]`: return if
  `new_length < _start_to_length[previous]`, otherwise lengthen `previous` to
  `new_length` and merge from `index`;
* otherwise: insert `[start, start + length)` at `index` and merge.

The shared `while stop >= next` loop is `absorbFollowing`.  Python updates
`_start_to_length[previous]` in every iteration, so the loop state is the
current range stored at `previous`.  `absorbFollowing_eq_deleteExtraNRs_loop`
proves this loop is the production RangeSetBlaze scan `deleteExtraNRs_loop`;
the proof therefore reuses that scan's ordering and union contract.

## Proof architecture

The Python-specific front end is small; the range mathematics is shared.

* `bisect_left` is the shared strict lower-bound split
  (`NR.strict_start_split_spec`), also used by Algo D's cursor search.
* Every mutating branch stores one current range after an untouched prefix and
  runs the merge loop (`mergeFollowing`).  Its one contract,
  `mergeFollowing_preserves_order_and_union`, is Algo C's scan contract
  transported along `absorbFollowing_eq_deleteExtraNRs_loop`.  This is why the
  module imports Algo C, which exports the scan and its contract for this use.
* Each branch then supplies only its own facts: which ranges stay untouched,
  why they end with a gap before the current range, and how the current
  range's set relates to the input.  `NR.toSet_eq_Ico` reads a stored range as
  Python's `[start, stop)`, and both early `return`s share
  `rangesToSet_union_Ico_of_covered`.
-/

/-! ## Python's half-open vocabulary -/

namespace IntRange.NR

/-- Python's stored range `[start, stop)`, as an inclusive nonempty range. -/
def ofStartStop (start stop : Int) (h : start < stop) : NR :=
  ⟨{ lo := start, hi := stop - 1 }, by change start ≤ stop - 1; omega⟩

/-- Python's exclusive end `start + _start_to_length[start]` of a stored range. -/
def stop (r : NR) : Int := r.val.hi + 1

/-- Python's `_start_to_length[start]` of a stored range. -/
def length (r : NR) : Int := r.stop - r.val.lo

/-- A stored range starts strictly before its exclusive end. -/
lemma lo_lt_stop (r : NR) : r.val.lo < r.stop :=
  Int.lt_add_one_iff.mpr r.property

/-- Every stored Python range has a strictly positive length. -/
lemma length_pos (r : NR) : 0 < r.length :=
  sub_pos.mpr r.lo_lt_stop

/-- Read in Python's vocabulary, a stored range denotes `[start, stop)`. -/
lemma toSet_eq_Ico (r : NR) : r.val.toSet = Set.Ico r.val.lo r.stop := by
  ext x
  simp only [IntRange.mem_toSet_iff, Set.mem_Ico, stop]
  omega

/-- A range built from Python's `[start, stop)` denotes exactly that interval. -/
@[simp] lemma ofStartStop_toSet (start stop : Int) (h : start < stop) :
    (ofStartStop start stop h).val.toSet = Set.Ico start stop := by
  ext x
  simp only [ofStartStop, IntRange.mem_toSet_iff, Set.mem_Ico]
  omega

end IntRange.NR

namespace RangeSetBlaze

open IntRange
open scoped IntRange.NR

/-! ## The algorithm -/

/-- Python's `bisect_left(self._start_items, start)`, returned as the ranges
before and from the insertion index.  On sorted starts, the maximal prefix with
`start_i < start` ends exactly at `bisect_left`'s index. -/
private def bisectLeft (start : Int) (ranges : List NR) : List NR × List NR :=
  ranges.span (fun nr => decide (nr.val.lo < start))

/-- Python's merge loop, where `current` is the range stored at `previous`
and its `NR.stop` is Python's `stop`:

```python
next = self._start_items[index]
while stop >= next:
    new_stop = max(stop, next + self._start_to_length[next])
    self._start_to_length[previous] = new_stop - previous
    del self._start_to_length[next]
    del self._start_items[index]
    stop = new_stop
    if index >= len(self._start_items):
        break
    next = self._start_items[index]
```

The empty-list case is also Python's `if index == len(self._start_items)`
early return before the loop.  The result is the final current range and the
ranges remaining from `index`. -/
def absorbFollowing (current : NR) : List NR → NR × List NR
  | [] => (current, [])
  | next :: rest =>
      if next.val.lo ≤ current.stop then
        absorbFollowing
          (NR.ofStartStop current.val.lo (max current.stop next.stop)
            (lt_max_of_lt_left current.lo_lt_stop))
          rest
      else
        (current, next :: rest)

/-- Store `current` after the untouched ranges and run the merge loop over the
following ranges. -/
private def mergeFollowing (untouched : List NR) (current : NR)
    (following : List NR) : List NR :=
  let merged := absorbFollowing current following
  untouched ++ merged.1 :: merged.2

/-- Python's branches when no stored range starts exactly at `start`:
`index == 0`, or inspect `previous = _start_items[index - 1]`. -/
private def addAfterPredecessor (ranges left right : List NR)
    (start length : Int) (hlength : 0 < length) : List NR :=
  match left.getLast? with
  | none =>
      mergeFollowing left (NR.ofStartStop start (start + length) (by omega)) right
  | some previous =>
      if start ≤ previous.stop then
        let newLength := start - previous.val.lo + length
        if hcovered : newLength < previous.length then
          ranges
        else
          mergeFollowing left.dropLast
            (NR.ofStartStop previous.val.lo (previous.val.lo + newLength) (by
              have := previous.length_pos
              omega))
            right
      else
        mergeFollowing left (NR.ofStartStop start (start + length) (by omega)) right

/-- The list computation of Python `_internal_add(start, length)`. -/
private def internalAddPyNRs (ranges : List NR) (start length : Int)
    (hlength : 0 < length) : List NR :=
  let split := bisectLeft start ranges
  match split.2 with
  | existing :: following =>
      if existing.val.lo = start then
        if length ≤ existing.length then
          ranges
        else
          mergeFollowing split.1
            (NR.ofStartStop start (start + length) (by omega)) following
      else
        addAfterPredecessor ranges split.1 split.2 start length hlength
  | [] => addAfterPredecessor ranges split.1 split.2 start length hlength

/-! ## Proof -/

/-- Python's merge loop is exactly the production RangeSetBlaze merge scan:
`stop >= next` is `next.lo ≤ current.hi + 1`, and the new exclusive stop
`max stop next_stop` is one past `max current.hi next.hi`. -/
theorem absorbFollowing_eq_deleteExtraNRs_loop (current : NR) (following : List NR) :
    absorbFollowing current following = deleteExtraNRs_loop current following := by
  induction following generalizing current with
  | nil => rfl
  | cons next rest ih =>
      -- Python's `stop >= next` is definitionally the scan's touch test.
      by_cases htouch : next.val.lo ≤ current.val.hi + 1
      · simp only [absorbFollowing, deleteExtraNRs_loop, NR.stop, htouch, decide_true,
          if_true, ih]
        -- Both loops keep `current`'s start; the new stop is one past the new `hi`.
        congr 1
        apply Subtype.ext
        change IntRange.mk _ _ = IntRange.mk _ _
        congr 1
        omega
      · simp [absorbFollowing, deleteExtraNRs_loop, NR.stop, htouch]

/-- `bisect_left` splits a canonical list into the ranges starting before
`start` and those starting at or after it. -/
private theorem bisectLeft_spec (start : Int) (ranges : List NR)
    (hpw : List.Pairwise NR.before ranges) :
    let split := bisectLeft start ranges
    ranges = split.1 ++ split.2 ∧
      (∀ nr ∈ split.1, nr.val.lo < start) ∧
      (∀ nr ∈ split.2, start ≤ nr.val.lo) :=
  NR.strict_start_split_spec ranges start hpw

/-- The common tail of every mutating branch: if the untouched ranges end
with a gap before `current`, and the following ranges start no earlier than
`current`, then storing `current` and running the merge loop preserves
canonical order and exactly adds `current`. -/
private theorem mergeFollowing_preserves_order_and_union
    (untouched : List NR) (current : NR) (following : List NR)
    (huntouched : List.Pairwise NR.before untouched)
    (hgap : ∀ nr ∈ untouched, nr ≺ current)
    (hfollowing : List.Pairwise NR.before following)
    (hlower : ∀ nr ∈ following, current.val.lo ≤ nr.val.lo) :
    List.Pairwise NR.before (mergeFollowing untouched current following) ∧
      rangesToSet (mergeFollowing untouched current following) =
        rangesToSet untouched ∪ current.val.toSet ∪ rangesToSet following := by
  obtain ⟨horder, hbound, hunion⟩ :=
    deleteExtraNRs_loop_preserves_order_lower_bound_and_union
      current.val.lo current following rfl hlower
  simp only [mergeFollowing, absorbFollowing_eq_deleteExtraNRs_loop]
  refine ⟨List.pairwise_append.mpr ⟨huntouched, horder hfollowing, ?_⟩, ?_⟩
  · intro nr hnr merged hmerged
    exact lt_of_lt_of_le (hgap nr hnr) (hbound merged hmerged)
  · rw [rangesToSet_append, hunion, Set.union_assoc]

/-- Python's two early `return`s: an input interval inside a stored range
leaves the represented set unchanged. -/
private lemma rangesToSet_union_Ico_of_covered
    {ranges : List NR} {container : NR} {start stop : Int}
    (hmem : container ∈ ranges)
    (hstart : container.val.lo ≤ start) (hstop : stop ≤ container.stop) :
    rangesToSet ranges = rangesToSet ranges ∪ Set.Ico start stop := by
  refine (Set.union_eq_left.mpr ?_).symm
  calc Set.Ico start stop
      ⊆ Set.Ico container.val.lo container.stop := Set.Ico_subset_Ico hstart hstop
    _ = container.val.toSet := container.toSet_eq_Ico.symm
    _ ⊆ rangesToSet ranges := toSet_subset_rangesToSet_of_mem_of_bounds hmem le_rfl le_rfl

/-- Correctness of the branches in which no stored range is known to start at
`start`. -/
private theorem addAfterPredecessor_preserves_order_and_union
    (ranges left right : List NR) (start length : Int) (hlength : 0 < length)
    (hpw : List.Pairwise NR.before ranges)
    (hsplit : ranges = left ++ right)
    (hleft : ∀ nr ∈ left, nr.val.lo < start)
    (hright : ∀ nr ∈ right, start ≤ nr.val.lo) :
    List.Pairwise NR.before (addAfterPredecessor ranges left right start length hlength) ∧
      rangesToSet (addAfterPredecessor ranges left right start length hlength) =
        rangesToSet ranges ∪ Set.Ico start (start + length) := by
  subst hsplit
  obtain ⟨hpwLeft, hpwRight, -⟩ := List.pairwise_append.mp hpw
  unfold addAfterPredecessor
  set input := NR.ofStartStop start (start + length) (by omega) with hinput
  -- Python's two inserting branches store the input at `index`; each needs
  -- only that every range before `index` ends with a gap before `start`.
  have hinsert (hgap : ∀ nr ∈ left, nr ≺ input) :
      List.Pairwise NR.before (mergeFollowing left input right) ∧
        rangesToSet (mergeFollowing left input right) =
          rangesToSet (left ++ right) ∪ Set.Ico start (start + length) := by
    obtain ⟨horder, hunion⟩ :=
      mergeFollowing_preserves_order_and_union left input right hpwLeft hgap hpwRight hright
    refine ⟨horder, ?_⟩
    rw [hunion, rangesToSet_append, hinput, NR.ofStartStop_toSet]
    ac_rfl
  split
  · -- `index == 0`: insert at the front.
    rename_i hnone
    simp only [List.getLast?_eq_none_iff] at hnone
    exact hinsert (by simp [hnone])
  · rename_i previous hprev
    obtain ⟨init, hinit⟩ := List.getLast?_eq_some_iff.mp hprev
    have hprevLo : previous.val.lo < start := hleft previous (by simp [hinit])
    obtain ⟨hpwInit, -, hinitPrev⟩ := List.pairwise_append.mp (hinit ▸ hpwLeft)
    split
    · -- `start <= stop`: the input touches or overlaps `previous`.
      rename_i htouch
      dsimp only
      split
      · -- `new_length < _start_to_length[previous]`: already covered.
        rename_i hcovered
        simp only [NR.length] at hcovered
        exact ⟨hpw, rangesToSet_union_Ico_of_covered (by simp [hinit]) hprevLo.le
          (by omega)⟩
      · -- Lengthen `previous` through the input and merge from `index`.
        rename_i hextends
        simp only [NR.length] at hextends
        obtain ⟨horder, hunion⟩ := mergeFollowing_preserves_order_and_union init
          (NR.ofStartStop previous.val.lo (previous.val.lo + (start - previous.val.lo + length))
            (by omega))
          right hpwInit
          (fun nr hnr => hinitPrev nr hnr previous (List.mem_singleton_self _))
          hpwRight
          (fun nr hnr => (hprevLo.trans_le (hright nr hnr)).le)
        rw [hinit, List.dropLast_concat]
        refine ⟨horder, ?_⟩
        -- The lengthened range is `previous` together with the input.
        have hlengthened :
            Set.Ico previous.val.lo (previous.val.lo + (start - previous.val.lo + length)) =
              Set.Ico previous.val.lo previous.stop ∪ Set.Ico start (start + length) := by
          ext x
          simp only [Set.mem_Ico, Set.mem_union]
          omega
        rw [hunion, NR.ofStartStop_toSet, hlengthened, ← previous.toSet_eq_Ico]
        simp only [rangesToSet_append, rangesToSet_cons, rangesToSet_nil, Set.union_empty]
        ac_rfl
    · -- A true gap after `previous`: insert at `index`.
      rename_i hgap
      have hprevBefore : previous ≺ input := by
        change previous.stop < start
        omega
      refine hinsert fun nr hnr => ?_
      rw [hinit, List.mem_append, List.mem_singleton] at hnr
      rcases hnr with hnr | rfl
      · exact NR.before_trans (hinitPrev nr hnr previous (List.mem_singleton_self _))
          hprevBefore
      · exact hprevBefore

/-- The Python list computation preserves canonical order and adds exactly
`[start, start + length)`. -/
private theorem internalAddPyNRs_preserves_order_and_union
    (ranges : List NR) (start length : Int) (hlength : 0 < length)
    (hpw : List.Pairwise NR.before ranges) :
    List.Pairwise NR.before (internalAddPyNRs ranges start length hlength) ∧
      rangesToSet (internalAddPyNRs ranges start length hlength) =
        rangesToSet ranges ∪ Set.Ico start (start + length) := by
  obtain ⟨hsplit, hleft, hright⟩ := bisectLeft_spec start ranges hpw
  unfold internalAddPyNRs
  generalize bisectLeft start ranges = split at hsplit hleft hright ⊢
  obtain ⟨left, right⟩ := split
  have hother := addAfterPredecessor_preserves_order_and_union ranges left right
    start length hlength hpw hsplit hleft hright
  cases right with
  | nil => exact hother
  | cons existing following =>
      dsimp only
      split
      · -- A range already starts at `start`.
        rename_i hexact
        subst hsplit
        split
        · -- `length <= _start_to_length[start]`: already covered.
          rename_i hcovered
          simp only [NR.length] at hcovered
          exact ⟨hpw, rangesToSet_union_Ico_of_covered (by simp) hexact.le (by omega)⟩
        · -- Lengthen the range at `start` and merge from `index + 1`.
          rename_i hlonger
          simp only [NR.length] at hlonger
          obtain ⟨hpwLeft, hpwRight, hcross⟩ := List.pairwise_append.mp hpw
          obtain ⟨horder, hunion⟩ := mergeFollowing_preserves_order_and_union
            left (NR.ofStartStop start (start + length) (by omega)) following hpwLeft
            (fun nr hnr => by
              have hbefore := hcross nr hnr existing List.mem_cons_self
              rw [NR.before, hexact] at hbefore
              exact hbefore)
            hpwRight.tail
            (fun nr hnr => hright nr (List.mem_cons_of_mem _ hnr))
          refine ⟨horder, ?_⟩
          -- The lengthened range at `start` contains the one it replaces.
          have hexistingSub : existing.val.toSet ⊆ Set.Ico start (start + length) := by
            rw [existing.toSet_eq_Ico, hexact]
            exact Set.Ico_subset_Ico_right (by omega)
          rw [hunion, NR.ofStartStop_toSet, rangesToSet_append, rangesToSet_cons]
          ext x
          have hsub := @hexistingSub x
          simp only [Set.mem_union]
          tauto
      · exact hother

/-! ## Public interface -/

/-- Python `IntRangeSet._internal_add(start, length)`, including its
`length > 0` precondition, on a canonical range set. -/
def internalAddPy (s : RangeSetBlaze) (start length : Int) (hlength : 0 < length) :
    RangeSetBlaze :=
  ⟨internalAddPyNRs s.ranges start length hlength,
    (internalAddPyNRs_preserves_order_and_union s.ranges start length hlength
      s.canonical).1⟩

/-- Python `_internal_add(start, length)` adds exactly the half-open interval
`[start, start + length)`. -/
theorem internalAddPy_toSet (s : RangeSetBlaze) (start length : Int)
    (hlength : 0 < length) :
    (internalAddPy s start length hlength).toSet =
      s.toSet ∪ Set.Ico start (start + length) :=
  (internalAddPyNRs_preserves_order_and_union s.ranges start length hlength
    s.canonical).2

/-- After `_internal_add`, Python's representation invariants hold, stated in
Python's vocabulary: every stored length is positive, `_start_items` is
strictly increasing (so sorted with unique keys), and every range's `stop` is
strictly below every later start (so ranges neither overlap nor touch). -/
theorem internalAddPy_python_invariants (s : RangeSetBlaze) (start length : Int)
    (hlength : 0 < length) :
    let ranges := (internalAddPy s start length hlength).ranges
    (∀ nr ∈ ranges, 0 < nr.length) ∧
      (ranges.map (fun nr => nr.val.lo)).Pairwise (· < ·) ∧
      ranges.Pairwise (fun a b => a.stop < b.val.lo) := by
  have hcanonical := (internalAddPy s start length hlength).canonical
  exact ⟨fun nr _ => nr.length_pos,
    List.pairwise_map.mpr (hcanonical.imp NR.before_lo_lt),
    hcanonical⟩

end RangeSetBlaze
