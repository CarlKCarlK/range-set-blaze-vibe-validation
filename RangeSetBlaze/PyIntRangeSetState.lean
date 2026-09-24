import RangeSetBlaze.PyIntRangeSet
import RangeSetBlaze.Canonical
import Mathlib.Data.Set.Card

/-!
# PySnpTools `IntRangeSet` state refinement

`RangeSetBlaze/PyIntRangeSet.lean` proves Python's insertion algorithm on the
list of ranges that Python's two fields denote.  This module models the two
fields themselves and proves that Python's mutations of both refine that list
model:

```text
Python state: sorted `_start_items` + dict `_start_to_length` + invariants
        ↓  Python-shaped mutations of both fields (`internalAdd`)
abstraction `Represents` to canonical ordered ranges (`RangeSetBlaze`)
```

## State

`PyIntRangeSet` has Python's two fields.  The dictionary is a partial
function `Int → Option Int`: Python only reads, writes, and deletes single
keys, which are function application and `Function.update` to `some` or
`none`.  A read of a missing key is Python's `KeyError`, and an out-of-range
list read is `IndexError`; both, and failed `assert`s, make `internalAdd`
return `none`.

## Invariants and abstraction

`Represents py s` says that `_start_items` is the list of starts of `s`'s
ranges, in order, and `_start_to_length` is exactly the table from each start
to its range's length.  Python's synchronization invariants are not left
implicit in that relation: `Represents.invariant` derives each of them as a
named field of `Invariant` —

* `_start_items` is strictly increasing, so sorted and duplicate-free;
* its elements are exactly the keys of `_start_to_length`, so the two have
  the same size (Python's `len(...) == len(...)` assertion);
* every stored length is positive;
* every stored range stops strictly before each later start.

Conversely `Invariant.exists_represents` shows these invariants are all that
`Represents` requires, and `Represents.unique` shows the abstraction is a
function.

## Refinement

`internalAdd_refines` proves that on a represented state Python's
`_internal_add(start, length)` never raises and its result represents
`internalAddPy s start length`, whose correctness is proved in
`PyIntRangeSet.lean`.  `internalAdd_spec` restates the result in Python's
vocabulary alone: from any state satisfying `Invariant`, `_internal_add`
preserves `Invariant` and adds exactly `[start, start + length)`.

The proof follows Python's branches one by one against the list model's.
Each Python mutation edits one stored range at one list position: inserting
a new start (`insert_stores`), assigning a new length to a stored start
(`assignLength_stores`), or deleting an absorbed start inside the merge loop
(`mergeLoop_stores`).  On the dictionary each is one `Function.update`
(`startToLengthOf_append_cons`); while stored starts are distinct, a lookup
finds the stored range (`startToLengthOf_of_mem`).  During the merge loop the
stored ranges overlap, so the loop invariant is `Stores` with distinct
starts, not `Represents`.

## Testing

`RangeSetBlaze/Regression.lean` checks `internalAdd` against the real Python
`_start_items` and `_start_to_length` after every generated call, and
`scripts/mutate_py_intrangeset_state.py` checks that one-line mutants of this
module are rejected by the proofs, by those tests, or both.
-/

namespace RangeSetBlaze

open IntRange
open scoped IntRange.NR

/-! ## Python's state -/

/-- The two fields of PySnpTools `IntRangeSet`. -/
structure PyIntRangeSet where
  /-- `_start_items`: the start of every stored range. -/
  startItems : List Int
  /-- `_start_to_length`: a dictionary from start to range length. -/
  startToLength : Int → Option Int

namespace PyIntRangeSet

/-- `IntRangeSet()`: both fields empty. -/
def empty : PyIntRangeSet := ⟨[], fun _ => none⟩

/-- The `_start_to_length` dictionary that stores `ranges`: each start maps to
its range's length.  When starts repeat the first range wins, but every state
this module reaches has distinct starts. -/
def startToLengthOf : List NR → Int → Option Int
  | [] => fun _ => none
  | r :: rs => Function.update (startToLengthOf rs) r.val.lo (some r.length)

/-- The fields store exactly `ranges`, in order: `_start_items` lists their
starts and `_start_to_length` is their start-to-length table.  During the
merge loop the stored ranges may overlap; `Represents` is the canonical case. -/
structure Stores (py : PyIntRangeSet) (ranges : List NR) : Prop where
  startItems_eq : py.startItems = ranges.map (·.val.lo)
  startToLength_eq : py.startToLength = startToLengthOf ranges

/-- The abstraction from Python's state to ordered ranges: `py` stores
exactly the canonical ranges of `s`. -/
abbrev Represents (py : PyIntRangeSet) (s : RangeSetBlaze) : Prop :=
  Stores py s.ranges

/-- Python's representation invariants on the two fields. -/
structure Invariant (py : PyIntRangeSet) : Prop where
  /-- `_start_items` is strictly increasing: sorted, with no duplicates. -/
  startItems_sorted : py.startItems.SortedLT
  /-- The elements of `_start_items` are exactly the keys of
  `_start_to_length`. -/
  mem_startItems_iff : ∀ k, k ∈ py.startItems ↔ (py.startToLength k).isSome
  /-- Every stored length is positive. -/
  length_pos : ∀ k length, py.startToLength k = some length → 0 < length
  /-- Every stored range `[start, start + length)` stops strictly before each
  later start: stored ranges neither overlap nor touch. -/
  stop_lt_later_start : py.startItems.Pairwise fun start next =>
    ∀ length, py.startToLength start = some length → start + length < next

/-! ## Python's algorithm -/

/-- Python's `bisect_left(_start_items, start)`: on a sorted list, the number
of items less than `start`. -/
def bisectLeft (items : List Int) (start : Int) : Nat :=
  (items.takeWhile (· < start)).length

/-- Python's merge loop, from the `if index == len(self._start_items)` early
return onward:

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
-/
def mergeLoop (previous : Int) (index : Nat) (stop : Int) (py : PyIntRangeSet) :
    Option PyIntRangeSet :=
  if hindex : index < py.startItems.length then
    let next := py.startItems[index]
    if next ≤ stop then do
      let nextLength ← py.startToLength next
      let newStop := max stop (next + nextLength)
      mergeLoop previous index newStop
        { startItems := py.startItems.eraseIdx index
          startToLength :=
            Function.update
              (Function.update py.startToLength previous (some (newStop - previous)))
              next none }
    else
      some py
  else
    some py
termination_by py.startItems.length - index
decreasing_by
  simp only [List.length_eraseIdx_of_lt hindex]
  omega

/-- Python's branches after the exact-start test fails: `index == 0`, or
inspect `previous = _start_items[index - 1]`. -/
def addAfterPrevious (py : PyIntRangeSet) (index : Nat) (start length : Int) :
    Option PyIntRangeSet :=
  if index = 0 then
    mergeLoop start (index + 1) (start + length)
      { startItems := py.startItems.insertIdx index start
        startToLength := Function.update py.startToLength start (some length) }
  else do
    let previous ← py.startItems[index - 1]?
    let previousLength ← py.startToLength previous
    let stop := previous + previousLength
    if start ≤ stop then
      let newLength := start - previous + length
      if newLength ≤ 0 then none  -- `assert new_length > 0`
      else if newLength < previousLength then some py
      else
        mergeLoop previous index (previous + newLength)
          { py with
            startToLength := Function.update py.startToLength previous (some newLength) }
    else
      mergeLoop start (index + 1) (start + length)
        { startItems := py.startItems.insertIdx index start
          startToLength := Function.update py.startToLength start (some length) }

/-- Python `IntRangeSet._internal_add(start, length)` on both fields.  `none`
is a raised `AssertionError`, `KeyError`, or `IndexError`. -/
def internalAdd (py : PyIntRangeSet) (start length : Int) : Option PyIntRangeSet :=
  if length ≤ 0 then none  -- `assert length > 0`
  else
    let index := bisectLeft py.startItems start
    if py.startItems[index]? = some start then do
      let existingLength ← py.startToLength start
      if length ≤ existingLength then some py
      else
        mergeLoop start (index + 1) (start + length)
          { py with startToLength := Function.update py.startToLength start (some length) }
    else
      addAfterPrevious py index start length

/-! ## The stored dictionary -/

/-- Only stored starts are keys of the dictionary. -/
lemma isSome_startToLengthOf_iff (ranges : List NR) (k : Int) :
    (startToLengthOf ranges k).isSome ↔ k ∈ ranges.map (·.val.lo) := by
  induction ranges with
  | nil => simp [startToLengthOf]
  | cons r rs ih =>
      by_cases hk : k = r.val.lo
      · simp [startToLengthOf, hk]
      · simp [startToLengthOf, hk, ih]

/-- Every dictionary entry is the start and length of a stored range. -/
lemma exists_mem_of_startToLengthOf_eq_some {ranges : List NR} {k length : Int}
    (h : startToLengthOf ranges k = some length) :
    ∃ r ∈ ranges, r.val.lo = k ∧ r.length = length := by
  induction ranges with
  | nil => simp [startToLengthOf] at h
  | cons r rs ih =>
      by_cases hk : k = r.val.lo
      · simp only [startToLengthOf, hk, Function.update_self, Option.some.injEq] at h
        exact ⟨r, List.mem_cons_self, hk.symm, h⟩
      · simp only [startToLengthOf, Function.update_of_ne hk] at h
        obtain ⟨r', hr', hlo, hlength⟩ := ih h
        exact ⟨r', List.mem_cons_of_mem _ hr', hlo, hlength⟩

/-- Storing one range at one list position is one dictionary assignment,
provided no earlier range has the same start.  This is the common form of
every Python mutation: an assignment to an existing start replaces the range
there, an assignment to a new start inserts it, and `del` removes it. -/
lemma startToLengthOf_append_cons (before after : List NR) (r : NR)
    (hfresh : r.val.lo ∉ before.map (·.val.lo)) :
    startToLengthOf (before ++ r :: after) =
      Function.update (startToLengthOf (before ++ after)) r.val.lo (some r.length) := by
  induction before with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at hfresh
      simp only [List.cons_append, startToLengthOf, ih hfresh.2]
      exact Function.update_comm hfresh.1 _ _ _

/-- With distinct starts, a stored range's start is not an earlier start. -/
lemma start_not_mem_earlier_starts {before after : List NR} {r : NR}
    (hdistinct : ((before ++ r :: after).map (·.val.lo)).Nodup) :
    r.val.lo ∉ before.map (·.val.lo) := by
  simp only [List.map_append, List.map_cons, List.nodup_middle, List.nodup_cons,
    List.mem_append, not_or] at hdistinct
  exact hdistinct.1.1

/-- With distinct starts, looking up a stored range's start finds its length. -/
lemma startToLengthOf_of_mem {ranges : List NR} {r : NR}
    (hdistinct : (ranges.map (·.val.lo)).Nodup) (hr : r ∈ ranges) :
    startToLengthOf ranges r.val.lo = some r.length := by
  obtain ⟨before, after, rfl⟩ := List.append_of_mem hr
  rw [startToLengthOf_append_cons _ _ _ (start_not_mem_earlier_starts hdistinct),
    Function.update_self]

/-- Canonical ranges have distinct starts. -/
lemma nodup_starts_of_canonical {ranges : List NR}
    (hcanonical : List.Pairwise NR.before ranges) :
    (ranges.map (·.val.lo)).Nodup :=
  List.pairwise_map.mpr (hcanonical.imp fun h => (NR.before_lo_lt h).ne)

/-! ## Python's invariants from the abstraction -/

/-- The integers Python's fields denote: every stored
`[start, start + _start_to_length[start])`. -/
def toSet (py : PyIntRangeSet) : Set Int :=
  {x | ∃ start length, py.startToLength start = some length ∧ start ≤ x ∧ x < start + length}

namespace Represents

variable {py : PyIntRangeSet} {s : RangeSetBlaze}

/-- `_start_items` is sorted, strictly: its starts are those of `s`'s
canonical ranges, in order. -/
theorem startItems_sorted (h : Represents py s) : py.startItems.SortedLT := by
  rw [h.startItems_eq, List.sortedLT_iff_pairwise, List.pairwise_map]
  exact s.canonical.imp NR.before_lo_lt

/-- The elements of `_start_items` are exactly the keys of
`_start_to_length`. -/
theorem mem_startItems_iff (h : Represents py s) (k : Int) :
    k ∈ py.startItems ↔ (py.startToLength k).isSome := by
  rw [h.startItems_eq, h.startToLength_eq, isSome_startToLengthOf_iff]

/-- Every stored length is positive. -/
theorem length_pos (h : Represents py s) {k length : Int}
    (hk : py.startToLength k = some length) : 0 < length := by
  rw [h.startToLength_eq] at hk
  obtain ⟨r, -, -, rfl⟩ := exists_mem_of_startToLengthOf_eq_some hk
  exact r.length_pos

/-- Every stored range stops strictly before each later start. -/
theorem stop_lt_later_start (h : Represents py s) :
    py.startItems.Pairwise fun start next =>
      ∀ length, py.startToLength start = some length → start + length < next := by
  rw [h.startItems_eq, List.pairwise_map]
  refine s.canonical.imp_of_mem fun {a _} ha _ hbefore length hlength => ?_
  rw [h.startToLength_eq, startToLengthOf_of_mem (nodup_starts_of_canonical s.canonical) ha,
    Option.some.injEq] at hlength
  rw [← hlength, a.lo_add_length]
  exact hbefore

/-- A represented state satisfies all of Python's invariants. -/
theorem invariant (h : Represents py s) : Invariant py :=
  ⟨h.startItems_sorted, h.mem_startItems_iff, fun _ _ => h.length_pos,
    h.stop_lt_later_start⟩

/-- Python's fields and the abstract ranges denote the same integers. -/
theorem toSet_eq (h : Represents py s) : py.toSet = s.toSet := by
  ext x
  simp only [toSet, Set.mem_ofPred_eq, toSet_eq_rangesToSet, mem_rangesToSet_iff,
    h.startToLength_eq]
  constructor
  · rintro ⟨_, _, hk, hlo, hhi⟩
    obtain ⟨r, hr, rfl, rfl⟩ := exists_mem_of_startToLengthOf_eq_some hk
    rw [r.lo_add_length, NR.stop] at hhi
    exact ⟨r, hr, hlo, by omega⟩
  · rintro ⟨r, hr, hlo, hhi⟩
    refine ⟨r.val.lo, r.length,
      startToLengthOf_of_mem (nodup_starts_of_canonical s.canonical) hr, hlo, ?_⟩
    rw [r.lo_add_length, NR.stop]
    omega

/-- The abstraction is a function: a state represents at most one range set. -/
theorem unique {s' : RangeSetBlaze} (h : Represents py s) (h' : Represents py s') :
    s = s' := by
  have hranges := ranges_eq_of_canonical_of_rangesToSet_eq s.canonical s'.canonical
    (by rw [← toSet_eq_rangesToSet, ← toSet_eq_rangesToSet, ← h.toSet_eq, h'.toSet_eq])
  cases s
  cases s'
  simpa using hranges

end Represents

namespace Invariant

variable {py : PyIntRangeSet}

/-- `_start_items` has no duplicates. -/
theorem startItems_nodup (h : Invariant py) : py.startItems.Nodup :=
  h.startItems_sorted.pairwise.imp ne_of_lt

/-- Python's `assert len(self._start_items) == len(self._start_to_length)`. -/
theorem ncard_keys_eq_length (h : Invariant py) :
    Set.ncard {k : Int | (py.startToLength k).isSome} = py.startItems.length := by
  have hkeys : {k : Int | (py.startToLength k).isSome} = ↑py.startItems.toFinset := by
    ext k
    simp [h.mem_startItems_iff]
  rw [hkeys, Set.ncard_coe_finset, List.toFinset_card_of_nodup h.startItems_nodup]

end Invariant

/-- The ranges Python's fields store, read in `_start_items` order. -/
def storedRanges (py : PyIntRangeSet) : List NR :=
  py.startItems.filterMap fun start =>
    (py.startToLength start).bind fun length =>
      if h : 0 < length then some (NR.ofStartStop start (start + length) (by omega)) else none

/-- Under Python's invariants the fields store `storedRanges`, which are
canonical: the invariants are all that the abstraction requires. -/
theorem Invariant.exists_represents {py : PyIntRangeSet} (h : Invariant py) :
    ∃ s, Represents py s := by
  have hstored (k : Int) (hk : k ∈ py.startItems) :
      ∃ length, py.startToLength k = some length ∧ 0 < length := by
    obtain ⟨length, hlength⟩ := Option.isSome_iff_exists.mp ((h.mem_startItems_iff k).mp hk)
    exact ⟨length, hlength, h.length_pos k length hlength⟩
  have hstarts : py.storedRanges.map (·.val.lo) = py.startItems := by
    rw [storedRanges, List.map_filterMap]
    refine (List.filterMap_congr fun k hk => ?_).trans List.filterMap_some
    obtain ⟨length, hlength, hpos⟩ := hstored k hk
    simp [hlength, hpos]
  have hcanonical : List.Pairwise NR.before py.storedRanges := by
    refine List.pairwise_filterMap.mpr (h.stop_lt_later_start.imp fun hstop r hr r' hr' => ?_)
    simp only [Option.bind_eq_some_iff, Option.dite_none_right_eq_some,
      Option.some.injEq] at hr hr'
    obtain ⟨length, hlength, -, rfl⟩ := hr
    obtain ⟨_, -, -, rfl⟩ := hr'
    have := hstop length hlength
    simp only [NR.before, NR.ofStartStop]
    omega
  refine ⟨⟨py.storedRanges, hcanonical⟩, hstarts.symm, ?_⟩
  funext k
  by_cases hk : k ∈ py.startItems
  · obtain ⟨length, hlength, hpos⟩ := hstored k hk
    have hmem : NR.ofStartStop k (k + length) (by omega) ∈ py.storedRanges :=
      List.mem_filterMap.mpr ⟨k, hk, by simp [hlength, hpos]⟩
    have := startToLengthOf_of_mem (hstarts ▸ h.startItems_nodup) hmem
    simp only [NR.lo_ofStartStop, NR.length_ofStartStop, add_sub_cancel_left] at this
    rw [hlength, this]
  · rw [Option.eq_none_iff_forall_not_mem.mpr fun _ hsome =>
        hk ((h.mem_startItems_iff k).mpr (Option.isSome_iff_exists.mpr ⟨_, hsome⟩)),
      eq_comm, ← Option.not_isSome_iff_eq_none, isSome_startToLengthOf_iff, hstarts]
    exact hk

/-! ## The merge loop -/

/-- Python's merge loop, run with `previous` and `stop` read from `current`
and `index` just after it, performs the abstract merge loop on the stored
ranges.  The stored ranges need only distinct starts: `current` may overlap
the ranges that follow it. -/
private theorem mergeLoop_stores (untouched : List NR) (current : NR) (following : List NR)
    (py : PyIntRangeSet)
    (hdistinct : ((untouched ++ current :: following).map (·.val.lo)).Nodup)
    (hpy : Stores py (untouched ++ current :: following)) :
    ∃ py', mergeLoop current.val.lo (untouched.length + 1) current.stop py = some py' ∧
      Stores py' (mergeFollowing untouched current following) := by
  induction following generalizing current py with
  | nil =>
      refine ⟨py, ?_, by simpa [mergeFollowing, absorbFollowing] using hpy⟩
      rw [mergeLoop, dif_neg (by simp [hpy.startItems_eq])]
  | cons next rest ih =>
      have hitems := hpy.startItems_eq
      have hindex : untouched.length + 1 < py.startItems.length := by simp [hitems]
      rw [mergeLoop, dif_pos hindex]
      have hnext : py.startItems[untouched.length + 1] = next.val.lo := by
        simp [hitems, List.getElem_append_right]
      simp only [hnext]
      by_cases htouch : next.val.lo ≤ current.stop
      · -- One iteration: `current` absorbs `next`, which is deleted from both fields.
        have hfresh : current.val.lo ∉ untouched.map (·.val.lo) ∧
            next.val.lo ∉ untouched.map (·.val.lo) ∧ next.val.lo ≠ current.val.lo ∧
            next.val.lo ∉ rest.map (·.val.lo) := by
          simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons,
            List.mem_cons] at hdistinct
          grind
        have hnextLength : py.startToLength next.val.lo = some next.length := by
          rw [hpy.startToLength_eq]
          exact startToLengthOf_of_mem hdistinct (by simp)
        rw [if_pos htouch]
        simp only [hnextLength, Option.bind_eq_bind, Option.bind_some, next.lo_add_length]
        let merged := NR.ofStartStop current.val.lo (max current.stop next.stop)
          (lt_max_of_lt_left current.lo_lt_stop)
        have hstep : mergeFollowing untouched current (next :: rest) =
            mergeFollowing untouched merged rest := by
          simp [mergeFollowing, absorbFollowing, htouch, merged]
        obtain ⟨py', hloop, hstores⟩ := ih merged
          { startItems := py.startItems.eraseIdx (untouched.length + 1)
            startToLength :=
              Function.update
                (Function.update py.startToLength current.val.lo
                  (some (max current.stop next.stop - current.val.lo)))
                next.val.lo none }
          (hdistinct.sublist (by simp [merged]))
          ⟨by simp [hitems, merged, List.eraseIdx_append_of_length_le], by
            have hgone : startToLengthOf (untouched ++ rest) next.val.lo = none := by
              rw [← Option.not_isSome_iff_eq_none, isSome_startToLengthOf_iff]
              rw [List.map_append, List.mem_append]
              exact not_or.mpr ⟨hfresh.2.1, hfresh.2.2.2⟩
            rw [hpy.startToLength_eq, startToLengthOf_append_cons _ _ _ hfresh.1,
              startToLengthOf_append_cons _ _ _ hfresh.2.1,
              startToLengthOf_append_cons _ _ merged hfresh.1]
            funext k
            simp only [Function.update_apply]
            split_ifs <;> simp_all [merged]⟩
        exact ⟨py', by simpa [merged] using hloop, hstep ▸ hstores⟩
      · rw [if_neg htouch]
        refine ⟨py, rfl, ?_⟩
        simpa [mergeFollowing, absorbFollowing, htouch] using hpy

/-! ## The branches before the merge loop -/

/-- On stored starts, `bisect_left` is the length of the abstract split's
prefix. -/
private lemma bisectLeft_starts (ranges : List NR) (start : Int) :
    bisectLeft (ranges.map (·.val.lo)) start =
      (RangeSetBlaze.bisectLeft start ranges).1.length := by
  simp only [bisectLeft, RangeSetBlaze.bisectLeft, List.takeWhile_map, List.length_map,
    List.span_eq_takeWhile_dropWhile]
  rfl

private lemma insertIdx_length_append {α : Type*} (before after : List α) (x : α) :
    (before ++ after).insertIdx before.length x = before ++ x :: after := by
  induction before with
  | nil => simp [List.insertIdx_zero]
  | cons a before ih => simp [List.insertIdx_succ_cons, ih]

/-- Python's insertion of `[start, start + length)` at `index` into both
fields stores the input range there, keeping starts distinct. -/
private lemma insert_stores (py : PyIntRangeSet) (left right : List NR)
    (start length : Int) (hlength : 0 < length)
    (hdistinct : ((left ++ right).map (·.val.lo)).Nodup)
    (hpy : Stores py (left ++ right))
    (hleft : ∀ nr ∈ left, nr.val.lo < start)
    (hright : ∀ nr ∈ right, start < nr.val.lo) :
    let input := NR.ofStartStop start (start + length) (by omega)
    ((left ++ input :: right).map (·.val.lo)).Nodup ∧
      Stores
        { startItems := py.startItems.insertIdx left.length start
          startToLength := Function.update py.startToLength start (some length) }
        (left ++ input :: right) := by
  intro input
  have hfresh : start ∉ (left ++ right).map (·.val.lo) := by
    simp only [List.map_append, List.mem_append, List.mem_map, not_or]
    exact ⟨fun ⟨nr, hnr, h⟩ => (hleft nr hnr).ne h,
      fun ⟨nr, hnr, h⟩ => (hright nr hnr).ne' h⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.map_append, List.map_cons, List.nodup_middle, List.nodup_cons]
    exact ⟨by simpa [input] using hfresh, by simpa using hdistinct⟩
  · rw [hpy.startItems_eq, List.map_append, ← List.length_map (f := (·.val.lo)),
      insertIdx_length_append]
    simp [input]
  · rw [hpy.startToLength_eq, startToLengthOf_append_cons _ _ input
      (fun h => hfresh (by simp only [List.map_append]; exact List.mem_append_left _ h))]
    simp [input]

/-- Python's `_start_to_length[start] = length` for a stored `start`
replaces that stored range in place by `[start, start + length)`. -/
private lemma assignLength_stores (py : PyIntRangeSet) (before after : List NR) (old : NR)
    (length : Int) (hlength : 0 < length)
    (hdistinct : ((before ++ old :: after).map (·.val.lo)).Nodup)
    (hpy : Stores py (before ++ old :: after)) :
    let lengthened := NR.ofStartStop old.val.lo (old.val.lo + length) (by omega)
    ((before ++ lengthened :: after).map (·.val.lo)).Nodup ∧
      Stores
        { py with startToLength := Function.update py.startToLength old.val.lo (some length) }
        (before ++ lengthened :: after) := by
  intro lengthened
  have hfresh := start_not_mem_earlier_starts hdistinct
  refine ⟨by simpa [lengthened] using hdistinct, by simp [hpy.startItems_eq, lengthened], ?_⟩
  rw [hpy.startToLength_eq, startToLengthOf_append_cons _ _ _ hfresh,
    startToLengthOf_append_cons _ _ lengthened hfresh, Function.update_idem]
  simp [lengthened]

/-- Python's branches when no stored range starts exactly at `start` perform
the corresponding abstract branches. -/
private theorem addAfterPrevious_stores (py : PyIntRangeSet) (left right : List NR)
    (start length : Int) (hlength : 0 < length)
    (hcanonical : List.Pairwise NR.before (left ++ right))
    (hpy : Stores py (left ++ right))
    (hleft : ∀ nr ∈ left, nr.val.lo < start)
    (hright : ∀ nr ∈ right, start < nr.val.lo) :
    ∃ py', addAfterPrevious py left.length start length = some py' ∧
      Stores py' (addAfterPredecessor (left ++ right) left right start length hlength) := by
  have hdistinct := nodup_starts_of_canonical hcanonical
  -- Both inserting branches store the input at `index` and run the loop.
  have hinsert :
      ∃ py', mergeLoop start (left.length + 1) (start + length)
          { startItems := py.startItems.insertIdx left.length start
            startToLength := Function.update py.startToLength start (some length) } =
            some py' ∧
        Stores py' (mergeFollowing left
          (NR.ofStartStop start (start + length) (by omega)) right) := by
    obtain ⟨hdistinct', hstores⟩ :=
      insert_stores py left right start length hlength hdistinct hpy hleft hright
    simpa using mergeLoop_stores left _ right _ hdistinct' hstores
  unfold addAfterPrevious addAfterPredecessor
  rcases List.eq_nil_or_concat left with rfl | ⟨init, previous, rfl⟩
  all_goals simp only [List.concat_eq_append] at *
  · simpa using hinsert
  · -- `previous = _start_items[index - 1]` is the last range before `index`.
    have hprevLo : previous.val.lo < start := hleft previous (by simp)
    have hprevLength : py.startToLength previous.val.lo = some previous.length := by
      rw [hpy.startToLength_eq]
      exact startToLengthOf_of_mem hdistinct (by simp)
    have hitem : py.startItems[(init ++ [previous]).length - 1]? = some previous.val.lo := by
      simp [hpy.startItems_eq]
    rw [if_neg (by simp)]
    simp only [hitem, hprevLength, Option.bind_eq_bind, Option.bind_some,
      List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _), List.getLast?_singleton,
      previous.lo_add_length]
    by_cases htouch : start ≤ previous.stop
    swap
    · simpa [htouch] using hinsert
    have hpositive : ¬start - previous.val.lo + length ≤ 0 := by omega
    simp only [htouch, if_true, hpositive, if_false]
    by_cases hcovered : start - previous.val.lo + length < previous.length
    · simpa [hcovered] using hpy
    · simp only [hcovered, if_false, dite_false]
      -- Lengthen `previous` in the dictionary and merge from `index`.
      simp only [List.append_assoc, List.singleton_append] at hpy hdistinct
      obtain ⟨hdistinct', hstores⟩ := assignLength_stores py init right previous
        (start - previous.val.lo + length) (by omega) hdistinct hpy
      simpa using mergeLoop_stores init _ right _ hdistinct' hstores

/-! ## Refinement -/

/-- Python's `_internal_add` on fields storing canonical `ranges` never
raises, and stores the abstract model's result. -/
private theorem internalAdd_stores (py : PyIntRangeSet) (ranges : List NR)
    (hcanonical : List.Pairwise NR.before ranges) (hpy : Stores py ranges)
    (start length : Int) (hlength : 0 < length) :
    ∃ py', internalAdd py start length = some py' ∧
      Stores py' (internalAddPyNRs ranges start length hlength) := by
  obtain ⟨hsplit, hleft, hright⟩ := RangeSetBlaze.bisectLeft_spec start ranges hcanonical
  have hindex : bisectLeft py.startItems start =
      (RangeSetBlaze.bisectLeft start ranges).1.length := by
    rw [hpy.startItems_eq, bisectLeft_starts]
  unfold internalAdd internalAddPyNRs
  rw [if_neg (not_le.mpr hlength)]
  simp only [hindex]
  generalize RangeSetBlaze.bisectLeft start ranges = split at hsplit hleft hright ⊢
  obtain ⟨left, right⟩ := split
  dsimp only at hsplit hleft hright ⊢
  subst hsplit
  have hdistinct := nodup_starts_of_canonical hcanonical
  -- Every branch except the exact-start one is `addAfterPrevious`.
  have hother (hne : ∀ nr ∈ right, nr.val.lo ≠ start) :=
    addAfterPrevious_stores py left right start length hlength hcanonical hpy hleft
      fun nr hnr => lt_of_le_of_ne (hright nr hnr) (hne nr hnr).symm
  cases right with
  | nil =>
      rw [if_neg (by simp [hpy.startItems_eq])]
      exact hother (by simp)
  | cons existing following =>
      have hitem : py.startItems[left.length]? = some existing.val.lo := by
        simp [hpy.startItems_eq]
      rw [hitem]
      by_cases hexact : existing.val.lo = start
      swap
      · rw [if_neg (by simpa using hexact)]
        simp only [hexact, if_false]
        refine hother fun nr hnr => ?_
        rcases List.mem_cons.mp hnr with rfl | hfollowing
        · exact hexact
        · have hbefore := List.rel_of_pairwise_cons
            (List.pairwise_append.mp hcanonical).2.1 hfollowing
          exact (lt_of_le_of_lt (hright existing List.mem_cons_self)
            (NR.before_lo_lt hbefore)).ne'
      -- A range already starts at `start`.
      have hexistingLength : py.startToLength start = some existing.length := by
        rw [hpy.startToLength_eq, ← hexact]
        exact startToLengthOf_of_mem hdistinct (by simp)
      simp only [hexact, if_true, hexistingLength, Option.bind_eq_bind, Option.bind_some]
      by_cases hcovered : length ≤ existing.length
      · simpa [hcovered] using hpy
      simp only [hcovered, if_false]
      -- Lengthen the range at `start` and merge from `index + 1`.
      obtain ⟨hdistinct', hstores⟩ :=
        assignLength_stores py left following existing length hlength hdistinct hpy
      simpa [hexact] using mergeLoop_stores left _ following _ hdistinct' hstores

/-! ## Public refinement and specification -/

/-- `IntRangeSet()` represents the empty range set. -/
theorem represents_empty : Represents empty ⟨[], List.Pairwise.nil⟩ := ⟨rfl, rfl⟩

/-- Python's `_internal_add(start, length)` on both fields refines the
list model: it never raises, and its result represents
`internalAddPy s start length`. -/
theorem internalAdd_refines {py : PyIntRangeSet} {s : RangeSetBlaze}
    (h : Represents py s) (start length : Int) (hlength : 0 < length) :
    ∃ py', internalAdd py start length = some py' ∧
      Represents py' (internalAddPy s start length hlength) :=
  internalAdd_stores py s.ranges s.canonical h start length hlength

/-- Correctness in Python's vocabulary alone: on fields satisfying Python's
invariants, `_internal_add(start, length)` does not raise, preserves the
invariants, and adds exactly `[start, start + length)`. -/
theorem internalAdd_spec {py : PyIntRangeSet} (h : Invariant py)
    (start length : Int) (hlength : 0 < length) :
    ∃ py', internalAdd py start length = some py' ∧ Invariant py' ∧
      py'.toSet = py.toSet ∪ Set.Ico start (start + length) := by
  obtain ⟨s, hs⟩ := h.exists_represents
  obtain ⟨py', hadd, hpy'⟩ := internalAdd_refines hs start length hlength
  exact ⟨py', hadd, hpy'.invariant, by rw [hpy'.toSet_eq, hs.toSet_eq, internalAddPy_toSet]⟩

end PyIntRangeSet

end RangeSetBlaze
