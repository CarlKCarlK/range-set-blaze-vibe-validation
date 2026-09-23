import RangeSetBlaze.Canonical

/-!
# `range_or_gap_at` query models

The production Rust collections range over a finite `Integer` domain and
return an inclusive range whose endpoints may be `T::min_value()` or
`T::max_value()`.  The repository models keys with mathematical `Int`, so the
finite domain endpoints are explicit parameters here.  This keeps successor
and predecessor arithmetic total while preserving the public Rust result
shape exactly for the dense-integer abstraction.
-/

/-- A closed interval containing `key` is the maximal part of `[lower, upper]`
on which `state` has the returned value. -/
def MaximalConstantInterval {State : Type*}
    (state : Int → State) (lower upper key : Int)
    (range : IntRange) (value : State) : Prop :=
  lower ≤ range.lo ∧ range.hi ≤ upper ∧
    range.lo ≤ key ∧ key ≤ range.hi ∧
    (∀ x, range.lo ≤ x → x ≤ range.hi → state x = value) ∧
    (range.lo = lower ∨ state (range.lo - 1) ≠ value) ∧
    (range.hi = upper ∨ state (range.hi + 1) ≠ value)

/-- A maximal constant interval and its state are unique. -/
theorem maximalConstantInterval_unique {State : Type*}
    {state : Int → State} {lower upper key : Int}
    {range₁ range₂ : IntRange} {value₁ value₂ : State}
    (h₁ : MaximalConstantInterval state lower upper key range₁ value₁)
    (h₂ : MaximalConstantInterval state lower upper key range₂ value₂) :
    range₁ = range₂ ∧ value₁ = value₂ := by
  rcases h₁ with ⟨h₁lower, h₁upper, h₁lo, h₁hi, h₁state, h₁left, h₁right⟩
  rcases h₂ with ⟨h₂lower, h₂upper, h₂lo, h₂hi, h₂state, h₂left, h₂right⟩
  have hvalue : value₁ = value₂ := by
    exact (h₁state key h₁lo h₁hi).symm.trans
      (h₂state key h₂lo h₂hi)
  have hlo : range₁.lo = range₂.lo := by
    apply le_antisymm
    · by_contra hnot
      have hlt : range₂.lo < range₁.lo := lt_of_not_ge hnot
      rcases h₁left with hboundary | hdifferent
      · omega
      · apply hdifferent
        rw [hvalue]
        exact h₂state (range₁.lo - 1) (by omega) (by omega)
    · by_contra hnot
      have hlt : range₁.lo < range₂.lo := lt_of_not_ge hnot
      rcases h₂left with hboundary | hdifferent
      · omega
      · apply hdifferent
        rw [← hvalue]
        exact h₁state (range₂.lo - 1) (by omega) (by omega)
  have hhi : range₁.hi = range₂.hi := by
    apply le_antisymm
    · by_contra hnot
      have hlt : range₂.hi < range₁.hi := lt_of_not_ge hnot
      rcases h₂right with hboundary | hdifferent
      · omega
      · apply hdifferent
        rw [← hvalue]
        exact h₁state (range₂.hi + 1) (by omega) (by omega)
    · by_contra hnot
      have hlt : range₁.hi < range₂.hi := lt_of_not_ge hnot
      rcases h₁right with hboundary | hdifferent
      · omega
      · apply hdifferent
        rw [hvalue]
        exact h₂state (range₁.hi + 1) (by omega) (by omega)
  exact ⟨by cases range₁; cases range₂; simp_all, hvalue⟩

namespace RangeSetBlaze

/-- Boolean membership state used by the set query specification. -/
noncomputable def queryState (set : RangeSetBlaze) (key : Int) : Bool :=
  by
    classical
    exact if key ∈ set.toSet then true else false

@[simp] theorem queryState_eq_true_iff (set : RangeSetBlaze) (key : Int) :
    set.queryState key = true ↔ key ∈ set.toSet := by
  classical
  change (if key ∈ rangesToSet set.ranges then true else false) = true ↔ _
  by_cases h : key ∈ rangesToSet set.ranges <;> simp [h]

@[simp] theorem queryState_eq_false_iff (set : RangeSetBlaze) (key : Int) :
    set.queryState key = false ↔ key ∉ set.toSet := by
  classical
  change (if key ∈ rangesToSet set.ranges then true else false) = false ↔ _
  by_cases h : key ∈ rangesToSet set.ranges <;> simp [h]

/-- The semantic contract shared by both production-shaped set queries. -/
def QueryResultSpec (set : RangeSetBlaze) (lower upper key : Int)
    (result : IntRange × Bool) : Prop :=
  MaximalConstantInterval set.queryState lower upper key result.1 result.2

/-- All stored set ranges lie inside the modeled finite Rust key domain. -/
def WithinDomain (set : RangeSetBlaze) (lower upper : Int) : Prop :=
  ∀ range ∈ set.ranges, lower ≤ range.val.lo ∧ range.val.hi ≤ upper

private theorem mem_rangesToSet_iff
    {ranges : List IntRange.NR} {key : Int} :
    key ∈ rangesToSet ranges ↔
      ∃ range ∈ ranges, range.val.lo ≤ key ∧ key ≤ range.val.hi := by
  induction ranges with
  | nil => simp
  | cons range rest ih =>
      simp only [rangesToSet_cons, Set.mem_union, IntRange.mem_toSet_iff, ih]
      constructor
      · rintro (h | h)
        · exact ⟨range, by simp, h⟩
        · rcases h with ⟨candidate, hmem, hcontains⟩
          exact ⟨candidate, by simp [hmem], hcontains⟩
      · rintro ⟨candidate, hmem, hcontains⟩
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Or.inl hcontains
        · exact Or.inr ⟨candidate, hmem, hcontains⟩

private theorem canonical_range_before_of_mem_before_last
    {initial : List IntRange.NR} {last candidate : IntRange.NR}
    (hcanonical : List.Pairwise IntRange.NR.before (initial ++ [last]))
    (hmem : candidate ∈ initial) : IntRange.NR.before candidate last := by
  exact (List.pairwise_append.mp hcanonical).2.2 candidate hmem last (by simp)

private theorem range_not_contains_between_neighbors
    {ranges left right : List IntRange.NR} {key : Int}
    (hcanonical : List.Pairwise IntRange.NR.before ranges)
    (hdecomp : ranges = left ++ right)
    (hleft : ∀ predecessor, left.getLast? = some predecessor →
      predecessor.val.hi < key)
    (hright : ∀ successor, right.head? = some successor →
      key < successor.val.lo) :
    key ∉ rangesToSet ranges := by
  rw [mem_rangesToSet_iff]
  rintro ⟨candidate, hmem, hcontains⟩
  rw [hdecomp] at hcanonical hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · by_cases hempty : left = []
    · simp [hempty] at hmem
    · let predecessor := left.getLast hempty
      have hlast : left.getLast? = some predecessor :=
        List.getLast?_eq_some_getLast hempty
      obtain ⟨initial, hdecompLeft⟩ := List.getLast?_eq_some_iff.mp hlast
      have hpredKey := hleft predecessor hlast
      rw [hdecompLeft, List.mem_append] at hmem
      rcases hmem with hprefix | hlastMem
      · have hbefore := canonical_range_before_of_mem_before_last
            (by simpa [hdecompLeft] using (List.pairwise_append.mp hcanonical).1) hprefix
        unfold IntRange.NR.before at hbefore
        have hnonempty := predecessor.property
        change predecessor.val.lo ≤ predecessor.val.hi at hnonempty
        omega
      · simp at hlastMem
        subst candidate
        omega
  · cases right with
    | nil => simp at hmem
    | cons successor tail =>
        have hsuccessorKey : key < successor.val.lo :=
          hright successor (by simp)
        have hrightCanonical : List.Pairwise IntRange.NR.before (successor :: tail) :=
          (List.pairwise_append.mp hcanonical).2.1
        rcases List.mem_cons.mp hmem with rfl | htail
        · omega
        · have hbefore := List.rel_of_pairwise_cons hrightCanonical htail
          have hlo := IntRange.NR.before_lo_lt hbefore
          omega

private theorem queryState_true_of_range_contains
    (set : RangeSetBlaze) {range : IntRange.NR} (hmem : range ∈ set.ranges)
    {key : Int} (hcontains : range.val.lo ≤ key ∧ key ≤ range.val.hi) :
    set.queryState key = true := by
  rw [queryState_eq_true_iff, toSet_eq_rangesToSet, mem_rangesToSet_iff]
  exact ⟨range, hmem, hcontains⟩

private theorem storedRange_queryResultSpec
    (set : RangeSetBlaze) (lower upper key : Int) (range : IntRange.NR)
    (hdomain : WithinDomain set lower upper)
    (hmem : range ∈ set.ranges)
    (hcontains : range.val.lo ≤ key ∧ key ≤ range.val.hi) :
    QueryResultSpec set lower upper key (range.val, true) := by
  obtain ⟨initial, remaining, hdecomp⟩ := List.mem_iff_append.mp hmem
  have hcanonical : List.Pairwise IntRange.NR.before
      (initial ++ range :: remaining) := by simpa [hdecomp] using set.canonical
  have hinitial := (List.pairwise_append.mp hcanonical).2.2
  have hremaining : ∀ candidate ∈ remaining,
      IntRange.NR.before range candidate := by
    intro candidate hc
    exact List.rel_of_pairwise_cons (List.pairwise_append.mp hcanonical).2.1 hc
  have hleftAbsent : range.val.lo - 1 ∉ set.toSet := by
    rw [toSet_eq_rangesToSet, mem_rangesToSet_iff]
    rintro ⟨candidate, hc, hcandidate⟩
    rw [hdecomp] at hc
    rcases List.mem_append.mp hc with hc | hc
    · have hbefore := hinitial candidate hc range (by simp)
      unfold IntRange.NR.before at hbefore
      omega
    · rcases List.mem_cons.mp hc with rfl | hc
      · omega
      · have hbefore := hremaining candidate hc
        have hnonempty := range.property
        change range.val.lo ≤ range.val.hi at hnonempty
        unfold IntRange.NR.before at hbefore
        omega
  have hrightAbsent : range.val.hi + 1 ∉ set.toSet := by
    rw [toSet_eq_rangesToSet, mem_rangesToSet_iff]
    rintro ⟨candidate, hc, hcandidate⟩
    rw [hdecomp] at hc
    rcases List.mem_append.mp hc with hc | hc
    · have hbefore := hinitial candidate hc range (by simp)
      unfold IntRange.NR.before at hbefore
      omega
    · rcases List.mem_cons.mp hc with rfl | hc
      · omega
      · have hbefore := hremaining candidate hc
        unfold IntRange.NR.before at hbefore
        omega
  have hrangeDomain := hdomain range hmem
  refine ⟨hrangeDomain.1, hrangeDomain.2, hcontains.1, hcontains.2,
    ?_, ?_, ?_⟩
  · intro x hlo hhi
    exact queryState_true_of_range_contains set hmem ⟨hlo, hhi⟩
  · by_cases hboundary : range.val.lo = lower
    · exact Or.inl hboundary
    · exact Or.inr (by simpa using
        (show set.queryState (range.val.lo - 1) = false from
          (queryState_eq_false_iff set _).mpr hleftAbsent))
  · by_cases hboundary : range.val.hi = upper
    · exact Or.inl hboundary
    · exact Or.inr (by simpa using
        (show set.queryState (range.val.hi + 1) = false from
          (queryState_eq_false_iff set _).mpr hrightAbsent))

private theorem gap_queryResultSpec
    (set : RangeSetBlaze) (lower upper key : Int) (gap : IntRange)
    (hdomainLower : lower ≤ gap.lo) (hdomainUpper : gap.hi ≤ upper)
    (hcontains : gap.lo ≤ key ∧ key ≤ gap.hi)
    (hempty : ∀ x, gap.lo ≤ x → x ≤ gap.hi → x ∉ set.toSet)
    (hleft : gap.lo = lower ∨ set.queryState (gap.lo - 1) ≠ false)
    (hright : gap.hi = upper ∨ set.queryState (gap.hi + 1) ≠ false) :
    QueryResultSpec set lower upper key (gap, false) := by
  refine ⟨hdomainLower, hdomainUpper, hcontains.1, hcontains.2, ?_, hleft, hright⟩
  intro x hlo hhi
  exact (queryState_eq_false_iff set _).mpr (hempty x hlo hhi)

private theorem nonstrictSplit_spec
    (ranges : List IntRange.NR) (key : Int)
    (hcanonical : List.Pairwise IntRange.NR.before ranges) :
    let split := List.span (fun range => decide (range.val.lo ≤ key)) ranges
    ranges = split.fst ++ split.snd ∧
      (∀ range ∈ split.fst, range.val.lo ≤ key) ∧
      (∀ range ∈ split.snd, key < range.val.lo) := by
  dsimp
  simp only [List.span_eq_takeWhile_dropWhile]
  refine ⟨(List.takeWhile_append_dropWhile).symm, ?_, ?_⟩
  · intro range hmem
    exact of_decide_eq_true (List.mem_takeWhile_imp
      (p := fun candidate : IntRange.NR => decide (candidate.val.lo ≤ key)) hmem)
  · induction ranges with
    | nil => simp
    | cons first rest ih =>
        by_cases hfirst : first.val.lo ≤ key
        · rw [List.dropWhile_cons_of_pos (by simp [hfirst])]
          exact ih hcanonical.tail
        · rw [List.dropWhile_cons_of_neg (by simp [hfirst])]
          intro range hmem
          rcases List.mem_cons.mp hmem with rfl | hmem
          · exact lt_of_not_ge hfirst
          · exact (lt_of_not_ge hfirst).trans
              (IntRange.NR.before_lo_lt
                (List.rel_of_pairwise_cons hcanonical hmem))

/-- Baseline Rust model: non-strict predecessor search, then a successor
search only when the predecessor does not contain `key`. -/
def rangeOrGapAtBaseline (set : RangeSetBlaze) (lower upper key : Int) :
    IntRange × Bool :=
  let split := List.span (fun range => decide (range.val.lo ≤ key)) set.ranges
  match split.fst.getLast? with
  | some predecessor =>
      if key ≤ predecessor.val.hi then (predecessor.val, true)
      else match split.snd.head? with
        | some successor => (⟨predecessor.val.hi + 1, successor.val.lo - 1⟩, false)
        | none => (⟨predecessor.val.hi + 1, upper⟩, false)
  | none =>
      match split.snd.head? with
      | some successor => (⟨lower, successor.val.lo - 1⟩, false)
      | none => (⟨lower, upper⟩, false)

/-- Cursor Rust model: a strict lower-bound gap exposes both adjacent ranges,
including the exact-start successor case. -/
def rangeOrGapAtCursor (set : RangeSetBlaze) (lower upper key : Int) :
    IntRange × Bool :=
  let gap := List.span (fun range => decide (range.val.lo < key)) set.ranges
  match gap.fst.getLast? with
  | some predecessor =>
      if key ≤ predecessor.val.hi then (predecessor.val, true)
      else match gap.snd.head? with
        | some successor =>
            if key = successor.val.lo then (successor.val, true)
            else (⟨predecessor.val.hi + 1, successor.val.lo - 1⟩, false)
        | none => (⟨predecessor.val.hi + 1, upper⟩, false)
  | none =>
      match gap.snd.head? with
      | some successor =>
          if key = successor.val.lo then (successor.val, true)
          else (⟨lower, successor.val.lo - 1⟩, false)
      | none => (⟨lower, upper⟩, false)

/-- The baseline set query returns the unique maximal present range or absent
gap containing the key. -/
theorem rangeOrGapAtBaseline_correct
    (set : RangeSetBlaze) (lower upper key : Int)
    (hdomain : WithinDomain set lower upper)
    (hkeyLower : lower ≤ key) (hkeyUpper : key ≤ upper) :
    QueryResultSpec set lower upper key
      (rangeOrGapAtBaseline set lower upper key) := by
  let split := List.span (fun range : IntRange.NR => decide (range.val.lo ≤ key))
    set.ranges
  have hsplit := nonstrictSplit_spec set.ranges key set.canonical
  change set.ranges = split.fst ++ split.snd ∧
      (∀ range ∈ split.fst, range.val.lo ≤ key) ∧
      (∀ range ∈ split.snd, key < range.val.lo) at hsplit
  rcases hsplit with ⟨hdecomp, hbefore, hafter⟩
  unfold rangeOrGapAtBaseline
  change (match split.fst.getLast? with | _ => _) |> fun result =>
    QueryResultSpec set lower upper key result
  cases hprev : split.fst.getLast? with
  | some predecessor =>
      have hpredMemLeft := List.mem_of_mem_getLast? hprev
      have hpredMem : predecessor ∈ set.ranges := by
        rw [hdecomp]
        exact List.mem_append_left _ hpredMemLeft
      have hpredStart := hbefore predecessor hpredMemLeft
      by_cases hcontained : key ≤ predecessor.val.hi
      · simp only [hcontained]
        exact storedRange_queryResultSpec set lower upper key predecessor
          hdomain hpredMem ⟨hpredStart, hcontained⟩
      · simp only [hcontained]
        have hpredEnd : predecessor.val.hi < key := lt_of_not_ge hcontained
        cases hnext : split.snd.head? with
        | some successor =>
            have hsuccMemRight := List.mem_of_head? hnext
            have hsuccMem : successor ∈ set.ranges := by
              rw [hdecomp]
              exact List.mem_append_right _ hsuccMemRight
            have hsuccStart := hafter successor hsuccMemRight
            apply gap_queryResultSpec set lower upper key _
            all_goals dsimp only
            · have := (hdomain predecessor hpredMem).1
              exact this.trans (predecessor.property.trans (by omega))
            · have := (hdomain successor hsuccMem).2
              have hnonempty := successor.property
              change successor.val.lo ≤ successor.val.hi at hnonempty
              omega
            · constructor <;> omega
            · intro x hxlo hxhi
              rw [toSet_eq_rangesToSet]
              exact range_not_contains_between_neighbors set.canonical hdecomp
                (fun candidate hlast => by rw [hprev] at hlast; cases hlast; omega)
                (fun candidate hhead => by rw [hnext] at hhead; cases hhead; omega)
            · exact Or.inr (by
                have htrue := queryState_true_of_range_contains set hpredMem
                  (show predecessor.val.lo ≤ predecessor.val.hi ∧
                    predecessor.val.hi ≤ predecessor.val.hi from
                    ⟨predecessor.property, le_rfl⟩)
                simpa using htrue)
            · exact Or.inr (by
                have htrue := queryState_true_of_range_contains set hsuccMem
                  (show successor.val.lo ≤ successor.val.lo ∧
                    successor.val.lo ≤ successor.val.hi from
                    ⟨le_rfl, successor.property⟩)
                simpa using htrue)
        | none =>
            have hrightEmpty : split.snd = [] := List.head?_eq_none_iff.mp hnext
            apply gap_queryResultSpec set lower upper key _
            all_goals dsimp only
            · have := (hdomain predecessor hpredMem).1
              exact this.trans (predecessor.property.trans (by omega))
            · exact le_rfl
            · exact ⟨by omega, hkeyUpper⟩
            · intro x hxlo hxhi
              rw [toSet_eq_rangesToSet]
              exact range_not_contains_between_neighbors set.canonical hdecomp
                (fun candidate hlast => by rw [hprev] at hlast; cases hlast; omega)
                (by simp [hrightEmpty])
            · exact Or.inr (by
                have htrue := queryState_true_of_range_contains set hpredMem
                  ⟨predecessor.property, le_rfl⟩
                simpa using htrue)
            · exact Or.inl rfl
  | none =>
      have hleftEmpty : split.fst = [] := List.getLast?_eq_none_iff.mp hprev
      cases hnext : split.snd.head? with
      | some successor =>
          have hsuccMemRight := List.mem_of_head? hnext
          have hsuccMem : successor ∈ set.ranges := by
            rw [hdecomp]
            exact List.mem_append_right _ hsuccMemRight
          have hsuccStart := hafter successor hsuccMemRight
          apply gap_queryResultSpec set lower upper key _
          all_goals dsimp only
          · exact le_rfl
          · have := (hdomain successor hsuccMem).2
            have hnonempty := successor.property
            change successor.val.lo ≤ successor.val.hi at hnonempty
            omega
          · exact ⟨hkeyLower, by omega⟩
          · intro x hxlo hxhi
            rw [toSet_eq_rangesToSet]
            exact range_not_contains_between_neighbors set.canonical hdecomp
              (by simp [hleftEmpty])
              (fun candidate hhead => by rw [hnext] at hhead; cases hhead; omega)
          · exact Or.inl rfl
          · exact Or.inr (by
              have htrue := queryState_true_of_range_contains set hsuccMem
                ⟨le_rfl, successor.property⟩
              simpa using htrue)
      | none =>
          have hrightEmpty : split.snd = [] := List.head?_eq_none_iff.mp hnext
          apply gap_queryResultSpec set lower upper key _
          all_goals dsimp only
          · exact le_rfl
          · exact le_rfl
          · exact ⟨hkeyLower, hkeyUpper⟩
          · intro x hxlo hxhi
            rw [toSet_eq_rangesToSet]
            exact range_not_contains_between_neighbors set.canonical hdecomp
              (by simp [hleftEmpty]) (by simp [hrightEmpty])
          · exact Or.inl rfl
          · exact Or.inl rfl

/-- The cursor set query satisfies the same semantic contract as the baseline
query, including its exact-start `peek_next` branches. -/
theorem rangeOrGapAtCursor_correct
    (set : RangeSetBlaze) (lower upper key : Int)
    (hdomain : WithinDomain set lower upper)
    (hkeyLower : lower ≤ key) (hkeyUpper : key ≤ upper) :
    QueryResultSpec set lower upper key
      (rangeOrGapAtCursor set lower upper key) := by
  let gap := List.span (fun range : IntRange.NR => decide (range.val.lo < key))
    set.ranges
  have hsplit := IntRange.NR.strict_start_split_spec set.ranges key set.canonical
  change set.ranges = gap.fst ++ gap.snd ∧
      (∀ range ∈ gap.fst, range.val.lo < key) ∧
      (∀ range ∈ gap.snd, key ≤ range.val.lo) at hsplit
  rcases hsplit with ⟨hdecomp, hbefore, hafter⟩
  unfold rangeOrGapAtCursor
  change (match gap.fst.getLast? with | _ => _) |> fun result =>
    QueryResultSpec set lower upper key result
  cases hprev : gap.fst.getLast? with
  | some predecessor =>
      have hpredMemLeft := List.mem_of_mem_getLast? hprev
      have hpredMem : predecessor ∈ set.ranges := by
        rw [hdecomp]
        exact List.mem_append_left _ hpredMemLeft
      have hpredStart := hbefore predecessor hpredMemLeft
      by_cases hcontained : key ≤ predecessor.val.hi
      · simp only [hcontained]
        exact storedRange_queryResultSpec set lower upper key predecessor
          hdomain hpredMem ⟨hpredStart.le, hcontained⟩
      · simp only [hcontained]
        have hpredEnd : predecessor.val.hi < key := lt_of_not_ge hcontained
        cases hnext : gap.snd.head? with
        | some successor =>
            have hsuccMemRight := List.mem_of_head? hnext
            have hsuccMem : successor ∈ set.ranges := by
              rw [hdecomp]
              exact List.mem_append_right _ hsuccMemRight
            have hsuccStart := hafter successor hsuccMemRight
            by_cases hexact : key = successor.val.lo
            · simp only [if_pos hexact]
              exact storedRange_queryResultSpec set lower upper key successor
                hdomain hsuccMem ⟨hexact.symm.le, hexact.le.trans successor.property⟩
            · simp only [hexact]
              have hkeyBefore : key < successor.val.lo := lt_of_le_of_ne hsuccStart hexact
              apply gap_queryResultSpec set lower upper key _
              all_goals dsimp only
              · have := (hdomain predecessor hpredMem).1
                exact this.trans (predecessor.property.trans (by omega))
              · have hupper := (hdomain successor hsuccMem).2
                have hnonempty := successor.property
                change successor.val.lo ≤ successor.val.hi at hnonempty
                omega
              · exact ⟨by omega, by omega⟩
              · intro x hxlo hxhi
                rw [toSet_eq_rangesToSet]
                exact range_not_contains_between_neighbors set.canonical hdecomp
                  (fun candidate hlast => by rw [hprev] at hlast; cases hlast; omega)
                  (fun candidate hhead => by rw [hnext] at hhead; cases hhead; omega)
              · exact Or.inr (by
                  have htrue := queryState_true_of_range_contains set hpredMem
                    ⟨predecessor.property, le_rfl⟩
                  simpa using htrue)
              · exact Or.inr (by
                  have htrue := queryState_true_of_range_contains set hsuccMem
                    ⟨le_rfl, successor.property⟩
                  simpa using htrue)
        | none =>
            have hrightEmpty : gap.snd = [] := List.head?_eq_none_iff.mp hnext
            apply gap_queryResultSpec set lower upper key _
            all_goals dsimp only
            · have := (hdomain predecessor hpredMem).1
              exact this.trans (predecessor.property.trans (by omega))
            · exact le_rfl
            · exact ⟨by omega, hkeyUpper⟩
            · intro x hxlo hxhi
              rw [toSet_eq_rangesToSet]
              exact range_not_contains_between_neighbors set.canonical hdecomp
                (fun candidate hlast => by rw [hprev] at hlast; cases hlast; omega)
                (by simp [hrightEmpty])
            · exact Or.inr (by
                have htrue := queryState_true_of_range_contains set hpredMem
                  ⟨predecessor.property, le_rfl⟩
                simpa using htrue)
            · exact Or.inl rfl
  | none =>
      have hleftEmpty : gap.fst = [] := List.getLast?_eq_none_iff.mp hprev
      cases hnext : gap.snd.head? with
      | some successor =>
          have hsuccMemRight := List.mem_of_head? hnext
          have hsuccMem : successor ∈ set.ranges := by
            rw [hdecomp]
            exact List.mem_append_right _ hsuccMemRight
          have hsuccStart := hafter successor hsuccMemRight
          by_cases hexact : key = successor.val.lo
          · simp only [if_pos hexact]
            exact storedRange_queryResultSpec set lower upper key successor
              hdomain hsuccMem ⟨hexact.symm.le, hexact.le.trans successor.property⟩
          · simp only [hexact]
            have hkeyBefore : key < successor.val.lo := lt_of_le_of_ne hsuccStart hexact
            apply gap_queryResultSpec set lower upper key _
            all_goals dsimp only
            · exact le_rfl
            · have hupper := (hdomain successor hsuccMem).2
              have hnonempty := successor.property
              change successor.val.lo ≤ successor.val.hi at hnonempty
              omega
            · exact ⟨hkeyLower, by omega⟩
            · intro x hxlo hxhi
              rw [toSet_eq_rangesToSet]
              exact range_not_contains_between_neighbors set.canonical hdecomp
                (by simp [hleftEmpty])
                (fun candidate hhead => by rw [hnext] at hhead; cases hhead; omega)
            · exact Or.inl rfl
            · exact Or.inr (by
                have htrue := queryState_true_of_range_contains set hsuccMem
                  ⟨le_rfl, successor.property⟩
                simpa using htrue)
      | none =>
          have hrightEmpty : gap.snd = [] := List.head?_eq_none_iff.mp hnext
          apply gap_queryResultSpec set lower upper key _
          all_goals dsimp only
          · exact le_rfl
          · exact le_rfl
          · exact ⟨hkeyLower, hkeyUpper⟩
          · intro x hxlo hxhi
            rw [toSet_eq_rangesToSet]
            exact range_not_contains_between_neighbors set.canonical hdecomp
              (by simp [hleftEmpty]) (by simp [hrightEmpty])
          · exact Or.inl rfl
          · exact Or.inl rfl

/-- Baseline and cursor set queries are equal because the shared semantic
answer is unique. -/
theorem rangeOrGapAtBaseline_eq_cursor
    (set : RangeSetBlaze) (lower upper key : Int)
    (hdomain : WithinDomain set lower upper)
    (hkeyLower : lower ≤ key) (hkeyUpper : key ≤ upper) :
    rangeOrGapAtBaseline set lower upper key =
      rangeOrGapAtCursor set lower upper key := by
  have hbaseline := rangeOrGapAtBaseline_correct set lower upper key
    hdomain hkeyLower hkeyUpper
  have hcursor := rangeOrGapAtCursor_correct set lower upper key
    hdomain hkeyLower hkeyUpper
  exact Prod.ext
    (maximalConstantInterval_unique hbaseline hcursor).1
    (maximalConstantInterval_unique hbaseline hcursor).2

end RangeSetBlaze

namespace RangeMapBlaze

/-- The semantic contract shared by both production-shaped map queries. -/
def QueryResultSpec {Value : Type*} (map : RangeMapBlaze Value)
    (lower upper key : Int) (result : IntRange × Option Value) : Prop :=
  MaximalConstantInterval map.toFunction lower upper key result.1 result.2

/-- All stored map runs lie inside the modeled finite Rust key domain. -/
def WithinDomain {Value : Type*} (map : RangeMapBlaze Value)
    (lower upper : Int) : Prop :=
  ∀ run ∈ map.runs, lower ≤ run.range.val.lo ∧ run.range.val.hi ≤ upper

private theorem runsToFunction_some_exists {Value : Type*}
    {runs : List (Run Value)} {key : Int} {value : Value}
    (h : runsToFunction runs key = some value) :
    ∃ run ∈ runs, run.range.val.lo ≤ key ∧ key ≤ run.range.val.hi ∧
      run.value = value := by
  induction runs with
  | nil => simp at h
  | cons run rest ih =>
      rw [runsToFunction_cons] at h
      by_cases hcontains : run.range.val.lo ≤ key ∧ key ≤ run.range.val.hi
      · simp [hcontains] at h
        exact ⟨run, by simp, hcontains.1, hcontains.2, h⟩
      · simp [hcontains] at h
        obtain ⟨candidate, hmem, hlo, hhi, hvalue⟩ := ih h
        exact ⟨candidate, by simp [hmem], hlo, hhi, hvalue⟩

private theorem runsToFunction_eq_some_of_mem_of_contains {Value : Type*}
    {runs : List (Run Value)} (hcanonical : Canonical runs)
    {run : Run Value} (hmem : run ∈ runs) {key : Int}
    (hcontains : run.range.val.lo ≤ key ∧ key ≤ run.range.val.hi) :
    runsToFunction runs key = some run.value := by
  induction runs with
  | nil => simp at hmem
  | cons first rest ih =>
      rw [runsToFunction_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · simp [hcontains]
      · have hbefore := List.rel_of_pairwise_cons hcanonical hmem
        have hfirstNot : ¬ (first.range.val.lo ≤ key ∧
            key ≤ first.range.val.hi) := by
          intro hfirst
          have := Run.before_hi_lt hbefore
          omega
        simp [hfirstNot, ih hcanonical.tail hmem]

private theorem runsToFunction_eq_none_of_no_contains {Value : Type*}
    {runs : List (Run Value)} {key : Int}
    (habsent : ∀ run ∈ runs,
      ¬ (run.range.val.lo ≤ key ∧ key ≤ run.range.val.hi)) :
    runsToFunction runs key = none := by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
      rw [runsToFunction_cons]
      have hrun := habsent run (by simp)
      simp [hrun, ih (fun candidate hmem => habsent candidate (by simp [hmem]))]

private theorem run_not_contains_between_neighbors {Value : Type*}
    {runs left right : List (Run Value)} {key : Int}
    (hcanonical : Canonical runs) (hdecomp : runs = left ++ right)
    (hleft : ∀ predecessor, left.getLast? = some predecessor →
      predecessor.range.val.hi < key)
    (hright : ∀ successor, right.head? = some successor →
      key < successor.range.val.lo) :
    ∀ run ∈ runs, ¬ (run.range.val.lo ≤ key ∧ key ≤ run.range.val.hi) := by
  intro run hmem hcontains
  rw [hdecomp] at hcanonical hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · by_cases hempty : left = []
    · simp [hempty] at hmem
    · let predecessor := left.getLast hempty
      have hlast : left.getLast? = some predecessor :=
        List.getLast?_eq_some_getLast hempty
      obtain ⟨initial, hdecompLeft⟩ := List.getLast?_eq_some_iff.mp hlast
      have hpredKey := hleft predecessor hlast
      rw [hdecompLeft, List.mem_append] at hmem
      rcases hmem with hinitial | hlastMem
      · have hleftCanonical := (List.pairwise_append.mp hcanonical).1
        rw [hdecompLeft] at hleftCanonical
        have hbefore := (List.pairwise_append.mp hleftCanonical).2.2
          run hinitial predecessor (by simp)
        have hnonempty := predecessor.range.property
        change predecessor.range.val.lo ≤ predecessor.range.val.hi at hnonempty
        have := Run.before_hi_lt hbefore
        omega
      · simp at hlastMem
        subst run
        omega
  · cases right with
    | nil => simp at hmem
    | cons successor tail =>
        have hsuccessorKey := hright successor (by simp)
        have hrightCanonical := (List.pairwise_append.mp hcanonical).2.1
        rcases List.mem_cons.mp hmem with rfl | htail
        · omega
        · have hbefore := List.rel_of_pairwise_cons hrightCanonical htail
          have := Run.before_lo_lt hbefore
          omega

private theorem storedRun_queryResultSpec {Value : Type*}
    (map : RangeMapBlaze Value) (lower upper key : Int) (run : Run Value)
    (hdomain : WithinDomain map lower upper) (hmem : run ∈ map.runs)
    (hcontains : run.range.val.lo ≤ key ∧ key ≤ run.range.val.hi) :
    QueryResultSpec map lower upper key (run.range.val, some run.value) := by
  obtain ⟨initial, remaining, hdecomp⟩ := List.mem_iff_append.mp hmem
  have hcanonical : Canonical (initial ++ run :: remaining) := by
    simpa [hdecomp] using map.canonical
  have hinitial := (List.pairwise_append.mp hcanonical).2.2
  have hremaining : ∀ candidate ∈ remaining, Run.before run candidate := by
    intro candidate hc
    exact List.rel_of_pairwise_cons (List.pairwise_append.mp hcanonical).2.1 hc
  have hleftDifferent : map.toFunction (run.range.val.lo - 1) ≠ some run.value := by
    intro heq
    obtain ⟨candidate, hc, hcLo, hcHi, hcValue⟩ :=
      runsToFunction_some_exists heq
    rw [hdecomp] at hc
    rcases List.mem_append.mp hc with hc | hc
    · have hbefore := hinitial candidate hc run (by simp)
      have hgap := Run.before_range_of_value_eq hbefore hcValue
      unfold IntRange.NR.before at hgap
      omega
    · rcases List.mem_cons.mp hc with rfl | hc
      · omega
      · have hbefore := hremaining candidate hc
        have := Run.before_hi_lt hbefore
        have hnonempty := run.range.property
        change run.range.val.lo ≤ run.range.val.hi at hnonempty
        omega
  have hrightDifferent : map.toFunction (run.range.val.hi + 1) ≠ some run.value := by
    intro heq
    obtain ⟨candidate, hc, hcLo, hcHi, hcValue⟩ :=
      runsToFunction_some_exists heq
    rw [hdecomp] at hc
    rcases List.mem_append.mp hc with hc | hc
    · have hbefore := hinitial candidate hc run (by simp)
      have := Run.before_hi_lt hbefore
      omega
    · rcases List.mem_cons.mp hc with rfl | hc
      · omega
      · have hbefore := hremaining candidate hc
        have hgap := Run.before_range_of_value_eq hbefore hcValue.symm
        unfold IntRange.NR.before at hgap
        omega
  have hrangeDomain := hdomain run hmem
  refine ⟨hrangeDomain.1, hrangeDomain.2, hcontains.1, hcontains.2,
    ?_, ?_, ?_⟩
  · intro x hlo hhi
    exact runsToFunction_eq_some_of_mem_of_contains map.canonical hmem ⟨hlo, hhi⟩
  · by_cases hboundary : run.range.val.lo = lower
    · exact Or.inl hboundary
    · exact Or.inr hleftDifferent
  · by_cases hboundary : run.range.val.hi = upper
    · exact Or.inl hboundary
    · exact Or.inr hrightDifferent

private theorem mapGap_queryResultSpec {Value : Type*}
    (map : RangeMapBlaze Value) (lower upper key : Int) (gap : IntRange)
    (hdomainLower : lower ≤ gap.lo) (hdomainUpper : gap.hi ≤ upper)
    (hcontains : gap.lo ≤ key ∧ key ≤ gap.hi)
    (hempty : ∀ x, gap.lo ≤ x → x ≤ gap.hi → map.toFunction x = none)
    (hleft : gap.lo = lower ∨ map.toFunction (gap.lo - 1) ≠ none)
    (hright : gap.hi = upper ∨ map.toFunction (gap.hi + 1) ≠ none) :
    QueryResultSpec map lower upper key (gap, none) := by
  exact ⟨hdomainLower, hdomainUpper, hcontains.1, hcontains.2,
    hempty, hleft, hright⟩

private theorem mapStrictSplit_spec {Value : Type*}
    (runs : List (Run Value)) (key : Int) (hcanonical : Canonical runs) :
    let split := List.span (fun run => decide (run.range.val.lo < key)) runs
    runs = split.fst ++ split.snd ∧
      (∀ run ∈ split.fst, run.range.val.lo < key) ∧
      (∀ run ∈ split.snd, key ≤ run.range.val.lo) := by
  dsimp
  simp only [List.span_eq_takeWhile_dropWhile]
  refine ⟨(List.takeWhile_append_dropWhile).symm, ?_, ?_⟩
  · intro run hmem
    exact of_decide_eq_true (List.mem_takeWhile_imp
      (p := fun candidate : Run Value => decide (candidate.range.val.lo < key)) hmem)
  · induction runs with
    | nil => simp
    | cons first rest ih =>
        by_cases hfirst : first.range.val.lo < key
        · rw [List.dropWhile_cons_of_pos (by simp [hfirst])]
          exact ih hcanonical.tail
        · rw [List.dropWhile_cons_of_neg (by simp [hfirst])]
          intro run hmem
          rcases List.mem_cons.mp hmem with rfl | hmem
          · exact not_lt.mp hfirst
          · exact (not_lt.mp hfirst).trans
              (Run.before_lo_lt (List.rel_of_pairwise_cons hcanonical hmem)).le

private theorem mapNonstrictSplit_spec {Value : Type*}
    (runs : List (Run Value)) (key : Int) (hcanonical : Canonical runs) :
    let split := List.span (fun run => decide (run.range.val.lo ≤ key)) runs
    runs = split.fst ++ split.snd ∧
      (∀ run ∈ split.fst, run.range.val.lo ≤ key) ∧
      (∀ run ∈ split.snd, key < run.range.val.lo) := by
  dsimp
  simp only [List.span_eq_takeWhile_dropWhile]
  refine ⟨(List.takeWhile_append_dropWhile).symm, ?_, ?_⟩
  · intro run hmem
    exact of_decide_eq_true (List.mem_takeWhile_imp
      (p := fun candidate : Run Value => decide (candidate.range.val.lo ≤ key)) hmem)
  · induction runs with
    | nil => simp
    | cons first rest ih =>
        by_cases hfirst : first.range.val.lo ≤ key
        · rw [List.dropWhile_cons_of_pos (by simp [hfirst])]
          exact ih hcanonical.tail
        · rw [List.dropWhile_cons_of_neg (by simp [hfirst])]
          intro run hmem
          rcases List.mem_cons.mp hmem with rfl | hmem
          · exact lt_of_not_ge hfirst
          · exact (lt_of_not_ge hfirst).trans
              (Run.before_lo_lt (List.rel_of_pairwise_cons hcanonical hmem))

/-- Baseline Rust map-query model. -/
def rangeOrGapAtBaseline {Value : Type*} (map : RangeMapBlaze Value)
    (lower upper key : Int) : IntRange × Option Value :=
  let split := List.span (fun run => decide (run.range.val.lo ≤ key)) map.runs
  match split.fst.getLast? with
  | some predecessor =>
      if key ≤ predecessor.range.val.hi then
        (predecessor.range.val, some predecessor.value)
      else match split.snd.head? with
        | some successor =>
            (⟨predecessor.range.val.hi + 1, successor.range.val.lo - 1⟩, none)
        | none => (⟨predecessor.range.val.hi + 1, upper⟩, none)
  | none =>
      match split.snd.head? with
      | some successor => (⟨lower, successor.range.val.lo - 1⟩, none)
      | none => (⟨lower, upper⟩, none)

/-- Cursor Rust map-query model. -/
def rangeOrGapAtCursor {Value : Type*} (map : RangeMapBlaze Value)
    (lower upper key : Int) : IntRange × Option Value :=
  let gap := List.span (fun run => decide (run.range.val.lo < key)) map.runs
  match gap.fst.getLast? with
  | some predecessor =>
      if key ≤ predecessor.range.val.hi then
        (predecessor.range.val, some predecessor.value)
      else match gap.snd.head? with
        | some successor =>
            if key = successor.range.val.lo then
              (successor.range.val, some successor.value)
            else
              (⟨predecessor.range.val.hi + 1, successor.range.val.lo - 1⟩, none)
        | none => (⟨predecessor.range.val.hi + 1, upper⟩, none)
  | none =>
      match gap.snd.head? with
      | some successor =>
          if key = successor.range.val.lo then
            (successor.range.val, some successor.value)
          else (⟨lower, successor.range.val.lo - 1⟩, none)
      | none => (⟨lower, upper⟩, none)

/-- Correctness of the regular/baseline map query. No decidable equality on
values is needed: the query only returns stored values. -/
theorem rangeOrGapAtBaseline_correct {Value : Type*}
    (map : RangeMapBlaze Value) (lower upper key : Int)
    (hdomain : WithinDomain map lower upper)
    (hkeyLower : lower ≤ key) (hkeyUpper : key ≤ upper) :
    QueryResultSpec map lower upper key
      (rangeOrGapAtBaseline map lower upper key) := by
  let split := List.span (fun run : Run Value => decide (run.range.val.lo ≤ key))
    map.runs
  have hsplit := mapNonstrictSplit_spec map.runs key map.canonical
  change map.runs = split.fst ++ split.snd ∧
      (∀ run ∈ split.fst, run.range.val.lo ≤ key) ∧
      (∀ run ∈ split.snd, key < run.range.val.lo) at hsplit
  rcases hsplit with ⟨hdecomp, hbefore, hafter⟩
  unfold rangeOrGapAtBaseline
  change (match split.fst.getLast? with | _ => _) |> fun result =>
    QueryResultSpec map lower upper key result
  cases hprev : split.fst.getLast? with
  | some predecessor =>
      have hpredMemLeft := List.mem_of_mem_getLast? hprev
      have hpredMem : predecessor ∈ map.runs := by
        rw [hdecomp]
        exact List.mem_append_left _ hpredMemLeft
      have hpredStart := hbefore predecessor hpredMemLeft
      by_cases hcontained : key ≤ predecessor.range.val.hi
      · simp only [hcontained]
        exact storedRun_queryResultSpec map lower upper key predecessor
          hdomain hpredMem ⟨hpredStart, hcontained⟩
      · simp only [hcontained]
        have hpredEnd : predecessor.range.val.hi < key := lt_of_not_ge hcontained
        cases hnext : split.snd.head? with
        | some successor =>
            have hsuccMemRight := List.mem_of_head? hnext
            have hsuccMem : successor ∈ map.runs := by
              rw [hdecomp]
              exact List.mem_append_right _ hsuccMemRight
            have hsuccStart := hafter successor hsuccMemRight
            apply mapGap_queryResultSpec map lower upper key _
            all_goals dsimp only
            · have hlower := (hdomain predecessor hpredMem).1
              exact hlower.trans (predecessor.range.property.trans (by omega))
            · have hupper := (hdomain successor hsuccMem).2
              have hnonempty := successor.range.property
              change successor.range.val.lo ≤ successor.range.val.hi at hnonempty
              omega
            · exact ⟨by omega, by omega⟩
            · intro x hxlo hxhi
              apply runsToFunction_eq_none_of_no_contains
              exact run_not_contains_between_neighbors map.canonical hdecomp
                (fun candidate hlast => by rw [hprev] at hlast; cases hlast; omega)
                (fun candidate hhead => by rw [hnext] at hhead; cases hhead; omega)
            · exact Or.inr (by
                have hsome := runsToFunction_eq_some_of_mem_of_contains
                  map.canonical hpredMem
                  (show predecessor.range.val.lo ≤ predecessor.range.val.hi ∧
                    predecessor.range.val.hi ≤ predecessor.range.val.hi from
                    ⟨predecessor.range.property, le_rfl⟩)
                intro hnone
                have hsome' : map.toFunction
                    (predecessor.range.val.hi + 1 - 1) = some predecessor.value := by
                  simpa [toFunction] using hsome
                rw [hnone] at hsome'
                simp at hsome')
            · exact Or.inr (by
                have hsome := runsToFunction_eq_some_of_mem_of_contains
                  map.canonical hsuccMem
                  (show successor.range.val.lo ≤ successor.range.val.lo ∧
                    successor.range.val.lo ≤ successor.range.val.hi from
                    ⟨le_rfl, successor.range.property⟩)
                intro hnone
                have hsome' : map.toFunction
                    (successor.range.val.lo - 1 + 1) = some successor.value := by
                  simpa [toFunction] using hsome
                rw [hnone] at hsome'
                simp at hsome')
        | none =>
            have hrightEmpty : split.snd = [] := List.head?_eq_none_iff.mp hnext
            apply mapGap_queryResultSpec map lower upper key _
            all_goals dsimp only
            · have hlower := (hdomain predecessor hpredMem).1
              exact hlower.trans (predecessor.range.property.trans (by omega))
            · exact le_rfl
            · exact ⟨by omega, hkeyUpper⟩
            · intro x hxlo hxhi
              apply runsToFunction_eq_none_of_no_contains
              exact run_not_contains_between_neighbors map.canonical hdecomp
                (fun candidate hlast => by rw [hprev] at hlast; cases hlast; omega)
                (by simp [hrightEmpty])
            · exact Or.inr (by
                have hsome := runsToFunction_eq_some_of_mem_of_contains
                  map.canonical hpredMem ⟨predecessor.range.property, le_rfl⟩
                intro hnone
                have hsome' : map.toFunction
                    (predecessor.range.val.hi + 1 - 1) = some predecessor.value := by
                  simpa [toFunction] using hsome
                rw [hnone] at hsome'
                simp at hsome')
            · exact Or.inl rfl
  | none =>
      have hleftEmpty : split.fst = [] := List.getLast?_eq_none_iff.mp hprev
      cases hnext : split.snd.head? with
      | some successor =>
          have hsuccMemRight := List.mem_of_head? hnext
          have hsuccMem : successor ∈ map.runs := by
            rw [hdecomp]
            exact List.mem_append_right _ hsuccMemRight
          have hsuccStart := hafter successor hsuccMemRight
          apply mapGap_queryResultSpec map lower upper key _
          all_goals dsimp only
          · exact le_rfl
          · have hupper := (hdomain successor hsuccMem).2
            have hnonempty := successor.range.property
            change successor.range.val.lo ≤ successor.range.val.hi at hnonempty
            omega
          · exact ⟨hkeyLower, by omega⟩
          · intro x hxlo hxhi
            apply runsToFunction_eq_none_of_no_contains
            exact run_not_contains_between_neighbors map.canonical hdecomp
              (by simp [hleftEmpty])
              (fun candidate hhead => by rw [hnext] at hhead; cases hhead; omega)
          · exact Or.inl rfl
          · exact Or.inr (by
              have hsome := runsToFunction_eq_some_of_mem_of_contains
                map.canonical hsuccMem ⟨le_rfl, successor.range.property⟩
              intro hnone
              have hsome' : map.toFunction
                  (successor.range.val.lo - 1 + 1) = some successor.value := by
                simpa [toFunction] using hsome
              rw [hnone] at hsome'
              simp at hsome')
      | none =>
          have hrightEmpty : split.snd = [] := List.head?_eq_none_iff.mp hnext
          apply mapGap_queryResultSpec map lower upper key _
          all_goals dsimp only
          · exact le_rfl
          · exact le_rfl
          · exact ⟨hkeyLower, hkeyUpper⟩
          · intro x hxlo hxhi
            apply runsToFunction_eq_none_of_no_contains
            exact run_not_contains_between_neighbors map.canonical hdecomp
              (by simp [hleftEmpty]) (by simp [hrightEmpty])
          · exact Or.inl rfl
          · exact Or.inl rfl

/-- Correctness of the cursor map query, including exact-start lookup through
`peek_next`. -/
theorem rangeOrGapAtCursor_correct {Value : Type*}
    (map : RangeMapBlaze Value) (lower upper key : Int)
    (hdomain : WithinDomain map lower upper)
    (hkeyLower : lower ≤ key) (hkeyUpper : key ≤ upper) :
    QueryResultSpec map lower upper key
      (rangeOrGapAtCursor map lower upper key) := by
  let gap := List.span (fun run : Run Value => decide (run.range.val.lo < key))
    map.runs
  have hsplit := mapStrictSplit_spec map.runs key map.canonical
  change map.runs = gap.fst ++ gap.snd ∧
      (∀ run ∈ gap.fst, run.range.val.lo < key) ∧
      (∀ run ∈ gap.snd, key ≤ run.range.val.lo) at hsplit
  rcases hsplit with ⟨hdecomp, hbefore, hafter⟩
  unfold rangeOrGapAtCursor
  change (match gap.fst.getLast? with | _ => _) |> fun result =>
    QueryResultSpec map lower upper key result
  cases hprev : gap.fst.getLast? with
  | some predecessor =>
      have hpredMemLeft := List.mem_of_mem_getLast? hprev
      have hpredMem : predecessor ∈ map.runs := by
        rw [hdecomp]
        exact List.mem_append_left _ hpredMemLeft
      have hpredStart := hbefore predecessor hpredMemLeft
      by_cases hcontained : key ≤ predecessor.range.val.hi
      · simp only [hcontained]
        exact storedRun_queryResultSpec map lower upper key predecessor
          hdomain hpredMem ⟨hpredStart.le, hcontained⟩
      · simp only [hcontained]
        have hpredEnd : predecessor.range.val.hi < key := lt_of_not_ge hcontained
        cases hnext : gap.snd.head? with
        | some successor =>
            have hsuccMemRight := List.mem_of_head? hnext
            have hsuccMem : successor ∈ map.runs := by
              rw [hdecomp]
              exact List.mem_append_right _ hsuccMemRight
            have hsuccStart := hafter successor hsuccMemRight
            by_cases hexact : key = successor.range.val.lo
            · simp only [if_pos hexact]
              exact storedRun_queryResultSpec map lower upper key successor
                hdomain hsuccMem
                  ⟨hexact.symm.le, hexact.le.trans successor.range.property⟩
            · simp only [hexact]
              have hkeyBefore : key < successor.range.val.lo :=
                lt_of_le_of_ne hsuccStart hexact
              apply mapGap_queryResultSpec map lower upper key _
              all_goals dsimp only
              · have hlower := (hdomain predecessor hpredMem).1
                exact hlower.trans (predecessor.range.property.trans (by omega))
              · have hupper := (hdomain successor hsuccMem).2
                have hnonempty := successor.range.property
                change successor.range.val.lo ≤ successor.range.val.hi at hnonempty
                omega
              · exact ⟨by omega, by omega⟩
              · intro x hxlo hxhi
                apply runsToFunction_eq_none_of_no_contains
                exact run_not_contains_between_neighbors map.canonical hdecomp
                  (fun candidate hlast => by rw [hprev] at hlast; cases hlast; omega)
                  (fun candidate hhead => by rw [hnext] at hhead; cases hhead; omega)
              · exact Or.inr (by
                  have hsome := runsToFunction_eq_some_of_mem_of_contains
                    map.canonical hpredMem ⟨predecessor.range.property, le_rfl⟩
                  intro hnone
                  have hsome' : map.toFunction
                      (predecessor.range.val.hi + 1 - 1) = some predecessor.value := by
                    simpa [toFunction] using hsome
                  rw [hnone] at hsome'
                  simp at hsome')
              · exact Or.inr (by
                  have hsome := runsToFunction_eq_some_of_mem_of_contains
                    map.canonical hsuccMem ⟨le_rfl, successor.range.property⟩
                  intro hnone
                  have hsome' : map.toFunction
                      (successor.range.val.lo - 1 + 1) = some successor.value := by
                    simpa [toFunction] using hsome
                  rw [hnone] at hsome'
                  simp at hsome')
        | none =>
            have hrightEmpty : gap.snd = [] := List.head?_eq_none_iff.mp hnext
            apply mapGap_queryResultSpec map lower upper key _
            all_goals dsimp only
            · have hlower := (hdomain predecessor hpredMem).1
              exact hlower.trans (predecessor.range.property.trans (by omega))
            · exact le_rfl
            · exact ⟨by omega, hkeyUpper⟩
            · intro x hxlo hxhi
              apply runsToFunction_eq_none_of_no_contains
              exact run_not_contains_between_neighbors map.canonical hdecomp
                (fun candidate hlast => by rw [hprev] at hlast; cases hlast; omega)
                (by simp [hrightEmpty])
            · exact Or.inr (by
                have hsome := runsToFunction_eq_some_of_mem_of_contains
                  map.canonical hpredMem ⟨predecessor.range.property, le_rfl⟩
                intro hnone
                have hsome' : map.toFunction
                    (predecessor.range.val.hi + 1 - 1) = some predecessor.value := by
                  simpa [toFunction] using hsome
                rw [hnone] at hsome'
                simp at hsome')
            · exact Or.inl rfl
  | none =>
      have hleftEmpty : gap.fst = [] := List.getLast?_eq_none_iff.mp hprev
      cases hnext : gap.snd.head? with
      | some successor =>
          have hsuccMemRight := List.mem_of_head? hnext
          have hsuccMem : successor ∈ map.runs := by
            rw [hdecomp]
            exact List.mem_append_right _ hsuccMemRight
          have hsuccStart := hafter successor hsuccMemRight
          by_cases hexact : key = successor.range.val.lo
          · simp only [if_pos hexact]
            exact storedRun_queryResultSpec map lower upper key successor
              hdomain hsuccMem
                ⟨hexact.symm.le, hexact.le.trans successor.range.property⟩
          · simp only [hexact]
            have hkeyBefore : key < successor.range.val.lo :=
              lt_of_le_of_ne hsuccStart hexact
            apply mapGap_queryResultSpec map lower upper key _
            all_goals dsimp only
            · exact le_rfl
            · have hupper := (hdomain successor hsuccMem).2
              have hnonempty := successor.range.property
              change successor.range.val.lo ≤ successor.range.val.hi at hnonempty
              omega
            · exact ⟨hkeyLower, by omega⟩
            · intro x hxlo hxhi
              apply runsToFunction_eq_none_of_no_contains
              exact run_not_contains_between_neighbors map.canonical hdecomp
                (by simp [hleftEmpty])
                (fun candidate hhead => by rw [hnext] at hhead; cases hhead; omega)
            · exact Or.inl rfl
            · exact Or.inr (by
                have hsome := runsToFunction_eq_some_of_mem_of_contains
                  map.canonical hsuccMem ⟨le_rfl, successor.range.property⟩
                intro hnone
                have hsome' : map.toFunction
                    (successor.range.val.lo - 1 + 1) = some successor.value := by
                  simpa [toFunction] using hsome
                rw [hnone] at hsome'
                simp at hsome')
      | none =>
          have hrightEmpty : gap.snd = [] := List.head?_eq_none_iff.mp hnext
          apply mapGap_queryResultSpec map lower upper key _
          all_goals dsimp only
          · exact le_rfl
          · exact le_rfl
          · exact ⟨hkeyLower, hkeyUpper⟩
          · intro x hxlo hxhi
            apply runsToFunction_eq_none_of_no_contains
            exact run_not_contains_between_neighbors map.canonical hdecomp
              (by simp [hleftEmpty]) (by simp [hrightEmpty])
          · exact Or.inl rfl
          · exact Or.inl rfl

/-- Baseline and cursor map queries are equal because their semantic result is
unique. -/
theorem rangeOrGapAtBaseline_eq_cursor {Value : Type*}
    (map : RangeMapBlaze Value) (lower upper key : Int)
    (hdomain : WithinDomain map lower upper)
    (hkeyLower : lower ≤ key) (hkeyUpper : key ≤ upper) :
    rangeOrGapAtBaseline map lower upper key =
      rangeOrGapAtCursor map lower upper key := by
  have hbaseline := rangeOrGapAtBaseline_correct map lower upper key
    hdomain hkeyLower hkeyUpper
  have hcursor := rangeOrGapAtCursor_correct map lower upper key
    hdomain hkeyLower hkeyUpper
  exact Prod.ext
    (maximalConstantInterval_unique hbaseline hcursor).1
    (maximalConstantInterval_unique hbaseline hcursor).2

end RangeMapBlaze
