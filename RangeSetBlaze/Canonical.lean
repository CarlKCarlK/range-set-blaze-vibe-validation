import RangeSetBlaze.Basic

open IntRange (NR)

namespace RangeSetBlaze

private lemma rangesToSet_lower_bound
    {ranges : List NR} {lower key : Int}
    (hlower : ∀ range ∈ ranges, lower ≤ range.val.lo)
    (hkey : key ∈ rangesToSet ranges) : lower ≤ key := by
  induction ranges with
  | nil => simp at hkey
  | cons range rest ih =>
      rw [rangesToSet_cons] at hkey
      rcases hkey with hkey | hkey
      · exact (hlower range (by simp)).trans
          ((IntRange.mem_toSet_iff range.val key).mp hkey).1
      · exact ih (fun candidate hmem => hlower candidate (by simp [hmem])) hkey

private lemma rangesToSet_strict_lower_bound
    {ranges : List NR} {lower key : Int}
    (hlower : ∀ range ∈ ranges, lower < range.val.lo)
    (hkey : key ∈ rangesToSet ranges) : lower < key := by
  induction ranges with
  | nil => simp at hkey
  | cons range rest ih =>
      rw [rangesToSet_cons] at hkey
      rcases hkey with hkey | hkey
      · exact (hlower range (by simp)).trans_le
          ((IntRange.mem_toSet_iff range.val key).mp hkey).1
      · exact ih (fun candidate hmem => hlower candidate (by simp [hmem])) hkey

private lemma canonical_tail_above_head
    {head : NR} {tail : List NR}
    (hcanonical : List.Pairwise IntRange.NR.before (head :: tail)) :
    ∀ range ∈ tail, head.val.hi + 1 < range.val.lo := by
  intro range hmem
  exact List.rel_of_pairwise_cons hcanonical hmem

private lemma canonical_head_lower_bound
    {head : NR} {tail : List NR}
    (hcanonical : List.Pairwise IntRange.NR.before (head :: tail)) :
    ∀ range ∈ head :: tail, head.val.lo ≤ range.val.lo := by
  intro range hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact le_rfl
  · exact (IntRange.NR.before_lo_lt
      (List.rel_of_pairwise_cons hcanonical hmem)).le

/-- Canonical range lists are uniquely determined by the integer set they
represent. -/
theorem ranges_eq_of_canonical_of_rangesToSet_eq
    {xs ys : List NR}
    (hxs : List.Pairwise IntRange.NR.before xs)
    (hys : List.Pairwise IntRange.NR.before ys)
    (hset : rangesToSet xs = rangesToSet ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons b bs =>
          have hb : b.val.lo ∈ rangesToSet (b :: bs) := by
            rw [rangesToSet_cons]
            exact Or.inl ((IntRange.mem_toSet_iff _ _).mpr ⟨le_rfl, b.property⟩)
          rw [← hset] at hb
          simp at hb
  | cons a as ih =>
      cases ys with
      | nil =>
          have ha : a.val.lo ∈ rangesToSet (a :: as) := by
            rw [rangesToSet_cons]
            exact Or.inl ((IntRange.mem_toSet_iff _ _).mpr ⟨le_rfl, a.property⟩)
          rw [hset] at ha
          simp at ha
      | cons b bs =>
          have ha_mem : a.val.lo ∈ rangesToSet (a :: as) := by
            rw [rangesToSet_cons]
            exact Or.inl ((IntRange.mem_toSet_iff _ _).mpr ⟨le_rfl, a.property⟩)
          have hb_mem : b.val.lo ∈ rangesToSet (b :: bs) := by
            rw [rangesToSet_cons]
            exact Or.inl ((IntRange.mem_toSet_iff _ _).mpr ⟨le_rfl, b.property⟩)
          have ha_mem' : a.val.lo ∈ rangesToSet (b :: bs) := by
            rw [← hset]
            exact ha_mem
          have hb_mem' : b.val.lo ∈ rangesToSet (a :: as) := by
            rw [hset]
            exact hb_mem
          have hblo : b.val.lo ≤ a.val.lo :=
            rangesToSet_lower_bound (canonical_head_lower_bound hys) ha_mem'
          have halo : a.val.lo ≤ b.val.lo :=
            rangesToSet_lower_bound (canonical_head_lower_bound hxs) hb_mem'
          have hlo : a.val.lo = b.val.lo := le_antisymm halo hblo
          have hanonempty : a.val.lo ≤ a.val.hi := a.property
          have hbnonempty : b.val.lo ≤ b.val.hi := b.property
          have hahi : a.val.hi = b.val.hi := by
            apply le_antisymm
            · by_contra hnot
              have hlt : b.val.hi < a.val.hi := lt_of_not_ge hnot
              let key := b.val.hi + 1
              have hkey : key ∈ rangesToSet (a :: as) := by
                rw [rangesToSet_cons]
                apply Or.inl
                rw [IntRange.mem_toSet_iff]
                dsimp only [key]
                constructor <;> omega
              rw [hset] at hkey
              rw [rangesToSet_cons] at hkey
              rcases hkey with hhead | htail
              · rw [IntRange.mem_toSet_iff] at hhead
                dsimp only [key] at hhead
                omega
              · have habove := rangesToSet_strict_lower_bound
                    (canonical_tail_above_head hys) htail
                dsimp only [key] at habove
                omega
            · by_contra hnot
              have hlt : a.val.hi < b.val.hi := lt_of_not_ge hnot
              let key := a.val.hi + 1
              have hkey : key ∈ rangesToSet (b :: bs) := by
                rw [rangesToSet_cons]
                apply Or.inl
                rw [IntRange.mem_toSet_iff]
                dsimp only [key]
                constructor <;> omega
              rw [← hset] at hkey
              rw [rangesToSet_cons] at hkey
              rcases hkey with hhead | htail
              · rw [IntRange.mem_toSet_iff] at hhead
                dsimp only [key] at hhead
                omega
              · have habove := rangesToSet_strict_lower_bound
                    (canonical_tail_above_head hxs) htail
                dsimp only [key] at habove
                omega
          have hab : a = b := by
            apply Subtype.ext
            cases ha : a.val with
            | mk alo ahi =>
                cases hb : b.val with
                | mk blo bhi =>
                    rw [ha, hb] at hlo hahi
                    change alo = blo at hlo
                    change ahi = bhi at hahi
                    subst blo
                    subst bhi
                    rfl
          subst b
          congr 1
          apply ih hxs.tail hys.tail
          ext key
          constructor <;> intro htail
          · have habove := rangesToSet_strict_lower_bound
                (canonical_tail_above_head hxs) htail
            have horiginal : key ∈ rangesToSet (a :: as) := by
              rw [rangesToSet_cons]
              exact Or.inr htail
            rw [hset, rangesToSet_cons] at horiginal
            rcases horiginal with hhead | htail' <;> try exact htail'
            rw [IntRange.mem_toSet_iff] at hhead
            omega
          · have habove := rangesToSet_strict_lower_bound
                (canonical_tail_above_head hys) htail
            have horiginal : key ∈ rangesToSet (a :: bs) := by
              rw [rangesToSet_cons]
              exact Or.inr htail
            rw [← hset, rangesToSet_cons] at horiginal
            rcases horiginal with hhead | htail' <;> try exact htail'
            rw [IntRange.mem_toSet_iff] at hhead
            omega

/-- Two packaged range sets are equal when they represent the same set of
integers. Canonicality is supplied by the package. -/
@[ext] theorem ext {left right : RangeSetBlaze}
    (hset : left.toSet = right.toSet) : left = right := by
  cases left with
  | mk leftRanges leftCanonical =>
      cases right with
      | mk rightRanges rightCanonical =>
          simp only [toSet] at hset
          have hranges := ranges_eq_of_canonical_of_rangesToSet_eq
            leftCanonical rightCanonical hset
          subst rightRanges
          rfl

end RangeSetBlaze

namespace RangeMapBlaze

private lemma runsToFunction_lower_bound
    {Value : Type*} {runs : List (Run Value)} {lower key : Int} {value : Value}
    (hlower : ∀ run ∈ runs, lower ≤ run.range.val.lo)
    (hkey : runsToFunction runs key = some value) : lower ≤ key := by
  induction runs with
  | nil => simp at hkey
  | cons run rest ih =>
      rw [runsToFunction_cons] at hkey
      split at hkey <;> rename_i hcontains
      · exact (hlower run (by simp)).trans hcontains.1
      · exact ih (fun candidate hmem => hlower candidate (by simp [hmem])) hkey

private lemma canonical_run_head_lower_bound
    {Value : Type*} {head : Run Value} {tail : List (Run Value)}
    (hcanonical : Canonical (head :: tail)) :
    ∀ run ∈ head :: tail, head.range.val.lo ≤ run.range.val.lo := by
  intro run hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact le_rfl
  · exact (Run.before_lo_lt (List.rel_of_pairwise_cons hcanonical hmem)).le

/-- A canonical tail cannot continue the head's value at the integer directly
after the head. Equal-valued canonical runs must leave a genuine gap. -/
private lemma canonical_tail_does_not_continue_head_value
    {Value : Type*} {head : Run Value} {tail : List (Run Value)}
    (hbefore : ∀ run ∈ tail, Run.before head run) :
    runsToFunction tail (head.range.val.hi + 1) ≠ some head.value := by
  induction tail with
  | nil => simp
  | cons run rest ih =>
      rw [runsToFunction_cons]
      by_cases hcontains :
          run.range.val.lo ≤ head.range.val.hi + 1 ∧
            head.range.val.hi + 1 ≤ run.range.val.hi
      · simp only [if_pos hcontains]
        intro hvalue
        have hvalue' : run.value = head.value := Option.some.inj hvalue
        have hgap := Run.before_range_of_value_eq
          (hbefore run (by simp)) hvalue'.symm
        unfold IntRange.NR.before at hgap
        omega
      · rw [if_neg hcontains]
        exact ih (fun candidate hmem => hbefore candidate (by simp [hmem]))

/-- Canonical run lists are uniquely determined by their represented partial
function. The equal-value gap condition in `Run.before` supplies maximality. -/
theorem runs_eq_of_canonical_of_runsToFunction_eq
    {Value : Type*} {xs ys : List (Run Value)}
    (hxs : Canonical xs) (hys : Canonical ys)
    (hfunction : runsToFunction xs = runsToFunction ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons b bs =>
          have hpoint := congrFun hfunction b.range.val.lo
          have hcontains :
              b.range.val.lo ≤ b.range.val.lo ∧
                b.range.val.lo ≤ b.range.val.hi := ⟨le_rfl, b.range.property⟩
          simp [runsToFunction_cons, hcontains] at hpoint
  | cons a as ih =>
      cases ys with
      | nil =>
          have hpoint := congrFun hfunction a.range.val.lo
          have hcontains :
              a.range.val.lo ≤ a.range.val.lo ∧
                a.range.val.lo ≤ a.range.val.hi := ⟨le_rfl, a.range.property⟩
          simp [runsToFunction_cons, hcontains] at hpoint
      | cons b bs =>
          have ha_contains :
              a.range.val.lo ≤ a.range.val.lo ∧
                a.range.val.lo ≤ a.range.val.hi := ⟨le_rfl, a.range.property⟩
          have hb_contains :
              b.range.val.lo ≤ b.range.val.lo ∧
                b.range.val.lo ≤ b.range.val.hi := ⟨le_rfl, b.range.property⟩
          have ha_value : runsToFunction (a :: as) a.range.val.lo = some a.value := by
            simp [runsToFunction_cons, ha_contains]
          have hb_value : runsToFunction (b :: bs) b.range.val.lo = some b.value := by
            simp [runsToFunction_cons, hb_contains]
          have ha_value' : runsToFunction (b :: bs) a.range.val.lo = some a.value := by
            rw [← hfunction]
            exact ha_value
          have hb_value' : runsToFunction (a :: as) b.range.val.lo = some b.value := by
            rw [hfunction]
            exact hb_value
          have hblo : b.range.val.lo ≤ a.range.val.lo :=
            runsToFunction_lower_bound
              (canonical_run_head_lower_bound hys) ha_value'
          have halo : a.range.val.lo ≤ b.range.val.lo :=
            runsToFunction_lower_bound
              (canonical_run_head_lower_bound hxs) hb_value'
          have hlo : a.range.val.lo = b.range.val.lo := le_antisymm halo hblo
          have hvalue : a.value = b.value := by
            have hpoint := congrFun hfunction a.range.val.lo
            have hb_at_a :
                b.range.val.lo ≤ a.range.val.lo ∧
                  a.range.val.lo ≤ b.range.val.hi := by
              constructor
              · omega
              · exact hlo ▸ b.range.property
            simp [runsToFunction_cons, ha_contains, hb_at_a] at hpoint
            exact hpoint
          have hanonempty : a.range.val.lo ≤ a.range.val.hi := a.range.property
          have hbnonempty : b.range.val.lo ≤ b.range.val.hi := b.range.property
          have hahi : a.range.val.hi = b.range.val.hi := by
            apply le_antisymm
            · by_contra hnot
              have hlt : b.range.val.hi < a.range.val.hi := lt_of_not_ge hnot
              let key := b.range.val.hi + 1
              have ha_key :
                  a.range.val.lo ≤ key ∧ key ≤ a.range.val.hi := by
                dsimp only [key]
                constructor <;> omega
              have hpoint := congrFun hfunction key
              rw [runsToFunction_cons] at hpoint
              rw [if_pos ha_key] at hpoint
              rw [runsToFunction_cons] at hpoint
              have hb_not_key : ¬ (b.range.val.lo ≤ key ∧ key ≤ b.range.val.hi) := by
                dsimp only [key]
                omega
              rw [if_neg hb_not_key] at hpoint
              apply canonical_tail_does_not_continue_head_value
                (fun run hmem => List.rel_of_pairwise_cons hys hmem)
              simpa only [key, hvalue] using hpoint.symm
            · by_contra hnot
              have hlt : a.range.val.hi < b.range.val.hi := lt_of_not_ge hnot
              let key := a.range.val.hi + 1
              have hb_key :
                  b.range.val.lo ≤ key ∧ key ≤ b.range.val.hi := by
                dsimp only [key]
                constructor <;> omega
              have hpoint := congrFun hfunction key
              rw [runsToFunction_cons] at hpoint
              have ha_not_key : ¬ (a.range.val.lo ≤ key ∧ key ≤ a.range.val.hi) := by
                dsimp only [key]
                omega
              rw [if_neg ha_not_key] at hpoint
              rw [runsToFunction_cons] at hpoint
              rw [if_pos hb_key] at hpoint
              apply canonical_tail_does_not_continue_head_value
                (fun run hmem => List.rel_of_pairwise_cons hxs hmem)
              simpa only [key, hvalue] using hpoint
          have hrange : a.range = b.range := by
            apply Subtype.ext
            cases ha : a.range.val with
            | mk alo ahi =>
                cases hb : b.range.val with
                | mk blo bhi =>
                    rw [ha, hb] at hlo hahi
                    change alo = blo at hlo
                    change ahi = bhi at hahi
                    subst blo
                    subst bhi
                    rfl
          have hab : a = b := by
            cases a with
            | mk arange avalue =>
                cases b with
                | mk brange bvalue =>
                    simp only at hrange hvalue
                    subst brange
                    subst bvalue
                    rfl
          subst b
          congr 1
          apply ih hxs.tail hys.tail
          funext key
          change runsToFunction as key = runsToFunction bs key
          have hpoint := congrFun hfunction key
          rw [runsToFunction_cons] at hpoint
          rw [runsToFunction_cons] at hpoint
          by_cases hcontains :
              a.range.val.lo ≤ key ∧ key ≤ a.range.val.hi
          · have has_none : runsToFunction as key = none := by
              cases heq : runsToFunction as key with
              | none => rfl
              | some value =>
                  have hlower := runsToFunction_lower_bound
                    (fun run hmem => by
                      have hbefore := List.rel_of_pairwise_cons hxs hmem
                      exact hbefore.1) heq
                  omega
            have hbs_none : runsToFunction bs key = none := by
              cases heq : runsToFunction bs key with
              | none => rfl
              | some value =>
                  have hlower := runsToFunction_lower_bound
                    (fun run hmem => by
                      have hbefore := List.rel_of_pairwise_cons hys hmem
                      exact hbefore.1) heq
                  omega
            rw [has_none, hbs_none]
          · simpa [hcontains] using hpoint

/-- Two packaged range maps are equal when they represent the same partial
function. Canonicality is supplied by the package. -/
@[ext] theorem ext {Value : Type*}
    {left right : RangeMapBlaze Value}
    (hfunction : left.toFunction = right.toFunction) : left = right := by
  cases left with
  | mk leftRuns leftCanonical =>
      cases right with
      | mk rightRuns rightCanonical =>
          simp only [toFunction] at hfunction
          have hruns := runs_eq_of_canonical_of_runsToFunction_eq
            leftCanonical rightCanonical hfunction
          subst rightRuns
          rfl

end RangeMapBlaze
