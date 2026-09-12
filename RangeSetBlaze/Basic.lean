import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith

/-- An inclusive range of integers with fields `lo` and `hi`. -/
structure IntRange where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

namespace IntRange

/-- A range is empty when `hi < lo`. -/
def empty (r : IntRange) : Prop := r.hi < r.lo

/-- A range is nonempty when `lo ≤ hi`. -/
def nonempty (r : IntRange) : Prop := r.lo ≤ r.hi

/-- Nonempty ranges are exactly the non-empty ones. -/
@[simp]
theorem nonempty_iff_not_empty (r : IntRange) :
    r.nonempty ↔ ¬ r.empty := by
  simp [nonempty, empty, not_lt]

/-- View a range as a set of integers using the closed interval. -/
def toSet (r : IntRange) : Set Int := Set.Icc r.lo r.hi

/-- The number of integers in an inclusive range. Empty ranges contribute zero. -/
def cardinality (r : IntRange) : Nat :=
  if r.lo ≤ r.hi then Int.toNat (r.hi - r.lo + 1) else 0

@[simp] lemma cardinality_of_nonempty {r : IntRange} (h : r.lo ≤ r.hi) :
    r.cardinality = Int.toNat (r.hi - r.lo + 1) := by
  simp [cardinality, h]

@[simp] lemma cardinality_of_empty {r : IntRange} (h : r.hi < r.lo) :
    r.cardinality = 0 := by
  simp [cardinality, not_le.mpr h]

/-- The set view is empty iff `hi < lo`. -/
@[simp]
lemma toSet_eq_empty_iff (r : IntRange) :
    r.toSet = (∅ : Set Int) ↔ r.hi < r.lo := by
  simp [toSet, Set.Icc_eq_empty_iff, not_le]

lemma toSet_eq_empty_of_hi_lt_lo {r : IntRange} (h : r.hi < r.lo) :
    r.toSet = (∅ : Set Int) := (toSet_eq_empty_iff r).mpr h

/-- Membership in `toSet` is equivalent to being in the closed interval. -/
@[simp]
lemma mem_toSet_iff (r : IntRange) (x : Int) :
    x ∈ r.toSet ↔ r.lo ≤ x ∧ x ≤ r.hi := by
  simp [toSet]

/-- The set representation is nonempty iff the range is nonempty. -/
@[simp]
lemma toSet_nonempty_iff (r : IntRange) :
    r.toSet.Nonempty ↔ r.nonempty := by
  simp [toSet, Set.nonempty_Icc, nonempty]

instance : DecidablePred empty :=
  fun r => inferInstanceAs (Decidable (r.hi < r.lo))

instance : DecidablePred nonempty :=
  fun r => inferInstanceAs (Decidable (r.lo ≤ r.hi))

/-- Closed-interval merge of two ranges. -/
def mergeRange (a b : IntRange) : IntRange :=
  { lo := min a.lo b.lo, hi := max a.hi b.hi }

/-- A hull is nonempty when its left input is nonempty. -/
lemma mergeRange_nonempty {a b : IntRange}
    (ha : a.nonempty) : (mergeRange a b).nonempty := by
  have h₁ : min a.lo b.lo ≤ a.lo := min_le_left _ _
  have h₂ : a.hi ≤ max a.hi b.hi := le_max_left _ _
  exact le_trans h₁ (le_trans ha h₂)

/-- If `a` and `b` have no integer gap either way, their hull is their union. -/
lemma mergeRange_toSet_of_noGap
    {a b : IntRange}
    (h₁ : ¬ (a.hi + 1 < b.lo))
    (h₂ : ¬ (b.hi + 1 < a.lo)) :
    (mergeRange a b).toSet = a.toSet ∪ b.toSet := by
  ext x; constructor <;> intro hx
  · have h_lo :
      min a.lo b.lo ≤ x := by
        simpa [IntRange.mem_toSet_iff, mergeRange] using hx.left
    have h_hi :
      x ≤ max a.hi b.hi := by
        simpa [IntRange.mem_toSet_iff, mergeRange] using hx.right
    have h_lo' := (min_le_iff).1 h_lo
    have h_hi' := (le_max_iff).1 h_hi
    cases h_lo' with
    | inl h_ax =>
      cases h_hi' with
      | inl h_xa =>
        exact Or.inl ⟨h_ax, h_xa⟩
      | inr h_xb =>
        by_cases h_bx : b.lo ≤ x
        · exact Or.inr ⟨h_bx, h_xb⟩
        ·
          have hx_lt : x < b.lo := lt_of_not_ge h_bx
          have hb_le : b.lo ≤ a.hi + 1 := not_lt.mp h₁
          have hx_lt' : x < a.hi + 1 := lt_of_lt_of_le hx_lt hb_le
          have hx_le_a : x ≤ a.hi := by
            linarith
          exact Or.inl ⟨h_ax, hx_le_a⟩
    | inr h_bx =>
      cases h_hi' with
      | inl h_xa =>
        by_cases h_ax : a.lo ≤ x
        · exact Or.inl ⟨h_ax, h_xa⟩
        ·
          have hx_lt : x < a.lo := lt_of_not_ge h_ax
          have ha_le : a.lo ≤ b.hi + 1 := not_lt.mp h₂
          have hx_lt' : x < b.hi + 1 := lt_of_lt_of_le hx_lt ha_le
          have hx_le_b : x ≤ b.hi := by
            linarith
          exact Or.inr ⟨h_bx, hx_le_b⟩
      | inr h_xb =>
        exact Or.inr ⟨h_bx, h_xb⟩
  · cases hx with
    | inl hx_a =>
      refine ⟨?_, ?_⟩
      · exact le_trans (min_le_left _ _) hx_a.left
      · exact le_trans hx_a.right (le_max_left _ _)
    | inr hx_b =>
      refine ⟨?_, ?_⟩
      · exact le_trans (min_le_right _ _) hx_b.left
      · exact le_trans hx_b.right (le_max_right _ _)

/-- Convenient abbreviation for nonempty ranges as a subtype. -/
abbrev NR := { r : IntRange // r.nonempty }

namespace NR

/-- One nonempty range comes before another with a gap if the first ends before the second starts. -/
def before (a b : NR) : Prop := a.val.hi + 1 < b.val.lo

scoped infixl:50 " ≺ " => NR.before

/-- If `a ≺ b`, then `a` starts strictly before `b`: `a.lo < b.lo`. -/
lemma before_lo_lt {a b : NR} (h : a ≺ b) :
    a.val.lo < b.val.lo := by
  exact lt_of_le_of_lt a.property (lt_trans (lt_add_one _) h)

/-- The gap-separated `before` relation cannot hold in both directions. -/
lemma before_asymm {a b : NR} (h : a ≺ b) : ¬ (b ≺ a) := by
  intro h'
  exact (before_lo_lt h).asymm (before_lo_lt h')

/-- The gap-separated ordering relation is transitive. -/
lemma before_trans {a b c : NR} (hab : a ≺ b) (hbc : b ≺ c) : a ≺ c := by
  unfold before at *
  have h₁ : a.val.hi + 1 ≤ b.val.hi :=
    (lt_of_lt_of_le hab b.property).le
  have h₂ : b.val.hi ≤ b.val.hi + 1 := by
    linarith
  have h₃ : b.val.hi < c.val.lo := lt_of_le_of_lt h₂ hbc
  exact lt_of_le_of_lt h₁ h₃

/-- In a pairwise-`before` decomposition `prefix ++ suffix`, the last range of
the prefix is before every range in the suffix. -/
lemma pairwise_before_prefix_last_suffix
    {prefixRanges suffixRanges : List NR} {prev : NR}
    (hpair : List.Pairwise NR.before (prefixRanges ++ suffixRanges))
    (hlast : prefixRanges.getLast? = some prev) :
    ∀ nr ∈ suffixRanges, prev ≺ nr := by
  intro nr hnr
  exact (List.pairwise_append.mp hpair).2.2 prev
    (List.mem_of_mem_getLast? (by simp [hlast])) nr hnr

/-- Every range after a strict lower-bound split starts at or after the split
key. Canonical ordering propagates the first failed predicate through the
suffix. -/
lemma strict_start_split_suffix_lower_bound
    (ranges : List NR) (start : Int)
    (hpw : List.Pairwise before ranges) :
    ∀ nr ∈ (List.span (fun candidate => decide (candidate.val.lo < start)) ranges).snd,
      start ≤ nr.val.lo := by
  rw [List.span_eq_takeWhile_dropWhile]
  induction ranges with
  | nil => simp
  | cons first rest ih =>
      by_cases hfirst : first.val.lo < start
      · rw [List.dropWhile_cons_of_pos (by simp [hfirst])]
        exact ih hpw.tail
      · rw [List.dropWhile_cons_of_neg (by simp [hfirst])]
        intro nr hmem
        rw [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact not_lt.mp hfirst
        · exact le_trans (not_lt.mp hfirst)
            (before_lo_lt (List.rel_of_pairwise_cons hpw hmem)).le

/-- Gap-separated ranges have disjoint set representations. -/
lemma disjoint_of_before {a b : NR} (h : a ≺ b) :
    a.val.toSet ∩ b.val.toSet = (∅ : Set Int) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hax, hbx⟩
    rcases (IntRange.mem_toSet_iff a.val x).1 hax with ⟨_, hax_hi⟩
    rcases (IntRange.mem_toSet_iff b.val x).1 hbx with ⟨hbx_lo, _⟩
    have h_lt : a.val.hi < b.val.lo := lt_trans (lt_add_one _) h
    exact (not_le_of_gt h_lt) (le_trans hbx_lo hax_hi)
  · intro hx
    cases hx

instance : DecidableRel before :=
  fun a b => inferInstanceAs (Decidable (a.val.hi + 1 < b.val.lo))

/-- Two nonempty closed integer ranges are mergeable when their union has no
integer gap: neither range is strictly before the other. -/
def mergeable (a b : NR) : Prop :=
  ¬ a ≺ b ∧ ¬ b ≺ a

instance : DecidableRel mergeable :=
  fun a b => inferInstanceAs (Decidable (¬ a ≺ b ∧ ¬ b ≺ a))

/-- Mergeability is symmetric. -/
lemma mergeable_comm {a b : NR} : mergeable a b ↔ mergeable b a := by
  simp only [mergeable, and_comm]

/-- Lower-endpoint preorder: `a` starts no later than `b` (`a.lo ≤ b.lo`). -/
def startsBefore (a b : NR) : Prop := a.val.lo ≤ b.val.lo

instance : DecidableRel startsBefore :=
  fun a b => inferInstanceAs (Decidable (a.val.lo ≤ b.val.lo))

/-- For ranges ordered by lower endpoint, the forward no-gap test is enough
to establish symmetric mergeability. -/
lemma mergeable_of_startsBefore_of_not_before {a b : NR}
    (horder : startsBefore a b) (hnot : ¬ a ≺ b) :
    mergeable a b := by
  refine ⟨hnot, ?_⟩
  intro hba
  unfold startsBefore at horder
  unfold before at hba
  have hb := b.property
  change b.val.lo ≤ b.val.hi at hb
  linarith

/-- 3-way discriminator: `a` is left of `b`, `b` is left of `a`, or they are mergeable. -/
inductive Rel3 (a b : NR) : Type where
  | left : (a ≺ b) → Rel3 a b
  | right : (b ≺ a) → Rel3 a b
  | mergeable : mergeable a b → Rel3 a b

open Classical

/-- Total classifier returning a `Rel3 a b`. -/
def Rel3.classify (a b : NR) : Rel3 a b := by
  classical
  by_cases h₁ : a ≺ b
  · exact Rel3.left h₁
  ·
    by_cases h₂ : b ≺ a
    · exact Rel3.right h₂
    · exact Rel3.mergeable ⟨h₁, h₂⟩

/-- Merge two overlapping/touching ranges into a single nonempty range. -/
def glue (a b : NR) : NR :=
  ⟨IntRange.mergeRange a.val b.val,
    IntRange.mergeRange_nonempty a.property⟩

/-- Gluing onto `a` preserves mergeability with any range already mergeable with `a`. -/
lemma mergeable_glue_left {a b c : NR} (h : mergeable a c) :
    mergeable (glue a b) c := by
  rcases h with ⟨hac, hca⟩
  constructor
  · intro hgap
    apply hac
    unfold glue IntRange.mergeRange before at hgap
    change max a.val.hi b.val.hi + 1 < c.val.lo at hgap
    change a.val.hi + 1 < c.val.lo
    have hmax : a.val.hi + 1 ≤ max a.val.hi b.val.hi + 1 := by
      calc
        a.val.hi + 1 = 1 + a.val.hi := add_comm _ _
        _ ≤ 1 + max a.val.hi b.val.hi :=
          add_le_add_right (le_max_left _ _) _
        _ = max a.val.hi b.val.hi + 1 := add_comm _ _
    exact lt_of_le_of_lt hmax hgap
  · intro hgap
    apply hca
    unfold glue IntRange.mergeRange before at hgap
    change c.val.hi + 1 < min a.val.lo b.val.lo at hgap
    change c.val.hi + 1 < a.val.lo
    exact lt_of_lt_of_le hgap (min_le_left _ _)

lemma glue_sets (a b : NR) (h : mergeable a b) :
    (glue a b).val.toSet = a.val.toSet ∪ b.val.toSet := by
  rcases h with ⟨h₁, h₂⟩
  have :
      (IntRange.mergeRange a.val b.val).toSet =
        a.val.toSet ∪ b.val.toSet := by
    simpa using
      (IntRange.mergeRange_toSet_of_noGap
        (a := a.val) (b := b.val)
        (by simpa [before] using h₁)
        (by
          have := h₂
          simpa [before] using this))
  simpa [glue] using this

/-- A range before both inputs is before their glue. -/
lemma before_glue {z a b : NR}
    (hza : z ≺ a) (hzb : z ≺ b) :
    z ≺ glue a b := by
  unfold before glue IntRange.mergeRange at *
  have : z.val.hi + 1 < min a.val.lo b.val.lo := lt_min hza hzb
  simpa using this

/-- The glue of two ranges before a third range is also before it. -/
lemma glue_before {a b z : NR}
    (haz : a ≺ z) (hbz : b ≺ z) :
    glue a b ≺ z := by
  unfold before glue IntRange.mergeRange at *
  rw [max_add]
  exact max_lt haz hbz

end NR

/-- Coercion from `IntRange` to `Set Int`. -/
instance : Coe IntRange (Set Int) where
  coe := toSet

end IntRange

open IntRange (NR)
open scoped IntRange.NR
open IntRange.NR

/-- A canonical list of nonempty ranges, ordered with genuine gaps. -/
structure RangeSetBlaze where
  ranges : List NR
  canonical : List.Pairwise (· ≺ ·) ranges
  deriving Repr

namespace RangeSetBlaze

/-- The set represented by a list of nonempty integer ranges. -/
def rangesToSet (rs : List NR) : Set Int :=
  rs.foldr (fun r acc => r.val.toSet ∪ acc) (∅ : Set Int)

/-- The sum of the inclusive cardinalities of a range list. For a canonical
list this is the cardinality of the represented finite integer set. -/
def rangesCardinality (rs : List NR) : Nat :=
  rs.foldr (fun r total => r.val.cardinality + total) 0

@[simp] lemma rangesCardinality_nil :
    rangesCardinality ([] : List NR) = 0 := rfl

@[simp] lemma rangesCardinality_cons (r : NR) (rs : List NR) :
    rangesCardinality (r :: rs) = r.val.cardinality + rangesCardinality rs := rfl

/-- The mathematical element count represented by a range set. -/
def cardinality (s : RangeSetBlaze) : Nat :=
  rangesCardinality s.ranges

@[simp] lemma rangesToSet_nil :
    rangesToSet ([] : List NR) = (∅ : Set Int) := rfl

@[simp] lemma rangesToSet_cons (r : NR) (rs : List NR) :
    rangesToSet (r :: rs) = r.val.toSet ∪ rangesToSet rs := rfl

@[simp] lemma rangesToSet_append (xs ys : List NR) :
    rangesToSet (xs ++ ys) = rangesToSet xs ∪ rangesToSet ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [ih, Set.union_left_comm, Set.union_comm]

/-- Every range occurring in a list is contained in that list's represented set. -/
private lemma member_toSet_subset_rangesToSet
    {ranges : List NR} {nr : NR} (hmem : nr ∈ ranges) :
    nr.val.toSet ⊆ rangesToSet ranges := by
  induction ranges with
  | nil => simp at hmem
  | cons x xs ih =>
      rw [rangesToSet_cons]
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Set.subset_union_left
      · exact Set.subset_union_of_subset_right (ih htail) _

/-- An interval bounded inside a stored range is contained in the represented
set of the whole range list. -/
lemma toSet_subset_rangesToSet_of_mem_of_bounds
    {ranges : List NR} {input : IntRange} {container : NR}
    (hmem : container ∈ ranges)
    (hlo : container.val.lo ≤ input.lo)
    (hhi : input.hi ≤ container.val.hi) :
    input.toSet ⊆ rangesToSet ranges := by
  refine Set.Subset.trans ?_ (member_toSet_subset_rangesToSet hmem)
  intro x hx
  rw [IntRange.mem_toSet_iff] at hx ⊢
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

/-- Convert a `RangeSetBlaze` to the set represented by its range list. -/
def toSet (L : RangeSetBlaze) : Set Int :=
  rangesToSet L.ranges

/-- The record set view is definitionally the set represented by its ranges. -/
@[simp] lemma toSet_eq_rangesToSet (L : RangeSetBlaze) :
    L.toSet = rangesToSet L.ranges := rfl

end RangeSetBlaze

/-!
## Shared integer range-map semantics

Raw run lists have first-match semantics, while `RangeMapBlaze` packages a
canonical list. Input ranges reuse `IntRange`, and stored runs reuse `NR`.

We maintain the canonical representation invariant, but do not prove canonical
uniqueness; uniqueness is not needed for the semantic foundation developed here.
-/

namespace RangeMapBlaze

/-- A nonempty integer range carrying one opaque value. -/
structure Run (Value : Type*) where
  range : NR
  value : Value

namespace Run

/-- Value-independent run order: the ranges are sorted and do not overlap. -/
def disjointBefore {Value : Type*} (a b : Run Value) : Prop :=
  a.range.val.hi < b.range.val.lo

/-- Canonical runs do not overlap; equal-valued touching runs are disallowed. -/
def before {Value : Type*} (a b : Run Value) : Prop :=
  disjointBefore a b ∧
    (a.value = b.value → a.range ≺ b.range)

/-- Canonically shaped runs have strictly ordered, nonoverlapping endpoints. -/
lemma before_hi_lt {Value : Type*} {a b : Run Value} (h : before a b) :
    a.range.val.hi < b.range.val.lo :=
  h.1

/-- A run that canonically precedes another also starts earlier. -/
lemma before_lo_lt {Value : Type*} {a b : Run Value} (h : before a b) :
    a.range.val.lo < b.range.val.lo :=
  lt_of_le_of_lt a.range.property h.1

/-- Equal-valued canonical neighbors have a genuine integer gap. -/
lemma before_range_of_value_eq {Value : Type*} {a b : Run Value}
    (h : before a b) (hvalue : a.value = b.value) : a.range ≺ b.range :=
  h.2 hvalue

/-- Mergeable canonical neighbors necessarily differ in value; because canonical
neighbors do not overlap, this is precisely the legal touching case. -/
lemma value_ne_of_before_of_mergeable {Value : Type*} {a b : Run Value}
    (h : before a b) (hmerge : NR.mergeable a.range b.range) :
    a.value ≠ b.value := by
  intro hvalue
  exact hmerge.1 (h.2 hvalue)

/-- Canonical run order is asymmetric. -/
lemma before_asymm {Value : Type*} {a b : Run Value} (h : before a b) :
    ¬ before b a := by
  intro h'
  exact (before_lo_lt h).asymm (before_lo_lt h')

/-- Canonical run order is transitive. -/
lemma before_trans {Value : Type*} {a b c : Run Value}
    (hab : before a b) (hbc : before b c) : before a c := by
  have hb : b.range.val.lo ≤ b.range.val.hi := b.range.property
  have hab_hi : a.range.val.hi < b.range.val.lo := hab.1
  have hbc_hi : b.range.val.hi < c.range.val.lo := hbc.1
  have hgap : a.range.val.hi + 1 < c.range.val.lo := by
    omega
  refine ⟨lt_trans hab.1 (lt_of_le_of_lt b.range.property hbc.1), ?_⟩
  intro hvalue
  simpa only [IntRange.NR.before] using hgap

end Run

/-- A run list has canonical shape when every earlier run canonically precedes every
later run. -/
abbrev Canonical {Value : Type*} (runs : List (Run Value)) : Prop :=
  List.Pairwise Run.before runs

/-- Interpret a raw run list using executable first-match semantics. -/
def runsToFunction {Value : Type*} : List (Run Value) → Int → Option Value
  | [], _ => none
  | run :: rest, key =>
      letI : Decidable (key ∈ run.range.val.toSet) :=
        decidable_of_iff (run.range.val.lo ≤ key ∧ key ≤ run.range.val.hi)
          (IntRange.mem_toSet_iff run.range.val key).symm
      if key ∈ run.range.val.toSet then
        some run.value
      else
        runsToFunction rest key

@[simp] lemma runsToFunction_nil {Value : Type*} (key : Int) :
    runsToFunction ([] : List (Run Value)) key = none :=
  rfl

@[simp] lemma runsToFunction_cons {Value : Type*}
    (run : Run Value) (rest : List (Run Value)) (key : Int) :
    runsToFunction (run :: rest) key =
      if run.range.val.lo ≤ key ∧ key ≤ run.range.val.hi then
        some run.value
      else
        runsToFunction rest key :=
  by simp [runsToFunction, IntRange.mem_toSet_iff]

/-- First-match interpretation of an append consults the suffix exactly when
the prefix has no value for the key. -/
lemma runsToFunction_append {Value : Type*}
    (xs ys : List (Run Value)) (key : Int) :
    runsToFunction (xs ++ ys) key =
      match runsToFunction xs key with
      | some value => some value
      | none => runsToFunction ys key := by
  induction xs with
  | nil => simp
  | cons run rest ih =>
      simp only [List.cons_append, runsToFunction_cons, ih]
      split <;> simp

/-- Pointwise overwrite by an inclusive integer input range. -/
def overwrite {Value : Type*}
    (old : Int → Option Value) (range : IntRange) (value : Value)
    (key : Int) : Option Value :=
  letI : Decidable (key ∈ range.toSet) :=
    decidable_of_iff (range.lo ≤ key ∧ key ≤ range.hi)
      (IntRange.mem_toSet_iff range key).symm
  if key ∈ range.toSet then some value else old key

@[simp] lemma overwrite_of_contains {Value : Type*}
    (old : Int → Option Value) (range : IntRange) (value : Value)
    (key : Int) (h : key ∈ range.toSet) :
    overwrite old range value key = some value := by
  simp [overwrite, h]

@[simp] lemma overwrite_of_not_contains {Value : Type*}
    (old : Int → Option Value) (range : IntRange) (value : Value)
    (key : Int) (h : ¬ key ∈ range.toSet) :
    overwrite old range value key = old key := by
  simp [overwrite, h]

/-- Overwriting by a reversed input range changes no key. -/
lemma overwrite_eq_of_hi_lt_lo {Value : Type*}
    (old : Int → Option Value) (range : IntRange) (value : Value)
    (h : range.hi < range.lo) :
    overwrite old range value = old := by
  funext key
  apply overwrite_of_not_contains
  intro hcontains
  rw [IntRange.mem_toSet_iff] at hcontains
  exact (not_le_of_gt h) (hcontains.1.trans hcontains.2)

end RangeMapBlaze

/-- A range map represented by canonical, nonempty, labeled integer runs. -/
structure RangeMapBlaze (Value : Type*) where
  runs : List (RangeMapBlaze.Run Value)
  canonical : RangeMapBlaze.Canonical runs

namespace RangeMapBlaze

/-- Interpret a packaged range map as a partial function on integers. -/
def toFunction {Value : Type*} (map : RangeMapBlaze Value) : Int → Option Value :=
  runsToFunction map.runs

/-- The support (key set) of a range map consists exactly of mapped keys. -/
def support {Value : Type*} (map : RangeMapBlaze Value) : Set Int :=
  { key | map.toFunction key ≠ none }

section Examples

example :
    runsToFunction
      ([⟨⟨⟨1, 3⟩, by decide⟩, 10⟩,
        ⟨⟨⟨5, 7⟩, by decide⟩, 20⟩] : List (Run Nat)) 2 =
      some 10 := by decide

example :
    runsToFunction
      ([⟨⟨⟨1, 3⟩, by decide⟩, 10⟩,
        ⟨⟨⟨5, 7⟩, by decide⟩, 20⟩] : List (Run Nat)) 4 =
      none := by decide

example :
    runsToFunction
      ([⟨⟨⟨1, 5⟩, by decide⟩, 10⟩,
        ⟨⟨⟨3, 7⟩, by decide⟩, 20⟩] : List (Run Nat)) 4 =
      some 10 := by decide

example : Canonical
    ([⟨⟨⟨1, 3⟩, by decide⟩, 10⟩,
      ⟨⟨⟨4, 6⟩, by decide⟩, 20⟩] : List (Run Nat)) := by
  simp [Canonical, Run.before, Run.disjointBefore, IntRange.NR.before]

example : ¬ Canonical
    ([⟨⟨⟨1, 3⟩, by decide⟩, 10⟩,
      ⟨⟨⟨4, 6⟩, by decide⟩, 10⟩] : List (Run Nat)) := by
  simp [Canonical, Run.before, Run.disjointBefore, IntRange.NR.before]

example :
    overwrite (fun _ : Int => some 10) ⟨2, 4⟩ 20 3 = some 20 := by
  norm_num [overwrite]

example :
    overwrite (fun _ : Int => some 10) ⟨2, 4⟩ 20 5 = some 10 := by
  norm_num [overwrite]

example :
    overwrite (fun key : Int => if key = 0 then some 10 else none) ⟨4, 2⟩ 20 =
      (fun key => if key = 0 then some 10 else none) := by
  apply overwrite_eq_of_hi_lt_lo
  decide

end Examples

end RangeMapBlaze
