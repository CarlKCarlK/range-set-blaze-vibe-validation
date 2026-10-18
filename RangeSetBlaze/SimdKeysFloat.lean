import RangeSetBlaze.SimdKeysInt
import Std.Tactic.BVDecide

/-!
# Float keys for the kernel

Rust orders `Total` and `NotNan` floats with `total_cmp`, which reads a float's bits as an
*ordered* signed integer: it flips every bit but the sign of a negative value
(`bits ^ ((bits >> (w-1)) as unsigned >> 1)`) and compares the results as signed integers. So we
model a float by that ordered value, a `SignedBits w`, and the float's bits are
`totalOrdered ordered` (the transform is its own inverse).

* A `Total` float is any `SignedBits w`. Its order is signed order, and Rust's `sub_one` subtracts
  one from the ordered value, exactly as for signed integers.
* A `NotNan` float is a `SignedBits w` whose bits are neither a NaN nor `-0.0`. Its `sub_one` is the
  next smaller such value. The only valid ordered value it can skip is `-1`, the bits of `-0.0`,
  which lies between the largest negative subnormal (`-2`) and `+0.0` (`0`).

Rust's `from_slice` loads each float as the lane `floatKey bits` (`f32_key` / `f64_key`: flip all
bits of a negative value, or set the sign bit of a non-negative one). The one width-specific fact
the proof needs is `floatKey (totalOrdered o) = o + 2^(w-1)`: the lane is the ordered value shifted
into unsigned order, which is what the signed-integer lane key already proves sound. That fact, and
where NaN and `-0.0` sit, are checked for 32 and 64 bits by `bv_decide`.
-/

namespace SimdRunCheck

/-- Rust's `total_cmp` transform: flip every bit but the sign of a negative value. It is its own
inverse, mapping a float's bits to its ordered value and back. -/
def totalOrdered {w : Nat} (b : BitVec w) : BitVec w :=
  b ^^^ ((b.sshiftRight (w - 1)) >>> 1)

/-- Rust's `f32_key` / `f64_key`: the lane `from_slice` loads for a float's `bits`. -/
def floatKey {w : Nat} (b : BitVec w) : BitVec w :=
  if b.msb then ~~~b else b ||| BitVec.ofNat w (2 ^ (w - 1))

/-- The facts about one float width that the proofs use. Each is checked by `bv_decide` or
`decide` for `f32` and `f64` below. -/
structure FloatWidth (w : Nat) where
  pos : 0 < w
  /-- Whether float bits are a NaN. -/
  isNaN : BitVec w → Bool
  /-- **The lane is the ordered value shifted into unsigned order.** -/
  key_eq : ∀ o : BitVec w, floatKey (totalOrdered o) = o + BitVec.ofNat w (2 ^ (w - 1))
  /-- The ordered value `-1` is `-0.0`, whose bits are just the sign bit. -/
  neg_zero : totalOrdered (0 - 1 : BitVec w) = BitVec.ofNat w (2 ^ (w - 1))
  /-- The smallest ordered value is a NaN, so a `NotNan` value never has it. -/
  min_nan : isNaN (totalOrdered (BitVec.ofNat w (2 ^ (w - 1)))) = true
  /-- `+0.0` (ordered value `0`) is a valid `NotNan`. -/
  zero_not_nan : isNaN (totalOrdered (0 : BitVec w)) = false
  zero_ne_neg_zero : totalOrdered (0 : BitVec w) ≠ BitVec.ofNat w (2 ^ (w - 1))
  /-- `-2 < -1 < 0` as signed values. -/
  neg_two_lt_neg_one : ((0 : BitVec w) - 2).toInt < ((0 : BitVec w) - 1).toInt
  neg_one_lt_zero : ((0 : BitVec w) - 1).toInt < (0 : BitVec w).toInt
  neg_one_sub_one : (0 : BitVec w) - 1 - 1 = 0 - 2

/-! ## `Total` floats -/

/-- `Total` floats: the key is the ordered value, the lane is Rust's `floatKey` of the float's bits
with no shift, and `sub_one` is the ordered value's `- 1`. -/
def totalLaneKey {w : Nat} (fw : FloatWidth w) : LaneKey (SignedBits w) w where
  lane k := floatKey (totalOrdered k.bits)
  shift := 0
  le_iff a b := by
    show a ≤ b ↔ floatKey (totalOrdered a.bits) + 0 ≤ floatKey (totalOrdered b.bits) + 0
    have add_zero : ∀ x : BitVec w, x + 0 = x := fun x => by simp
    rw [fw.key_eq, fw.key_eq, add_zero, add_zero]
    exact (signedLaneKey w fw.pos).le_iff a b
  pred := (signedLaneKey w fw.pos).pred
  pred_spec := (signedLaneKey w fw.pos).pred_spec

/-! ## `NotNan` floats -/

/-- Whether an ordered value is a `NotNan` float: its bits are neither a NaN nor `-0.0`. -/
def notNanValid {w : Nat} (fw : FloatWidth w) (k : SignedBits w) : Prop :=
  fw.isNaN (totalOrdered k.bits) = false ∧ totalOrdered k.bits ≠ BitVec.ofNat w (2 ^ (w - 1))

instance {w : Nat} (fw : FloatWidth w) (k : SignedBits w) : Decidable (notNanValid fw k) := by
  unfold notNanValid; infer_instance

/-- A `NotNan` float of width `w`, as its ordered value. -/
abbrev NotNanBits {w : Nat} (fw : FloatWidth w) := { k : SignedBits w // notNanValid fw k }

instance {w : Nat} (fw : FloatWidth w) : Inhabited (NotNanBits fw) :=
  ⟨⟨⟨0⟩, fw.zero_not_nan, fw.zero_ne_neg_zero⟩⟩

/-- Rust's `<NotNan as Integer>::sub_one`: the next smaller `NotNan` value. From `+0.0` it skips
`-0.0` (ordered `-1`) to ordered `-2`. Its value at the smallest `NotNan` is irrelevant (it returns
its input there); the kernel never asks for the predecessor of a key with none below it. -/
def notNanPred {w : Nat} (fw : FloatWidth w) (x : NotNanBits fw) : NotNanBits fw :=
  let o : SignedBits w := if x.1.bits = 0 then ⟨0 - 2⟩ else ⟨x.1.bits - 1⟩
  if h : notNanValid fw o then ⟨o, h⟩ else x

/-- `NotNan` floats: the same lane as `Total`, restricted to valid values. No `NotNan` value lies
strictly between `notNanPred x` and `x`: either the predecessor is the previous ordered value, or
`x` is `+0.0` and the only ordered value skipped is `-0.0`, which isn't a `NotNan`. -/
def notNanLaneKey {w : Nat} (fw : FloatWidth w) : LaneKey (NotNanBits fw) w where
  lane k := floatKey (totalOrdered k.1.bits)
  shift := 0
  le_iff a b := (totalLaneKey fw).le_iff a.1 b.1
  pred := notNanPred fw
  pred_spec x y hlt hpred k := by
    have signed := (signedLaneKey w fw.pos).pred_spec
    change ∀ x y : SignedBits w, y < x → (⟨x.bits - 1⟩ : SignedBits w) = y → ∀ k, y < k ↔ x ≤ k
      at signed
    show y.1 < k.1 ↔ x.1 ≤ k.1
    by_cases hzero : x.1.bits = 0
    · -- `x` is `+0.0`: its predecessor is ordered `-2`, and the skipped `-1` is `-0.0`.
      have hpred' : notNanPred fw x =
          if h : notNanValid fw ⟨0 - 2⟩ then ⟨⟨0 - 2⟩, h⟩ else x := by
        simp only [notNanPred, hzero, if_true]
      rw [hpred'] at hpred
      split at hpred
      · have hy : y.1 = ⟨0 - 2⟩ := by rw [← hpred]
        let m : SignedBits w := ⟨0 - 1⟩
        have hmx : m < x.1 := by
          change m.bits.toInt < x.1.bits.toInt
          rw [hzero]; exact fw.neg_one_lt_zero
        have hym : y.1 < m := by
          change y.1.bits.toInt < m.bits.toInt
          rw [hy]; exact fw.neg_two_lt_neg_one
        have hupper := signed x.1 m hmx (by
          show (⟨x.1.bits - 1⟩ : SignedBits w) = ⟨0 - 1⟩; rw [hzero])
        have hlower := signed m y.1 hym (by
          show (⟨(0 - 1) - 1⟩ : SignedBits w) = y.1; rw [hy, fw.neg_one_sub_one])
        have hkm : k.1 ≠ m := by
          intro heq
          apply k.2.2
          rw [show k.1.bits = (0 : BitVec w) - 1 by rw [heq]]
          exact fw.neg_zero
        rw [hlower k.1, ← hupper k.1, le_iff_lt_or_eq]
        constructor
        · rintro (h | h)
          · exact h
          · exact absurd h.symm hkm
        · exact Or.inl
      · rw [← hpred] at hlt
        exact absurd hlt (lt_irrefl _)
    · -- Otherwise the predecessor is the previous ordered value.
      have hpred' : notNanPred fw x =
          if h : notNanValid fw ⟨x.1.bits - 1⟩ then ⟨⟨x.1.bits - 1⟩, h⟩ else x := by
        simp only [notNanPred, hzero, if_false]
      rw [hpred'] at hpred
      split at hpred
      · exact signed x.1 y.1 hlt (by rw [← hpred]) k.1
      · rw [← hpred] at hlt
        exact absurd hlt (lt_irrefl _)

/-! ## `f32` and `f64` -/

/-- `f32`: a NaN has every exponent bit set and a nonzero mantissa. -/
def f32Width : FloatWidth 32 where
  pos := by decide
  isNaN b := BitVec.ult 0x7F800000#32 (b &&& 0x7FFFFFFF#32)
  key_eq o := by
    unfold floatKey totalOrdered
    simp only [show (2 : Nat) ^ (32 - 1) = 0x80000000 by rfl]
    bv_decide
  neg_zero := by decide
  min_nan := by decide
  zero_not_nan := by decide
  zero_ne_neg_zero := by decide
  neg_two_lt_neg_one := by decide
  neg_one_lt_zero := by decide
  neg_one_sub_one := by decide

/-- `f64`: a NaN has every exponent bit set and a nonzero mantissa. -/
def f64Width : FloatWidth 64 where
  pos := by decide
  isNaN b := BitVec.ult 0x7FF0000000000000#64 (b &&& 0x7FFFFFFFFFFFFFFF#64)
  key_eq o := by
    unfold floatKey totalOrdered
    simp only [show (2 : Nat) ^ (64 - 1) = 0x8000000000000000 by rfl]
    bv_decide
  neg_zero := by decide
  min_nan := by decide
  zero_not_nan := by decide
  zero_ne_neg_zero := by decide
  neg_two_lt_neg_one := by decide
  neg_one_lt_zero := by decide
  neg_one_sub_one := by decide

/-! ## The shipped configuration -/

/-- **The shipped kernel is correct for every float key type**: 512-bit vectors with unroll factor
4, so `NotNanF32` and `TotalF32` (16 lanes) and `NotNanF64` and `TotalF64` (8 lanes). -/
theorem shipped_float_kernel_correct :
    (∀ values, let k := (notNanLaneKey f32Width).toSimdKey 16 (by decide) (by decide)
      keyRangeSet (k.kernelRanges 4 values) = keySet values ∧
        KeyRangesNonempty (k.kernelRanges 4 values)) ∧
    (∀ values, let k := (notNanLaneKey f64Width).toSimdKey 8 (by decide) (by decide)
      keyRangeSet (k.kernelRanges 4 values) = keySet values ∧
        KeyRangesNonempty (k.kernelRanges 4 values)) ∧
    (∀ values, let k := (totalLaneKey f32Width).toSimdKey 16 (by decide) (by decide)
      keyRangeSet (k.kernelRanges 4 values) = keySet values ∧
        KeyRangesNonempty (k.kernelRanges 4 values)) ∧
    (∀ values, let k := (totalLaneKey f64Width).toSimdKey 8 (by decide) (by decide)
      keyRangeSet (k.kernelRanges 4 values) = keySet values ∧
        KeyRangesNonempty (k.kernelRanges 4 values)) :=
  ⟨fun values => SimdKey.kernelRanges_correct _
      (Or.inr ((notNanLaneKey f32Width).blockSound (by decide) _ (by decide) (by decide))) values,
   fun values => SimdKey.kernelRanges_correct _
      (Or.inr ((notNanLaneKey f64Width).blockSound (by decide) _ (by decide) (by decide))) values,
   fun values => SimdKey.kernelRanges_correct _
      (Or.inr ((totalLaneKey f32Width).blockSound (by decide) _ (by decide) (by decide))) values,
   fun values => SimdKey.kernelRanges_correct _
      (Or.inr ((totalLaneKey f64Width).blockSound (by decide) _ (by decide) (by decide))) values⟩

end SimdRunCheck
