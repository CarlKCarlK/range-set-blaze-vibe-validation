import RangeSetBlaze.SimdKeys
import Mathlib.Data.Char

/-!
# The `char` key type

Rust's `char` is a Unicode scalar value: a code point below `0x110000` that is not a surrogate
(`0xD800` to `0xDFFF`). Its SIMD lane is the `u32` code point, so lane order is key order with no
shift. The only subtlety is `sub_one`, which skips the surrogate gap: the predecessor of
`'\u{E000}'` is `'\u{D7FF}'`. Since no `char` lies in the gap, the two are adjacent keys, which is
what lets a run correctly continue across it.
-/

namespace SimdRunCheck

/-- Order on `Char` is order on code points. -/
theorem char_lt_iff_toNat_lt (a b : Char) : a < b ↔ a.toNat < b.toNat := by
  rw [Char.lt_def, UInt32.lt_iff_toNat_lt]; rfl

/-- Order on `Char` is order on code points. -/
theorem char_le_iff_toNat_le (a b : Char) : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]; rfl

/-- `Char.ofNat` is the identity on valid code points. -/
theorem toNat_ofNat_of_valid (n : Nat) (h : n < 55296 ∨ 57343 < n ∧ n < 1114112) :
    (Char.ofNat n).toNat = n := by
  unfold Char.ofNat Char.ofNatAux
  rw [dif_pos h]
  simp [Char.toNat]

/-- Rust's `<char as Integer>::sub_one`: subtract one from the code point, jumping from `0xDFFF`
(the end of the surrogate gap) to `0xD7FF`. Its value at `'\0'` is irrelevant: the kernel never
asks for the predecessor of a key that has none below it. -/
def charPred (c : Char) : Char :=
  if c.toNat - 1 = 0xDFFF then Char.ofNat 0xD7FF else Char.ofNat (c.toNat - 1)

/-- A code point is at most `0x10FFFF` and avoids the surrogate gap. -/
theorem char_toNat_valid (c : Char) : c.toNat < 55296 ∨ 57343 < c.toNat ∧ c.toNat < 1114112 :=
  c.valid

/-- `char`'s lane is its `u32` code point, and predecessor is `charPred`. No `char` lies strictly
between `charPred x` and `x`: either the predecessor is the previous code point, or `x` is
`'\u{E000}'` and everything between it and `'\u{D7FF}'` is a surrogate, hence not a `char`. -/
def charLaneKey : LaneKey Char 32 where
  lane c := BitVec.ofNat 32 c.toNat
  shift := 0
  le_iff a b := by
    have ha := char_toNat_valid a
    have hb := char_toNat_valid b
    simp only [BitVec.le_def, char_le_iff_toNat_le, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (0 : BitVec 32).toNat = 0 from rfl]
    omega
  pred := charPred
  pred_spec x y hlt hpred k := by
    have hx := char_toNat_valid x
    have hk := char_toNat_valid k
    rw [char_lt_iff_toNat_lt] at hlt
    rw [char_lt_iff_toNat_lt, char_le_iff_toNat_le]
    unfold charPred at hpred
    split at hpred
    · subst hpred
      have : (Char.ofNat 0xD7FF).toNat = 0xD7FF := by
        exact toNat_ofNat_of_valid _ (by omega)
      omega
    · subst hpred
      rw [toNat_ofNat_of_valid _ (by omega)] at hlt ⊢
      omega

/-- **The kernel is correct for `char`.** For any block shape that fits in `2^32` lanes, the
ranges the kernel returns cover exactly the input characters and are all nonempty. -/
theorem char_kernel_correct {lanes chunks : Nat} (hpos : 0 < lanes) (hchunks : 0 < chunks)
    (hblock : chunks * lanes ≤ 2 ^ 32) (values : List Char) :
    keyRangeSet
        ((charLaneKey.toSimdKey lanes hpos (by
          have := Nat.le_mul_of_pos_left lanes hchunks; omega)).kernelRanges chunks values) =
        keySet values ∧
      KeyRangesNonempty
        ((charLaneKey.toSimdKey lanes hpos (by
          have := Nat.le_mul_of_pos_left lanes hchunks; omega)).kernelRanges chunks values) :=
  SimdKey.kernelRanges_correct _ (Or.inr (charLaneKey.blockSound hpos _ hchunks hblock)) values

/-- The shipped configuration: 16 lanes, 4 chunks per block. -/
theorem shipped_char_kernel_correct (values : List Char) :
    keyRangeSet ((charLaneKey.toSimdKey 16 (by decide) (by decide)).kernelRanges 4 values) =
        keySet values ∧
      KeyRangesNonempty ((charLaneKey.toSimdKey 16 (by decide) (by decide)).kernelRanges 4 values) :=
  SimdKey.kernelRanges_correct _ (Or.inr (charLaneKey.blockSound (by decide) _ (by decide)
    (by decide))) values

end SimdRunCheck
