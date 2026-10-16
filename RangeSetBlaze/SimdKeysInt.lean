import RangeSetBlaze.SimdKeys

/-!
# Integer keys for the kernel

Unsigned integers (`u8` through `u64`, `usize`, and `Ipv4Addr`, which Rust orders as a `u32`) use
their bits as the lane with shift `0`. Signed integers use their two's-complement bits as the lane
with shift `2^(w-1)`: adding it turns signed order into unsigned order. Rust's `sub_one` is
`self - 1`, which is the lane's `- 1`.
-/

namespace SimdRunCheck

/-- **A wrapping `- 1` is an immediate predecessor.** If `rank` is an order embedding into
unsigned lanes and `pred` subtracts one from the rank, then `pred x = y` below `x` leaves nothing
strictly between them. -/
theorem pred_spec_of_rank {K : Type} [LinearOrder K] {w : Nat} (rank : K → BitVec w)
    (hrank : ∀ a b, a ≤ b ↔ rank a ≤ rank b) (pred : K → K)
    (hpred : ∀ x, rank (pred x) = rank x - 1) :
    ∀ x y : K, y < x → pred x = y → ∀ k, y < k ↔ x ≤ k := by
  intro x y hlt hxy k
  have hyx : rank y ≤ rank x := (hrank y x).mp hlt.le
  have hnxy : ¬ rank x ≤ rank y := fun h => absurd ((hrank x y).mpr h) (not_le_of_gt hlt)
  have hy : rank y = rank x - 1 := by rw [← hxy]; exact hpred x
  have hxpos : 0 < (rank x).toNat := by
    simp only [BitVec.le_def] at hyx hnxy; omega
  have hsub := toNat_sub_one hxpos
  rw [← hy] at hsub
  rw [lt_iff_le_not_ge, hrank, hrank k y, hrank x k]
  simp only [BitVec.le_def]
  omega

/-! ## Unsigned integers -/

/-- Unsigned integers: the key is the lane, with shift `0`, and `sub_one` is `- 1`. -/
def unsignedLaneKey (w : Nat) : LaneKey (BitVec w) w where
  lane := id
  shift := 0
  le_iff a b := by simp
  pred x := x - 1
  pred_spec := pred_spec_of_rank id (fun _ _ => Iff.rfl) (· - 1) (fun _ => rfl)

/-- **The kernel is correct for unsigned keys** (`u8`, `u16`, `u32`, `u64`, `usize`, `Ipv4Addr`)
for any chunk width `lanes` and unroll factor `chunks` whose block fits in the lane's range. -/
theorem unsigned_kernel_correct (w lanes chunks : Nat) (hpos : 0 < lanes) (hlanes : lanes ≤ 2 ^ w)
    (hchunks : 0 < chunks) (hblock : chunks * lanes ≤ 2 ^ w) (values : List (BitVec w)) :
    keyRangeSet (((unsignedLaneKey w).toSimdKey lanes hpos hlanes).kernelRanges chunks values) =
        keySet values ∧
      KeyRangesNonempty
        (((unsignedLaneKey w).toSimdKey lanes hpos hlanes).kernelRanges chunks values) :=
  SimdKey.kernelRanges_correct _
    (Or.inr ((unsignedLaneKey w).blockSound hpos hlanes hchunks hblock)) values

/-! ## Signed integers -/

/-- A signed `w`-bit integer, stored as its two's-complement bits and ordered by its value. -/
structure SignedBits (w : Nat) where
  /-- The two's-complement bits. -/
  bits : BitVec w
  deriving DecidableEq

instance (w : Nat) : Inhabited (SignedBits w) := ⟨⟨0⟩⟩

/-- Signed order: compare the integers the bits denote. -/
instance (w : Nat) : LinearOrder (SignedBits w) :=
  LinearOrder.lift' (fun x : SignedBits w => x.bits.toInt) (fun a b h => by
    cases a; cases b; simp only [SignedBits.mk.injEq]; exact BitVec.toInt_inj.mp h)

theorem SignedBits.le_def {w : Nat} (a b : SignedBits w) : a ≤ b ↔ a.bits.toInt ≤ b.bits.toInt :=
  Iff.rfl

/-- **Adding `2^(w-1)` turns a signed value into an unsigned one**: the unsigned value of the
shifted bits is the signed value plus `2^(w-1)`. -/
theorem toNat_add_signShift {w : Nat} (hw : 0 < w) (x : BitVec w) :
    ((x + BitVec.ofNat w (2 ^ (w - 1))).toNat : Int) = x.toInt + 2 ^ (w - 1) := by
  have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hp : 0 < 2 ^ (w - 1) := Nat.two_pow_pos _
  have hlt := x.isLt
  have hm : 2 ^ (w - 1) % 2 ^ w = 2 ^ (w - 1) := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, hm, BitVec.toInt_eq_toNat_cond]
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega)]; push_cast; rfl
  · have : (x.toNat + 2 ^ (w - 1)) % 2 ^ w = x.toNat + 2 ^ (w - 1) - 2 ^ w := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [this, Nat.cast_sub (by omega)]; push_cast; omega

/-- Signed integers: the lane is the bits, shifted by `2^(w-1)` so unsigned order on shifted lanes
is signed order, and `sub_one` is `- 1`. -/
def signedLaneKey (w : Nat) (hw : 0 < w) : LaneKey (SignedBits w) w where
  lane := SignedBits.bits
  shift := BitVec.ofNat w (2 ^ (w - 1))
  le_iff a b := by
    rw [SignedBits.le_def, BitVec.le_def]
    have ha := toNat_add_signShift hw a.bits
    have hb := toNat_add_signShift hw b.bits
    omega
  pred x := ⟨x.bits - 1⟩
  pred_spec := pred_spec_of_rank (fun x : SignedBits w => x.bits + BitVec.ofNat w (2 ^ (w - 1)))
    (fun a b => by
      rw [SignedBits.le_def, BitVec.le_def]
      have ha := toNat_add_signShift hw a.bits
      have hb := toNat_add_signShift hw b.bits
      omega)
    (fun x => ⟨x.bits - 1⟩) (fun x => by
      show x.bits - 1 + _ = x.bits + _ - 1
      rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg]; ac_rfl)

/-- **The kernel is correct for signed keys** (`i8`, `i16`, `i32`, `i64`, `isize`) for any chunk
width `lanes` and unroll factor `chunks` whose block fits in the lane's range. -/
theorem signed_kernel_correct (w : Nat) (hw : 0 < w) (lanes chunks : Nat) (hpos : 0 < lanes)
    (hlanes : lanes ≤ 2 ^ w) (hchunks : 0 < chunks) (hblock : chunks * lanes ≤ 2 ^ w)
    (values : List (SignedBits w)) :
    keyRangeSet (((signedLaneKey w hw).toSimdKey lanes hpos hlanes).kernelRanges chunks values) =
        keySet values ∧
      KeyRangesNonempty
        (((signedLaneKey w hw).toSimdKey lanes hpos hlanes).kernelRanges chunks values) :=
  SimdKey.kernelRanges_correct _
    (Or.inr ((signedLaneKey w hw).blockSound hpos hlanes hchunks hblock)) values

/-! ## The shipped configuration -/

/-- **The shipped kernel is correct for every unsigned key type**: 512-bit vectors with unroll
factor 4, so `u8` (64 lanes), `u16` (32), `u32` (16, also `Ipv4Addr`), and `u64` (8). `usize`
matches `u32` or `u64` by target pointer width. -/
theorem shipped_unsigned_kernel_correct :
    (∀ values, let k := (unsignedLaneKey 8).toSimdKey 64 (by decide) (by decide)
      keyRangeSet (k.kernelRanges 4 values) = keySet values ∧
        KeyRangesNonempty (k.kernelRanges 4 values)) ∧
    (∀ values, let k := (unsignedLaneKey 16).toSimdKey 32 (by decide) (by decide)
      keyRangeSet (k.kernelRanges 4 values) = keySet values ∧
        KeyRangesNonempty (k.kernelRanges 4 values)) ∧
    (∀ values, let k := (unsignedLaneKey 32).toSimdKey 16 (by decide) (by decide)
      keyRangeSet (k.kernelRanges 4 values) = keySet values ∧
        KeyRangesNonempty (k.kernelRanges 4 values)) ∧
    (∀ values, let k := (unsignedLaneKey 64).toSimdKey 8 (by decide) (by decide)
      keyRangeSet (k.kernelRanges 4 values) = keySet values ∧
        KeyRangesNonempty (k.kernelRanges 4 values)) :=
  ⟨unsigned_kernel_correct 8 64 4 (by decide) (by decide) (by decide) (by decide),
   unsigned_kernel_correct 16 32 4 (by decide) (by decide) (by decide) (by decide),
   unsigned_kernel_correct 32 16 4 (by decide) (by decide) (by decide) (by decide),
   unsigned_kernel_correct 64 8 4 (by decide) (by decide) (by decide) (by decide)⟩

/-- **The shipped kernel is correct for every signed key type**: 512-bit vectors with unroll
factor 4, so `i8` (64 lanes), `i16` (32), `i32` (16), and `i64` (8). `isize` matches `i32` or
`i64` by target pointer width. -/
theorem shipped_signed_kernel_correct :
    (∀ values, let k := (signedLaneKey 8 (by decide)).toSimdKey 64 (by decide) (by decide)
      keyRangeSet (k.kernelRanges 4 values) = keySet values ∧
        KeyRangesNonempty (k.kernelRanges 4 values)) ∧
    (∀ values, let k := (signedLaneKey 16 (by decide)).toSimdKey 32 (by decide) (by decide)
      keyRangeSet (k.kernelRanges 4 values) = keySet values ∧
        KeyRangesNonempty (k.kernelRanges 4 values)) ∧
    (∀ values, let k := (signedLaneKey 32 (by decide)).toSimdKey 16 (by decide) (by decide)
      keyRangeSet (k.kernelRanges 4 values) = keySet values ∧
        KeyRangesNonempty (k.kernelRanges 4 values)) ∧
    (∀ values, let k := (signedLaneKey 64 (by decide)).toSimdKey 8 (by decide) (by decide)
      keyRangeSet (k.kernelRanges 4 values) = keySet values ∧
        KeyRangesNonempty (k.kernelRanges 4 values)) :=
  ⟨signed_kernel_correct 8 (by decide) 64 4 (by decide) (by decide) (by decide) (by decide),
   signed_kernel_correct 16 (by decide) 32 4 (by decide) (by decide) (by decide) (by decide),
   signed_kernel_correct 32 (by decide) 16 4 (by decide) (by decide) (by decide) (by decide),
   signed_kernel_correct 64 (by decide) 8 4 (by decide) (by decide) (by decide) (by decide)⟩

end SimdRunCheck
