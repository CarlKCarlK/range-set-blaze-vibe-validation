import RangeSetBlaze.SimdKeysInt

/-!
# 128-bit keys for the kernel

`u128`, `Ipv6Addr` (which `from_slice.rs` converts with `u128::from`), and `i128` span two `u64`
lanes: a value's low half sits in an even lane and its high half in the next. One chunk is a
`u64x8` vector holding four values. The chunk test subtracts offsets `0, 1, 2, 3` from the low
lanes only, and compares every lane with `splat(first)`, so it says: all high halves equal
`first`'s, and each value's low half is `first`'s low half plus its index, wrapping at 64 bits.

The lane test alone accepts a chunk whose low halves wrap past `2^64` (the carry never reaches the
high half), so the key-order test `first <= last` is what rules that out: with equal high halves,
a wrap would put the last low half below the first. This module proves it.

Both `u128` and `Ipv6Addr` are modeled by `BitVec 128`. `i128` is `SignedBits 128`; adding `2^127`
leaves each low half unchanged and adds `2^63` to each high half, so the lane test is unchanged
and signed order becomes unsigned order.
-/

namespace SimdRunCheck

/-- The low 64 bits of a 128-bit value: the value held in its low `u64` lane. -/
def lowHalf (x : BitVec 128) : BitVec 64 := x.extractLsb' 0 64

/-- The high 64 bits of a 128-bit value: the value held in its high `u64` lane. -/
def highHalf (x : BitVec 128) : BitVec 64 := x.extractLsb' 64 64

/-- The low half as a natural number is the value modulo `2^64`. -/
theorem toNat_lowHalf (x : BitVec 128) : (lowHalf x).toNat = x.toNat % 2 ^ 64 := by
  simp [lowHalf]
/-- The high half as a natural number is the value divided by `2^64`. -/
theorem toNat_highHalf (x : BitVec 128) : (highHalf x).toNat = x.toNat / 2 ^ 64 := by
  have := x.isLt
  simp [highHalf, Nat.shiftRight_eq_div_pow]
  omega

/-- **A 128-bit value is its two halves**: `value = high * 2^64 + low`. -/
theorem toNat_halves (x : BitVec 128) :
    x.toNat = (highHalf x).toNat * 2 ^ 64 + (lowHalf x).toNat := by
  rw [toNat_lowHalf, toNat_highHalf]; omega

/-- Adding `2^127` leaves the low half unchanged. -/
theorem lowHalf_add_signShift (x : BitVec 128) :
    lowHalf (x + BitVec.ofNat 128 (2 ^ 127)) = lowHalf x := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_lowHalf, toNat_lowHalf, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega
/-- Adding `2^127` adds `2^63` (wrapping) to the high half. -/
theorem highHalf_add_signShift (x : BitVec 128) :
    highHalf (x + BitVec.ofNat 128 (2 ^ 127)) = highHalf x + BitVec.ofNat 64 (2 ^ 63) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  rw [toNat_highHalf, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, toNat_highHalf]
  omega

/-- The two-lane chunk test, as Rust's `(values - offsets) == splat(first)` reads lane by lane:
the low lanes minus their offsets all equal `first`'s low half (that is, the low halves form a
64-bit wrapping run, `lanesMatch`), and every high lane equals `first`'s high half. -/
def halvesMatch (chunk : List (BitVec 128)) : Bool :=
  lanesMatch (chunk.map lowHalf) &&
    (chunk.map highHalf == List.replicate chunk.length (highHalf (chunk.headD 0)))

/-- **The soundness core for 128-bit keys.** If the two-lane test passes, the chunk has at most
`2^64` values, and its first value is at most its last (unsigned), then the chunk is a real run.
All high halves agree, so if the low halves had wrapped, the last value would be below the first.
By `no_wrap_of_le_mod` they did not, so value `i` is `first + i`. -/
theorem isRun_of_halvesMatch {chunk : List (BitVec 128)} (hne : chunk ≠ [])
    (hmatch : halvesMatch chunk = true) (hlen : chunk.length ≤ 2 ^ 64)
    (hle : chunk.headD 0 ≤ chunk.getLastD 0) : IsRun chunk := by
  simp only [halvesMatch, Bool.and_eq_true, beq_iff_eq] at hmatch
  obtain ⟨hlow, hhigh⟩ := hmatch
  rw [lanesMatch_iff, headD_map_of_ne_nil hne _ 0, List.length_map, default_bitVec] at hlow
  have hlowi : ∀ i (h : i < chunk.length), lowHalf chunk[i] =
      lowHalf (chunk.headD 0) + BitVec.ofNat 64 i := by
    intro i h
    have := List.getElem_of_eq hlow (by simpa using h)
    simpa [wrappingRun] using this
  have hhighi : ∀ i (h : i < chunk.length), highHalf chunk[i] = highHalf (chunk.headD 0) := by
    intro i h
    have := List.getElem_of_eq hhigh (by simpa using h)
    simpa using this
  obtain ⟨n, hn⟩ : ∃ n, chunk.length = n + 1 :=
    ⟨chunk.length - 1, by have := List.length_pos_iff.mpr hne; omega⟩
  have hnlt : n < chunk.length := by omega
  have hlast : chunk.getLastD 0 = chunk[n] := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
    simp [hn]
  have hlowNat : ∀ i (h : i < chunk.length), (lowHalf chunk[i]).toNat =
      ((lowHalf (chunk.headD 0)).toNat + i) % 2 ^ 64 := by
    intro i h
    rw [hlowi i h, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := (lowHalf (chunk.headD 0)).isLt
    omega
  have hfirstLt := (lowHalf (chunk.headD 0)).isLt
  have hle' : (chunk.headD 0).toNat ≤ chunk[n].toNat := by rw [← hlast]; exact hle
  have hnoWrap : (lowHalf (chunk.headD 0)).toNat + n < 2 ^ 64 := by
    apply no_wrap_of_le_mod hfirstLt (by omega)
    rw [← hlowNat n hnlt]
    have h1 := toNat_halves (chunk.headD 0)
    have h2 := toNat_halves chunk[n]
    rw [hhighi n hnlt] at h2
    omega
  unfold IsRun
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range']
    have hi : i < chunk.length := by simpa using h1
    have h3 := toNat_halves chunk[i]
    have h4 := toNat_halves (chunk.headD 0)
    rw [hhighi i hi, hlowNat i hi] at h3
    rw [h3]
    have : ((lowHalf (chunk.headD 0)).toNat + i) % 2 ^ 64 = (lowHalf (chunk.headD 0)).toNat + i :=
      Nat.mod_eq_of_lt (by omega)
    omega

/-- How the unrolled block check compares a block of `chunks` chunks of `L` values. Chunk `k` is
compared against `splat(block[0]) + offsets + k * step`: every high half is `hi`, and the low
halves are the wrapping run from `lo`, where `lo` advances by `L` after each chunk. The step adds to
the low lanes only, so `lo` is a 64-bit value. -/
def halvesChunksMatch (L : Nat) (hi lo : BitVec 64) : Nat → List (BitVec 128) → Bool
  | 0, _ => true
  | chunks + 1, block =>
      ((block.take L).map highHalf == List.replicate L hi) &&
        ((block.take L).map lowHalf == wrappingRun lo L) &&
        halvesChunksMatch L hi (lo + BitVec.ofNat 64 L) chunks (block.drop L)

/-- **Stepping chunk by chunk equals one comparison of the whole block** (high halves all `hi`, low
halves one wrapping run). -/
theorem halvesChunksMatch_iff (L : Nat) (hi : BitVec 64) (chunks : Nat) :
    ∀ (lo : BitVec 64) (block : List (BitVec 128)), block.length = chunks * L →
    (halvesChunksMatch L hi lo chunks block = true ↔
      block.map highHalf = List.replicate (chunks * L) hi ∧
        block.map lowHalf = wrappingRun lo (chunks * L)) := by
  induction chunks with
  | zero =>
    intro lo block hlen
    simp only [Nat.zero_mul, List.length_eq_zero_iff] at hlen
    simp [halvesChunksMatch, hlen, wrappingRun]
  | succ chunks ih =>
    intro lo block hlen
    have hsplit := List.take_append_drop L block
    have htake : (block.take L).length = L := by
      simp [List.length_take, hlen, Nat.succ_mul]
    have hdrop : (block.drop L).length = chunks * L := by
      simp [List.length_drop, hlen, Nat.succ_mul]
    rw [Nat.succ_mul, Nat.add_comm (chunks * L) L, wrappingRun_add, ← List.replicate_append_replicate]
    simp only [halvesChunksMatch, Bool.and_eq_true, beq_iff_eq, ih _ _ hdrop]
    have hmap : block.map highHalf = (block.take L).map highHalf ++ (block.drop L).map highHalf := by
      rw [← List.map_append, hsplit]
    have hmap' : block.map lowHalf = (block.take L).map lowHalf ++ (block.drop L).map lowHalf := by
      rw [← List.map_append, hsplit]
    rw [hmap, hmap']
    have hl1 : ((block.take L).map highHalf).length = (List.replicate L hi).length := by rw [List.length_map, htake, List.length_replicate]
    have hl2 : ((block.take L).map lowHalf).length = (wrappingRun lo L).length := by
      rw [List.length_map, htake, length_wrappingRun]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      rw [h1, h2, h3, h4]; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨a1, a2⟩ := List.append_inj h1 hl1
      obtain ⟨b1, b2⟩ := List.append_inj h2 hl2
      exact ⟨⟨a1, b1⟩, a2, b2⟩

/-- Started from the block's own first value, the chunk-by-chunk comparison is `halvesMatch` on the
whole block. -/
theorem halvesChunksMatch_headD_iff (L chunks : Nat) (hpos : 0 < chunks * L)
    (block : List (BitVec 128)) (hlen : block.length = chunks * L) :
    halvesChunksMatch L (highHalf (block.headD 0)) (lowHalf (block.headD 0)) chunks block = true ↔
      halvesMatch block = true := by
  have hne : block ≠ [] := by rintro rfl; rw [List.length_nil] at hlen; omega
  rw [halvesChunksMatch_iff _ _ _ _ _ hlen]
  simp only [halvesMatch, Bool.and_eq_true, beq_iff_eq, lanesMatch_iff,
    headD_map_of_ne_nil hne lowHalf (0 : BitVec 64), default_bitVec, List.length_map, hlen]
  exact and_comm

/-- **The sign shift does not change the lane test.** Adding `2^127` leaves low halves unchanged
and adds the same constant to every high half, so equality of high halves and the low-half run
are both preserved. -/
theorem halvesMatch_map_signShift (chunk : List (BitVec 128)) :
    halvesMatch (chunk.map (· + BitVec.ofNat 128 (2 ^ 127))) = halvesMatch chunk := by
  by_cases hnil : chunk = []
  · subst hnil; rfl
  apply Bool.eq_iff_iff.mpr
  have hlow : (chunk.map (· + BitVec.ofNat 128 (2 ^ 127))).map lowHalf = chunk.map lowHalf := by
    simp only [List.map_map]
    exact List.map_congr_left (fun x _ => lowHalf_add_signShift x)
  have hhigh : (chunk.map (· + BitVec.ofNat 128 (2 ^ 127))).map highHalf =
      chunk.map (fun x => highHalf x + BitVec.ofNat 64 (2 ^ 63)) := by
    simp only [List.map_map]
    exact List.map_congr_left (fun x _ => highHalf_add_signShift x)
  have hhead : (chunk.map (· + BitVec.ofNat 128 (2 ^ 127))).headD 0 =
      chunk.headD 0 + BitVec.ofNat 128 (2 ^ 127) := by
    rw [headD_map_of_ne_nil hnil _ 0, default_bitVec]
  simp only [halvesMatch, Bool.and_eq_true, beq_iff_eq, hlow, hhigh, List.length_map, hhead,
    highHalf_add_signShift, List.eq_replicate_iff, List.mem_map]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rintro b ⟨a, ha, rfl⟩
    have := h3 _ ⟨a, ha, rfl⟩
    simpa using this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    rw [h3 _ ⟨a, ha, rfl⟩]

/-- A chunk that passes the two-lane test and `first ≤ last` (unsigned) is a run of keys
(`u128`, `Ipv6Addr`). -/
theorem isKeyRun_of_halvesMatch {chunk : List (BitVec 128)} (hne : chunk ≠ [])
    (hmatch : halvesMatch chunk = true) (hlen : chunk.length ≤ 2 ^ 64)
    (hle : chunk.headD default ≤ chunk.getLastD default) : IsKeyRun chunk :=
  isKeyRun_of_isRun id (fun _ _ => Iff.rfl) hne
    (by simpa using isRun_of_halvesMatch hne hmatch hlen hle)

/-- The `i128` version: the two-lane test on the raw bits plus `first ≤ last` in signed order. It
reduces to the unsigned case through the rank `bits + 2^127`. -/
theorem isKeyRun_of_signed_halvesMatch {chunk : List (SignedBits 128)} (hne : chunk ≠ [])
    (hmatch : halvesMatch (chunk.map SignedBits.bits) = true) (hlen : chunk.length ≤ 2 ^ 64)
    (hle : chunk.headD default ≤ chunk.getLastD default) : IsKeyRun chunk := by
  have hw : 0 < 128 := by decide
  let laneKey := signedLaneKey 128 hw
  apply isKeyRun_of_isRun laneKey.rank laneKey.le_iff hne
  have hmap : chunk.map laneKey.rank =
      (chunk.map SignedBits.bits).map (· + BitVec.ofNat 128 (2 ^ 127)) := by
    simp only [List.map_map]; rfl
  have hne' : chunk.map laneKey.rank ≠ [] := by simpa using hne
  apply isRun_of_halvesMatch hne' _ (by simpa using hlen)
  · rw [headD_map_of_ne_nil hne _ 0, getLastD_map_of_ne_nil hne _ 0]
    exact (laneKey.le_iff _ _).mp hle
  · rw [hmap, halvesMatch_map_signShift]; exact hmatch

/-- The `SimdKey` for `u128` and `Ipv6Addr`, with `lanes` values per chunk (shipped: 4). The chunk
test is `halvesMatch` plus `first <= last`; `sub_one` is `- 1`. -/
def u128SimdKey (lanes : Nat) (hpos : 0 < lanes) (hlanes : lanes ≤ 2 ^ 64) :
    SimdKey (BitVec 128) where
  lanes := lanes
  pred x := x - 1
  pred_spec := (unsignedLaneKey 128).pred_spec
  chunkCheck chunk := halvesMatch chunk && decide (chunk.headD default ≤ chunk.getLastD default)
  blockLanesMatch chunks block :=
    halvesChunksMatch lanes (highHalf (block.headD 0)) (lowHalf (block.headD 0)) chunks block
  chunkCheck_sound chunk hlen hcheck := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
    have hne : chunk ≠ [] := by rintro rfl; simp at hlen; omega
    exact isKeyRun_of_halvesMatch hne hcheck.1 (by omega) hcheck.2

/-- The unrolled loop is sound for `u128` and `Ipv6Addr` whenever a block holds at most `2^64`
values. -/
theorem u128_blockSound {lanes chunks : Nat} (hpos : 0 < lanes) (hlanes : lanes ≤ 2 ^ 64)
    (hchunks : 0 < chunks) (hblock : chunks * lanes ≤ 2 ^ 64) :
    (u128SimdKey lanes hpos hlanes).BlockSound chunks := by
  intro previousEnd block hlen hcheck
  change block.length = chunks * lanes at hlen
  simp only [SimdKey.blockContinues, u128SimdKey, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hcheck
  obtain ⟨-, hle, hmatch⟩ := hcheck
  have hpos' : 0 < chunks * lanes := Nat.mul_pos hchunks hpos
  have hne : block ≠ [] := by rintro rfl; simp at hlen; omega
  exact isKeyRun_of_halvesMatch hne
    ((halvesChunksMatch_headD_iff lanes chunks hpos' block hlen).mp hmatch) (by omega) hle

/-- The `SimdKey` for `i128`, with `lanes` values per chunk (shipped: 4). The lane test runs on the
raw two's-complement bits; the order is signed; `sub_one` is `- 1`. -/
def i128SimdKey (lanes : Nat) (hpos : 0 < lanes) (hlanes : lanes ≤ 2 ^ 64) :
    SimdKey (SignedBits 128) where
  lanes := lanes
  pred := (signedLaneKey 128 (by decide)).pred
  pred_spec := (signedLaneKey 128 (by decide)).pred_spec
  chunkCheck chunk := halvesMatch (chunk.map SignedBits.bits) &&
    decide (chunk.headD default ≤ chunk.getLastD default)
  blockLanesMatch chunks block :=
    halvesChunksMatch lanes (highHalf (block.headD default).bits)
      (lowHalf (block.headD default).bits) chunks (block.map SignedBits.bits)
  chunkCheck_sound chunk hlen hcheck := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
    have hne : chunk ≠ [] := by rintro rfl; simp at hlen; omega
    exact isKeyRun_of_signed_halvesMatch hne hcheck.1 (by omega) hcheck.2

/-- The unrolled loop is sound for `i128` whenever a block holds at most `2^64` values. -/
theorem i128_blockSound {lanes chunks : Nat} (hpos : 0 < lanes) (hlanes : lanes ≤ 2 ^ 64)
    (hchunks : 0 < chunks) (hblock : chunks * lanes ≤ 2 ^ 64) :
    (i128SimdKey lanes hpos hlanes).BlockSound chunks := by
  intro previousEnd block hlen hcheck
  change block.length = chunks * lanes at hlen
  simp only [SimdKey.blockContinues, i128SimdKey, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hcheck
  obtain ⟨-, hle, hmatch⟩ := hcheck
  have hpos' : 0 < chunks * lanes := Nat.mul_pos hchunks hpos
  have hne : block ≠ [] := by rintro rfl; simp at hlen; omega
  have hmlen : (block.map SignedBits.bits).length = chunks * lanes := by simpa using hlen
  have hhead : (block.map SignedBits.bits).headD 0 = (block.headD default).bits := by
    rw [headD_map_of_ne_nil hne _ 0]
  rw [← hhead] at hmatch
  exact isKeyRun_of_signed_halvesMatch hne
    ((halvesChunksMatch_headD_iff lanes chunks hpos' _ hmlen).mp hmatch) (by omega) hle

/-- **The kernel is correct for `u128` and `Ipv6Addr`** for any chunk width and unroll factor whose
block holds at most `2^64` values. -/
theorem u128_kernel_correct (lanes chunks : Nat) (hpos : 0 < lanes) (hlanes : lanes ≤ 2 ^ 64)
    (hchunks : 0 < chunks) (hblock : chunks * lanes ≤ 2 ^ 64) (values : List (BitVec 128)) :
    keyRangeSet ((u128SimdKey lanes hpos hlanes).kernelRanges chunks values) = keySet values ∧
      KeyRangesNonempty ((u128SimdKey lanes hpos hlanes).kernelRanges chunks values) :=
  SimdKey.kernelRanges_correct _ (Or.inr (u128_blockSound hpos hlanes hchunks hblock)) values

/-- **The kernel is correct for `i128`** for any chunk width and unroll factor whose block holds at
most `2^64` values. -/
theorem i128_kernel_correct (lanes chunks : Nat) (hpos : 0 < lanes) (hlanes : lanes ≤ 2 ^ 64)
    (hchunks : 0 < chunks) (hblock : chunks * lanes ≤ 2 ^ 64) (values : List (SignedBits 128)) :
    keyRangeSet ((i128SimdKey lanes hpos hlanes).kernelRanges chunks values) = keySet values ∧
      KeyRangesNonempty ((i128SimdKey lanes hpos hlanes).kernelRanges chunks values) :=
  SimdKey.kernelRanges_correct _ (Or.inr (i128_blockSound hpos hlanes hchunks hblock)) values

/-- **The shipped kernel is correct for every 128-bit key type**: `u128`, `Ipv6Addr`, and `i128`
all use two `u64` lanes per value, so a `u64x8` vector holds 4 values, with unroll factor 4. -/
theorem shipped_128bit_kernel_correct :
    (∀ values, let k := u128SimdKey 4 (by decide) (by decide)
      keyRangeSet (k.kernelRanges 4 values) = keySet values ∧
        KeyRangesNonempty (k.kernelRanges 4 values)) ∧
    (∀ values, let k := i128SimdKey 4 (by decide) (by decide)
      keyRangeSet (k.kernelRanges 4 values) = keySet values ∧
        KeyRangesNonempty (k.kernelRanges 4 values)) :=
  ⟨u128_kernel_correct 4 4 (by decide) (by decide) (by decide) (by decide),
   i128_kernel_correct 4 4 (by decide) (by decide) (by decide) (by decide)⟩

end SimdRunCheck
