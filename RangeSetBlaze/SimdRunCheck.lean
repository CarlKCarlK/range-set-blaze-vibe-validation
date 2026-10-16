import Mathlib.Tactic.Linarith

/-!
# SIMD run checks and lane wraparound

`RangeSetBlaze::from_slice` scans a slice for runs of consecutive integers with SIMD.
A *chunk* of `L` values fills one vector, and lane `i` is compared against `first + i`,
where `first` is the chunk's first value. Vector arithmetic wraps, so this lane test
alone also accepts chunks that wrap past the type's maximum, such as the `u8` chunk
`[254, 255, 0, 1, …]`.

Lanes are modeled as `BitVec w`, whose `+` wraps exactly like a `w`-bit SIMD lane.

* **Part A** (this section) records the wraparound counterexamples: the original chunk bug,
  and an unrolled-block bug for unroll factors that production does not use.
* **Part B** proves that the checks the shipped kernel uses are sound.
-/

namespace SimdRunCheck

variable {w : Nat}

/-- The `len` lane values of a wrapping run that starts at `first`: lane `i` holds `first + i`
in `w`-bit wrapping arithmetic. The SIMD kernel compares a chunk against this vector. -/
def wrappingRun (first : BitVec w) (len : Nat) : List (BitVec w) :=
  (List.range len).map fun i => first + BitVec.ofNat w i

/-- The SIMD lane test: the chunk equals the wrapping run that starts at its first value.
In the Rust kernel this is `(values - offsets).simd_eq(splat(first)).all_true()`. -/
def lanesMatch (chunk : List (BitVec w)) : Bool :=
  chunk == wrappingRun (chunk.headD 0) chunk.length

/-- The chunk really is a run of consecutive unsigned integers: read as natural numbers, its
values are `first, first + 1, …`, so no lane wrapped. -/
def IsRun (chunk : List (BitVec w)) : Prop :=
  chunk.map BitVec.toNat = List.range' (chunk.headD 0).toNat chunk.length

instance (chunk : List (BitVec w)) : Decidable (IsRun chunk) := by
  unfold IsRun; infer_instance

/-- The lane test as the Rust kernel writes it: subtract each lane's offset `i`, then compare every
lane with the first value (`(values - offsets).simd_eq(splat(first)).all_true()`).
`kernelLanesMatch_eq_lanesMatch` shows it is `lanesMatch`. -/
def kernelLanesMatch (chunk : List (BitVec w)) : Bool :=
  chunk.mapIdx (fun i value => value - BitVec.ofNat w i) ==
    List.replicate chunk.length (chunk.headD 0)

/-- Subtracting the offsets and comparing with the first value is the same as comparing with the
wrapping run: `value - i = first` exactly when `value = first + i`. -/
theorem kernelLanesMatch_eq_lanesMatch (chunk : List (BitVec w)) :
    kernelLanesMatch chunk = lanesMatch chunk := by
  simp only [kernelLanesMatch, lanesMatch, wrappingRun]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, List.ext_getElem_iff, List.length_mapIdx, List.length_replicate,
    List.length_map, List.length_range, true_and, List.getElem_mapIdx, List.getElem_replicate,
    List.getElem_map, List.getElem_range]
  refine forall_congr' fun i => forall_congr' fun _ => forall_congr' fun _ => ?_
  constructor
  · intro h; rw [← h, BitVec.sub_add_cancel]
  · intro h; rw [h, BitVec.add_sub_cancel]

/-- The check before the wraparound fix: the lane test alone. -/
def originalCheck (chunk : List (BitVec w)) : Bool :=
  lanesMatch chunk

/-- The fixed chunk check: the lane test, plus the chunk's first value is at most its last.
A run that wraps ends below where it starts, so the extra comparison rejects it. -/
def chunkCheck (chunk : List (BitVec w)) : Bool :=
  lanesMatch chunk && decide (chunk.headD 0 ≤ chunk.getLastD 0)

/-- The unrolled block check. The block must continue the run that ended at `previousEnd`
(Rust: `next[0] > end && next[0].sub_one() == end`), and the whole block, `N` chunks of `L`
lanes, must pass the fixed chunk check. The kernel compares the block chunk by chunk, stepping
the expected vector by `L` each time, but checks `first ≤ last` only once for the whole block. -/
def blockCheck (previousEnd : BitVec w) (block : List (BitVec w)) : Bool :=
  decide (previousEnd < block.headD 0) && block.headD 0 - 1 == previousEnd && chunkCheck block

/-! ## Part A: counterexamples -/

/-- **The original bug.** The 16-lane `u8` chunk `[254, 255, 0, 1, …, 13]` passes the lane test,
but it is not a run. -/
theorem originalCheck_accepts_wrapped_chunk :
    originalCheck (wrappingRun (254 : BitVec 8) 16) = true ∧
      ¬IsRun (wrappingRun (254 : BitVec 8) 16) := by
  decide

/-- **Every counterexample to the original check**, for 16 `u8` lanes. Any chunk that passes
the lane test is a wrapping run, so ranging over its first value covers them all: the check
is wrong exactly for the chunks that start above `256 - 16 = 240`. -/
theorem originalCheck_wrong_iff :
    ∀ first : BitVec 8,
      (originalCheck (wrappingRun first 16) = true ∧ ¬IsRun (wrappingRun first 16)) ↔
        240 < first.toNat := by
  decide

/-- The fix repairs the 16-lane `u8` case: the fixed check accepts no wrapped chunk. -/
theorem chunkCheck_rejects_wrapped_chunks :
    ∀ first : BitVec 8,
      chunkCheck (wrappingRun first 16) = true → IsRun (wrappingRun first 16) := by
  decide

/-- **The unrolled-block bug.** With `u8` (64 lanes) and an unroll factor of 5, a block holds
320 values, more than the 256 a `u8` can take. A run that ends at 63, continued by a block that
wraps all the way around, passes every part of the block check, but the block is not a run.

The real kernel shows the same failure: with unroll factor 5, `from_slice` on the 384 `u8`
values `0, 1, …, 255, 0, 1, …, 127` returns `0..=127` instead of `0..=255`. Production uses
unroll factor 4 (256 values per `u8` block), which Part B proves safe. -/
theorem blockCheck_unroll_five_accepts_wrapped_block :
    blockCheck (63 : BitVec 8) (wrappingRun 64 320) = true ∧
      ¬IsRun (wrappingRun (64 : BitVec 8) 320) := by
  decide +kernel

/-! ## Part B: the shipped checks are sound

The proofs read lanes as natural numbers. A wrapping run starting at `first` holds
`(first + i) % 2^w` in lane `i`; it is a real run exactly when it never reaches `2^w`.
-/

@[simp] theorem length_wrappingRun (first : BitVec w) (len : Nat) :
    (wrappingRun first len).length = len := by
  simp [wrappingRun]

theorem headD_wrappingRun (first : BitVec w) {len : Nat} (hlen : 0 < len) :
    (wrappingRun first len).headD 0 = first := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hlen
  simp [wrappingRun, List.range_succ_eq_map]

/-- The last lane of a nonempty wrapping run, as a natural number. -/
theorem toNat_getLastD_wrappingRun (first : BitVec w) (n : Nat) :
    ((wrappingRun first (n + 1)).getLastD 0).toNat = (first.toNat + n) % 2 ^ w := by
  simp [wrappingRun, List.range_succ, BitVec.toNat_add, BitVec.toNat_ofNat]

/-- A chunk passes the lane test exactly when it is the wrapping run that starts at its first
value. -/
theorem lanesMatch_iff (chunk : List (BitVec w)) :
    lanesMatch chunk = true ↔ chunk = wrappingRun (chunk.headD 0) chunk.length := by
  simp [lanesMatch]

/-- **A wrapping run is a real run exactly when it does not pass the top**: `first + len ≤ 2^w`. -/
theorem isRun_wrappingRun_iff (first : BitVec w) (len : Nat) :
    IsRun (wrappingRun first len) ↔ first.toNat + len ≤ 2 ^ w ∨ len = 0 := by
  rcases Nat.eq_zero_or_pos len with rfl | hlen
  · simp [IsRun, wrappingRun]
  have hlanes : (wrappingRun first len).map BitVec.toNat =
      (List.range len).map fun i => (first.toNat + i) % 2 ^ w := by
    simp [wrappingRun, BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [IsRun, hlanes, headD_wrappingRun first hlen, length_wrappingRun,
    List.range'_eq_map_range, List.map_inj_left, List.mem_range]
  constructor
  · intro hall
    have hlast := hall (len - 1) (by omega)
    have := Nat.mod_lt (first.toNat + (len - 1)) (Nat.two_pow_pos w)
    left; omega
  · rintro (hfits | rfl) i hi
    · exact Nat.mod_eq_of_lt (by omega)
    · omega

/-- The arithmetic heart of the wraparound fix. Start at `first < M`, take `steps < M` more
steps modulo `M`, and land at or above `first`: then the steps never wrapped. -/
theorem no_wrap_of_le_mod {M first steps : Nat} (hfirst : first < M) (hsteps : steps < M)
    (hle : first ≤ (first + steps) % M) : first + steps < M := by
  by_contra hwrap
  have : (first + steps) % M = first + steps - M := by
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- What the fixed chunk check says about a chunk of `n + 1` values, read as natural numbers: the
chunk is the wrapping run from its first value, and the run's last value is at or above its first. -/
theorem chunkCheck_eq_true_iff {chunk : List (BitVec w)} {n : Nat} (hlen : chunk.length = n + 1) :
    chunkCheck chunk = true ↔ chunk = wrappingRun (chunk.headD 0) (n + 1) ∧
      (chunk.headD 0).toNat ≤ ((chunk.headD 0).toNat + n) % 2 ^ w := by
  simp only [chunkCheck, Bool.and_eq_true, decide_eq_true_eq, lanesMatch_iff, hlen, BitVec.le_def]
  constructor <;> rintro ⟨hrun, hle⟩ <;> refine ⟨hrun, ?_⟩
  · rwa [hrun, toNat_getLastD_wrappingRun, headD_wrappingRun _ (Nat.succ_pos n)] at hle
  · rwa [hrun, toNat_getLastD_wrappingRun, headD_wrappingRun _ (Nat.succ_pos n)]

/-- **The fixed chunk check is sound** for chunks of at most `2^w` lanes: it accepts only real
runs. Every SIMD chunk qualifies, since a vector never has more lanes than its lane type has
values. -/
theorem isRun_of_chunkCheck {chunk : List (BitVec w)} (hcheck : chunkCheck chunk = true)
    (hlen : chunk.length ≤ 2 ^ w) : IsRun chunk := by
  rcases hn : chunk.length with _ | n
  · rw [List.length_eq_zero_iff.mp hn]; simp [IsRun]
  obtain ⟨hrun, hle⟩ := (chunkCheck_eq_true_iff hn).mp hcheck
  rw [hrun, isRun_wrappingRun_iff]
  have := no_wrap_of_le_mod (BitVec.isLt _) (by omega) hle
  omega

/-- The literal `1` as a `w`-bit lane, when `w` is at least one bit. -/
theorem toNat_one (hw : 1 < 2 ^ w) : (1 : BitVec w).toNat = 1 := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]

/-- **Exactly when the unrolled block check is sound.** For blocks of `M` values that continue a
run, the block check accepts only real runs, for every such block, if and only if `M ≤ 2^w` or
`2^w` divides `M`.

* Production: `u8` lanes with 64 lanes and unroll factor 4 give `M = 256 = 2^8`, at the edge.
* Unroll factor 8 (`M = 512`) is sound only because `2^8 ∣ 512`: the block's last value is then
  one below its first, and the continuation precondition rules out a first value of `0`.
* Unroll factor 5 (`M = 320`) is not sound; see `blockCheck_unroll_five_accepts_wrapped_block`. -/
theorem blockCheck_sound_iff (M : Nat) :
    (∀ (previousEnd : BitVec w) (block : List (BitVec w)),
        block.length = M → blockCheck previousEnd block = true → IsRun block) ↔
      M ≤ 2 ^ w ∨ 2 ^ w ∣ M := by
  constructor
  · intro hsound
    by_contra hbad
    simp only [not_or, not_le] at hbad
    obtain ⟨hbig, hnotdvd⟩ := hbad
    have hw : 1 ≤ w := by
      rcases Nat.eq_zero_or_pos w with rfl | hw
      · simp at hnotdvd
      · exact hw
    have htwo : 2 ≤ 2 ^ w := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
    have hone := toNat_one (w := w) (by omega)
    obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
    -- The counterexample: a run ending at `0`, continued by the wrapping run starting at `1`.
    have hhead := headD_wrappingRun (1 : BitVec w) (Nat.succ_pos n)
    have hmod : (1 + n) % 2 ^ w ≠ 0 := fun h =>
      hnotdvd (Nat.dvd_of_mod_eq_zero (by rwa [Nat.add_comm] at h))
    have hlanes : lanesMatch (wrappingRun (1 : BitVec w) (n + 1)) = true := by
      rw [lanesMatch_iff, hhead, length_wrappingRun]
    have hcheck : blockCheck 0 (wrappingRun (1 : BitVec w) (n + 1)) = true := by
      simp only [blockCheck, chunkCheck, hlanes, hhead, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq, BitVec.lt_def, BitVec.le_def, hone, toNat_getLastD_wrappingRun]
      exact ⟨⟨by simp, by simp⟩, trivial, Nat.pos_of_ne_zero hmod⟩
    have hrun := hsound 0 _ (length_wrappingRun _ _) hcheck
    rw [isRun_wrappingRun_iff, hone] at hrun
    omega
  · rintro hM previousEnd block rfl hcheck
    simp only [blockCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    obtain ⟨⟨hafter, -⟩, hchunk⟩ := hcheck
    rcases hM with hsmall | hdvd
    · exact isRun_of_chunkCheck hchunk hsmall
    -- `2^w ∣ M`: a block that long can't pass the check at all.
    exfalso
    rw [BitVec.lt_def] at hafter
    rcases hn : block.length with _ | n
    · rw [List.length_eq_zero_iff.mp hn] at hafter; simp at hafter
    obtain ⟨-, hle⟩ := (chunkCheck_eq_true_iff hn).mp hchunk
    rw [hn] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    -- `first + n = (first - 1) + k * 2^w`, so the last value is `first - 1`.
    have hfirst := (block.headD 0).isLt
    have : ((block.headD 0).toNat + n) % 2 ^ w = (block.headD 0).toNat - 1 := by
      rw [show (block.headD 0).toNat + n = ((block.headD 0).toNat - 1) + 2 ^ w * k by omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega

/-! ### The kernel compares a block chunk by chunk -/

/-- How the kernel compares a block of `chunks` chunks of `L` lanes: chunk `k` is compared against
`expected + k·L + lane offsets`, stepping the expected vector by `L` after each chunk (Rust:
`expected += lanes_splat`). -/
def chunksMatch (L : Nat) (expected : BitVec w) : Nat → List (BitVec w) → Bool
  | 0, _ => true
  | chunks + 1, block =>
      (block.take L == wrappingRun expected L) &&
        chunksMatch L (expected + BitVec.ofNat w L) chunks (block.drop L)

/-- A wrapping run splits into two shorter ones. -/
theorem wrappingRun_add (first : BitVec w) (m n : Nat) :
    wrappingRun first (m + n) = wrappingRun first m ++ wrappingRun (first + BitVec.ofNat w m) n := by
  simp only [wrappingRun, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Function.comp, BitVec.ofNat_add, BitVec.add_assoc]

/-- **Stepping chunk by chunk is the same as comparing against one wrapping run.** -/
theorem chunksMatch_iff (L : Nat) (expected : BitVec w) (chunks : Nat) (block : List (BitVec w))
    (hlen : block.length = chunks * L) :
    chunksMatch L expected chunks block = true ↔ block = wrappingRun expected (chunks * L) := by
  induction chunks generalizing expected block with
  | zero =>
    simp only [Nat.zero_mul, List.length_eq_zero_iff] at hlen
    simp [chunksMatch, hlen, wrappingRun]
  | succ chunks ih =>
    have hsplit := List.take_append_drop L block
    have htake : (block.take L).length = L := by
      simp [List.length_take, hlen, Nat.succ_mul]
    have hdrop : (block.drop L).length = chunks * L := by
      simp [List.length_drop, hlen, Nat.succ_mul]
    rw [Nat.succ_mul, Nat.add_comm (chunks * L) L, wrappingRun_add]
    simp only [chunksMatch, Bool.and_eq_true, beq_iff_eq, ih _ _ hdrop]
    constructor
    · rintro ⟨h1, h2⟩
      rw [← hsplit, h1, h2]
    · intro h
      rw [← hsplit] at h
      exact List.append_inj h (by simp [htake])

/-- The block check in the kernel's shape: the continuation test, `first ≤ last` once for the
whole block, and the chunk-by-chunk lane comparison. -/
def kernelBlockCheck (L chunks : Nat) (previousEnd : BitVec w) (block : List (BitVec w)) : Bool :=
  decide (previousEnd < block.headD 0) && block.headD 0 - 1 == previousEnd &&
    (decide (block.headD 0 ≤ block.getLastD 0) && chunksMatch L (block.headD 0) chunks block)

/-- The kernel's block check is the `blockCheck` that `blockCheck_sound_iff` characterizes. -/
theorem kernelBlockCheck_eq_blockCheck (L chunks : Nat) (previousEnd : BitVec w)
    (block : List (BitVec w)) (hlen : block.length = chunks * L) :
    kernelBlockCheck L chunks previousEnd block = blockCheck previousEnd block := by
  have hmatch := chunksMatch_iff L (block.headD 0) chunks block hlen
  rw [← hlen] at hmatch
  simp only [kernelBlockCheck, blockCheck, chunkCheck, lanesMatch]
  rw [Bool.and_comm (decide _) (chunksMatch _ _ _ _)]
  congr 2
  exact Bool.eq_iff_iff.mpr (by simpa using hmatch)

/-! ### A real run covers exactly the interval from its first value to its last -/

/-- The values of a list, read as natural numbers. -/
def valueSet (values : List (BitVec w)) : Set Nat :=
  {n | ∃ v ∈ values, v.toNat = n}

/-- **A real run covers exactly the interval from its first value to its last**, read as natural
numbers. -/
theorem valueSet_of_isRun {chunk : List (BitVec w)} (hrun : IsRun chunk) (hne : chunk ≠ []) :
    valueSet chunk = Set.Icc (chunk.headD 0).toNat (chunk.getLastD 0).toNat ∧
      (chunk.headD 0).toNat ≤ (chunk.getLastD 0).toNat := by
  have hlen : chunk.length ≠ 0 := by simpa using hne
  have hlast : (chunk.getLastD 0).toNat = (chunk.headD 0).toNat + chunk.length - 1 := by
    have := (List.getLastD_map (f := BitVec.toNat) (l := chunk) (a := 0)).symm
    rw [hrun] at this
    simpa [List.getLastD_eq_getLast?, List.getLast?_range', hlen] using this
  refine ⟨?_, by omega⟩
  ext n
  have hmem : n ∈ valueSet chunk ↔ n ∈ chunk.map BitVec.toNat := by
    simp [valueSet, List.mem_map]
  rw [hmem, hrun, List.mem_range'_1, Set.mem_Icc, hlast]
  omega

/-- Subtracting one from a positive lane does not wrap. -/
theorem toNat_sub_one {x : BitVec w} (hpos : 0 < x.toNat) : (x - 1).toNat = x.toNat - 1 := by
  have hlt := x.isLt
  rw [BitVec.toNat_sub, toNat_one (by omega),
    show 2 ^ w - 1 + x.toNat = (x.toNat - 1) + 2 ^ w by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-! The kernel built on these checks, generic over the key type, is in `SimdKernel.lean`; the key
types, with their correctness for the shipped configuration, are in `SimdKeys*.lean`. -/

end SimdRunCheck
