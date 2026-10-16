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

/-! ## The kernel

A model of `collect_ranges` in `from_slice.rs`, following its loops and branches. Ranges are pairs
`(start, stop)`, kept newest-first: the head is the range `RangeCollector` is still extending. -/

/-- The integers a list of ranges covers, read as natural numbers. -/
def rangeSet (ranges : List (BitVec w × BitVec w)) : Set Nat :=
  {n | ∃ r ∈ ranges, r.1.toNat ≤ n ∧ n ≤ r.2.toNat}

/-- Rust's `RangeCollector::push`. The new range merges into the current one when it starts at or
after it and touches or overlaps it; otherwise it becomes the new current range. -/
def pushRange (ranges : List (BitVec w × BitVec w)) (start stop : BitVec w) :
    List (BitVec w × BitVec w) :=
  match ranges with
  | (currentStart, currentEnd) :: older =>
      if currentStart ≤ start ∧ (start ≤ currentEnd ∨ start - 1 = currentEnd) then
        (currentStart, if currentEnd < stop then stop else currentEnd) :: older
      else (start, stop) :: (currentStart, currentEnd) :: older
  | [] => [(start, stop)]

/-- Push each value as a one-value range (Rust: `for &value in chunk { ranges.push(value, value) }`). -/
def pushValues (ranges : List (BitVec w × BitVec w)) (values : List (BitVec w)) :
    List (BitVec w × BitVec w) :=
  values.foldl (fun ranges value => pushRange ranges value value) ranges

/-- Rust's single-chunk extension loop: while the next chunk continues the run, extend it. The
continuation test is `next[0] > end && next[0].sub_one() == end && is_consecutive(next)`, which is
`blockCheck` on one chunk. Returns the run's new end and the values not yet consumed. -/
def extendByChunks (L : Nat) (stop : BitVec w) (rest : List (BitVec w)) :
    BitVec w × List (BitVec w) :=
  if 0 < L ∧ L ≤ rest.length then
    if blockCheck stop (rest.take L) then
      extendByChunks L ((rest.take L).getLastD 0) (rest.drop L)
    else (stop, rest)
  else (stop, rest)
termination_by rest.length
decreasing_by simp; omega

/-- Rust's unrolled extension loop: while `chunks > 1` and a whole block of `chunks` chunks
continues the run, extend it by the block. -/
def extendByBlocks (L chunks : Nat) (stop : BitVec w) (rest : List (BitVec w)) :
    BitVec w × List (BitVec w) :=
  if 0 < L ∧ 1 < chunks ∧ chunks * L ≤ rest.length then
    if kernelBlockCheck L chunks stop (rest.take (chunks * L)) then
      extendByBlocks L chunks ((rest.take (chunks * L)).getLastD 0) (rest.drop (chunks * L))
    else (stop, rest)
  else (stop, rest)
termination_by rest.length
decreasing_by
  have : 0 < chunks * L := Nat.mul_pos (by omega) (by omega)
  simp; omega

theorem length_extendByChunks_le (L : Nat) (stop : BitVec w) (rest : List (BitVec w)) :
    (extendByChunks L stop rest).2.length ≤ rest.length := by
  fun_induction extendByChunks L stop rest with
  | case1 => simp_all; omega
  | case2 | case3 => simp

theorem length_extendByBlocks_le (L chunks : Nat) (stop : BitVec w) (rest : List (BitVec w)) :
    (extendByBlocks L chunks stop rest).2.length ≤ rest.length := by
  fun_induction extendByBlocks L chunks stop rest with
  | case1 => simp_all; omega
  | case2 | case3 => simp

/-- The kernel's main loop (`collect_ranges`): take a chunk; if it is a run, extend it by blocks
and then by chunks and push the whole run; otherwise push its values one by one. Push any
leftover values one by one at the end. -/
def collectRanges (L chunks : Nat) (ranges : List (BitVec w × BitVec w))
    (rest : List (BitVec w)) : List (BitVec w × BitVec w) :=
  if 0 < L ∧ L ≤ rest.length then
    if chunkCheck (rest.take L) then
      let afterBlocks := extendByBlocks L chunks ((rest.take L).getLastD 0) (rest.drop L)
      let afterChunks := extendByChunks L afterBlocks.1 afterBlocks.2
      collectRanges L chunks (pushRange ranges ((rest.take L).headD 0) afterChunks.1)
        afterChunks.2
    else collectRanges L chunks (pushValues ranges (rest.take L)) (rest.drop L)
  else pushValues ranges rest
termination_by rest.length
decreasing_by
  · have h1 := length_extendByChunks_le L (extendByBlocks L chunks ((rest.take L).getLastD 0)
      (rest.drop L)).1 (extendByBlocks L chunks ((rest.take L).getLastD 0) (rest.drop L)).2
    have h2 := length_extendByBlocks_le L chunks ((rest.take L).getLastD 0) (rest.drop L)
    rw [List.length_drop] at h2
    omega
  · simp; omega

/-! ### Correctness of the kernel -/

@[simp] theorem valueSet_nil : valueSet ([] : List (BitVec w)) = ∅ := by
  simp [valueSet]

theorem valueSet_append (a b : List (BitVec w)) :
    valueSet (a ++ b) = valueSet a ∪ valueSet b := by
  ext n; simp [valueSet, or_and_right, exists_or]

theorem valueSet_cons (v : BitVec w) (values : List (BitVec w)) :
    valueSet (v :: values) = {v.toNat} ∪ valueSet values := by
  ext n; simp [valueSet, eq_comm]

@[simp] theorem rangeSet_nil : rangeSet ([] : List (BitVec w × BitVec w)) = ∅ := by
  simp [rangeSet]

/-- Subtracting one from a positive lane does not wrap. -/
theorem toNat_sub_one {x : BitVec w} (hpos : 0 < x.toNat) : (x - 1).toNat = x.toNat - 1 := by
  have hlt := x.isLt
  rw [BitVec.toNat_sub, toNat_one (by omega),
    show 2 ^ w - 1 + x.toNat = (x.toNat - 1) + 2 ^ w by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- Membership in the ranges of a nonempty list, split into its newest range and the rest. -/
theorem mem_rangeSet_cons (n : Nat) (newest : BitVec w × BitVec w)
    (older : List (BitVec w × BitVec w)) :
    n ∈ rangeSet (newest :: older) ↔
      (newest.1.toNat ≤ n ∧ n ≤ newest.2.toNat) ∨ n ∈ rangeSet older := by
  simp [rangeSet]

/-- **Pushing a range adds exactly its interval**, whether it merges into the current range or not. -/
theorem rangeSet_pushRange (ranges : List (BitVec w × BitVec w)) (start stop : BitVec w) :
    rangeSet (pushRange ranges start stop) = rangeSet ranges ∪ Set.Icc start.toNat stop.toNat := by
  cases ranges with
  | nil => ext n; simp [pushRange, rangeSet]
  | cons current older =>
    obtain ⟨currentStart, currentEnd⟩ := current
    by_cases hmerge : currentStart ≤ start ∧ (start ≤ currentEnd ∨ start - 1 = currentEnd)
    · simp only [pushRange, if_pos hmerge]
      obtain ⟨hstart, htouch⟩ := hmerge
      rw [BitVec.le_def] at hstart
      -- The new range starts no later than one past the current range's end.
      have hnear : start.toNat ≤ currentEnd.toNat + 1 := by
        rcases htouch with hle' | hpred
        · rw [BitVec.le_def] at hle'; omega
        · by_cases hzero : start.toNat = 0
          · omega
          · have := toNat_sub_one (x := start) (by omega)
            rw [hpred] at this; omega
      have hend : (if currentEnd < stop then stop else currentEnd).toNat =
          max currentEnd.toNat stop.toNat := by
        by_cases hlt : currentEnd < stop
        · rw [if_pos hlt]; rw [BitVec.lt_def] at hlt; omega
        · rw [if_neg hlt]; rw [BitVec.lt_def] at hlt; omega
      ext n
      simp only [Set.mem_union, Set.mem_Icc, mem_rangeSet_cons, hend]
      by_cases hold : n ∈ rangeSet older
      · simp [hold]
      · simp only [hold, or_false]; omega
    · simp only [pushRange, if_neg hmerge]
      ext n
      simp only [Set.mem_union, Set.mem_Icc, mem_rangeSet_cons]
      tauto

theorem rangeSet_pushValues (ranges : List (BitVec w × BitVec w)) (values : List (BitVec w)) :
    rangeSet (pushValues ranges values) = rangeSet ranges ∪ valueSet values := by
  induction values generalizing ranges with
  | nil => simp [pushValues]
  | cons v values ih =>
    have hstep : pushValues ranges (v :: values) = pushValues (pushRange ranges v v) values := rfl
    rw [hstep, ih, rangeSet_pushRange, valueSet_cons, Set.Icc_self,
      Set.union_assoc]

/-- A block that continues a run ending at `stop` starts at `stop + 1`. -/
theorem toNat_headD_of_continues {stop : BitVec w} {next : List (BitVec w)}
    (hafter : stop < next.headD 0) (hpred : next.headD 0 - 1 = stop) :
    (next.headD 0).toNat = stop.toNat + 1 := by
  rw [BitVec.lt_def] at hafter
  have := toNat_sub_one (x := next.headD 0) (by omega)
  rw [hpred] at this
  omega

/-- **A block that continues a run, and is a real run,** holds exactly the values just past the
run's old end, up through the block's last value. Both extension loops consume such blocks. -/
theorem valueSet_of_continuation {stop : BitVec w} {block : List (BitVec w)}
    (hcheck : blockCheck stop block = true) (hrun : IsRun block) :
    valueSet block = Set.Ioc stop.toNat (block.getLastD 0).toNat ∧
      stop.toNat < (block.getLastD 0).toNat := by
  simp only [blockCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcheck
  obtain ⟨⟨hafter, hpred⟩, -⟩ := hcheck
  have hne : block ≠ [] := by rintro rfl; simp [BitVec.lt_def] at hafter
  obtain ⟨hvalues, hle⟩ := valueSet_of_isRun hrun hne
  have hhead := toNat_headD_of_continues hafter hpred
  refine ⟨?_, by omega⟩
  rw [hvalues, hhead]
  ext n; simp only [Set.mem_Icc, Set.mem_Ioc]; omega

/-- **What the single-chunk loop consumes**: exactly the values just past the old end, up through
the new end. -/
theorem extendByChunks_spec {L : Nat} (hlanes : L ≤ 2 ^ w) (stop : BitVec w)
    (rest : List (BitVec w)) :
    ∃ consumed, rest = consumed ++ (extendByChunks L stop rest).2 ∧
      stop.toNat ≤ (extendByChunks L stop rest).1.toNat ∧
      valueSet consumed = Set.Ioc stop.toNat (extendByChunks L stop rest).1.toNat := by
  fun_induction extendByChunks L stop rest with
  | case1 stop rest hlong hcheck ih =>
    obtain ⟨consumed, hrest, hle, hvalues⟩ := ih
    have hlen : (rest.take L).length = L := by simp; omega
    obtain ⟨hnext, hlt⟩ := valueSet_of_continuation hcheck
      ((blockCheck_sound_iff L).mpr (Or.inl hlanes) stop _ hlen hcheck)
    refine ⟨rest.take L ++ consumed, ?_, by omega, ?_⟩
    · rw [List.append_assoc, ← hrest, List.take_append_drop]
    · rw [valueSet_append, hnext, hvalues, Set.Ioc_union_Ioc_eq_Ioc hlt.le hle]
  | case2 | case3 => exact ⟨[], by simp, le_refl _, by simp⟩

/-- **What the unrolled loop consumes**, given the block condition from `blockCheck_sound_iff`. -/
theorem extendByBlocks_spec {L chunks : Nat}
    (hblock : chunks ≤ 1 ∨ chunks * L ≤ 2 ^ w ∨ 2 ^ w ∣ chunks * L) (stop : BitVec w)
    (rest : List (BitVec w)) :
    ∃ consumed, rest = consumed ++ (extendByBlocks L chunks stop rest).2 ∧
      stop.toNat ≤ (extendByBlocks L chunks stop rest).1.toNat ∧
      valueSet consumed = Set.Ioc stop.toNat (extendByBlocks L chunks stop rest).1.toNat := by
  fun_induction extendByBlocks L chunks stop rest with
  | case1 stop rest hlong hcheck ih =>
    obtain ⟨consumed, hrest, hle, hvalues⟩ := ih
    have hlen : (rest.take (chunks * L)).length = chunks * L := by simp; omega
    rw [kernelBlockCheck_eq_blockCheck L chunks stop _ hlen] at hcheck
    obtain ⟨hnext, hlt⟩ := valueSet_of_continuation hcheck
      ((blockCheck_sound_iff (chunks * L)).mpr (by omega) stop _ hlen hcheck)
    refine ⟨rest.take (chunks * L) ++ consumed, ?_, by omega, ?_⟩
    · rw [List.append_assoc, ← hrest, List.take_append_drop]
    · rw [valueSet_append, hnext, hvalues, Set.Ioc_union_Ioc_eq_Ioc hlt.le hle]
  | case2 | case3 => exact ⟨[], by simp, le_refl _, by simp⟩

/-- A run's values come in three consecutive pieces: the first chunk `[first, last]`, the values the
unrolled loop added `(last, end of blocks]`, and those the single-chunk loop added. -/
theorem run_pieces_union {first last blocksEnd stop : Nat} (others : Set Nat)
    (h1 : first ≤ last) (h2 : last ≤ blocksEnd) (h3 : blocksEnd ≤ stop) :
    Set.Icc first last ∪ (Set.Ioc last blocksEnd ∪ (Set.Ioc blocksEnd stop ∪ others)) =
      Set.Icc first stop ∪ others := by
  rw [← Set.union_assoc (Set.Ioc _ _), Set.Ioc_union_Ioc_eq_Ioc h2 h3, ← Set.union_assoc,
    Set.Icc_union_Ioc_eq_Icc h1 (le_trans h2 h3)]

/-- **The kernel is correct.** Given chunks of `L ≤ 2^w` lanes and the block condition of
`blockCheck_sound_iff`, the ranges `collectRanges` adds cover exactly the slice's values. SIMD may
miss a run (its values are then pushed one by one) but never invents one. -/
theorem rangeSet_collectRanges {L chunks : Nat} (hlanes : L ≤ 2 ^ w)
    (hblock : chunks ≤ 1 ∨ chunks * L ≤ 2 ^ w ∨ 2 ^ w ∣ chunks * L)
    (ranges : List (BitVec w × BitVec w)) (rest : List (BitVec w)) :
    rangeSet (collectRanges L chunks ranges rest) = rangeSet ranges ∪ valueSet rest := by
  fun_induction collectRanges L chunks ranges rest with
  | case1 ranges rest hlong hchunk afterBlocks afterChunks ih =>
    rw [ih]
    have hne : rest.take L ≠ [] := by
      simp only [ne_eq, List.take_eq_nil_iff, not_or]; constructor <;> grind
    have hrun := isRun_of_chunkCheck hchunk (by simp; omega)
    obtain ⟨hchunkValues, hchunkLe⟩ := valueSet_of_isRun hrun hne
    obtain ⟨consumedBlocks, hrestBlocks, hleBlocks, hvaluesBlocks⟩ :=
      extendByBlocks_spec hblock ((rest.take L).getLastD 0) (rest.drop L)
    obtain ⟨consumedChunks, hrestChunks, hleChunks, hvaluesChunks⟩ :=
      extendByChunks_spec hlanes afterBlocks.1 afterBlocks.2
    -- Restate the loop facts in terms of the kernel's `afterBlocks` and `afterChunks`.
    change rest.drop L = consumedBlocks ++ afterBlocks.2 at hrestBlocks
    change ((rest.take L).getLastD 0).toNat ≤ afterBlocks.1.toNat at hleBlocks
    change valueSet consumedBlocks =
      Set.Ioc ((rest.take L).getLastD 0).toNat afterBlocks.1.toNat at hvaluesBlocks
    change afterBlocks.2 = consumedChunks ++ afterChunks.2 at hrestChunks
    change afterBlocks.1.toNat ≤ afterChunks.1.toNat at hleChunks
    change valueSet consumedChunks = Set.Ioc afterBlocks.1.toNat afterChunks.1.toNat at hvaluesChunks
    have hrest : rest = rest.take L ++ (consumedBlocks ++ (consumedChunks ++ afterChunks.2)) := by
      rw [← hrestChunks, ← hrestBlocks, List.take_append_drop]
    rw [rangeSet_pushRange]
    conv_rhs => rw [hrest]
    -- The run is `[first, last] ∪ (last, end of blocks] ∪ (end of blocks, end of chunks]`.
    rw [valueSet_append, valueSet_append, valueSet_append, hchunkValues, hvaluesBlocks,
      hvaluesChunks, run_pieces_union _ hchunkLe hleBlocks hleChunks, Set.union_assoc]
  | case2 ranges rest hlong hchunk ih =>
    rw [ih, rangeSet_pushValues, Set.union_assoc, ← valueSet_append, List.take_append_drop]
  | case3 ranges rest hshort =>
    exact rangeSet_pushValues ranges rest

/-- The whole kernel, starting with no ranges. -/
def kernelRanges (L chunks : Nat) (values : List (BitVec w)) : List (BitVec w × BitVec w) :=
  collectRanges L chunks [] values

theorem rangeSet_kernelRanges {L chunks : Nat} (hlanes : L ≤ 2 ^ w)
    (hblock : chunks ≤ 1 ∨ chunks * L ≤ 2 ^ w ∨ 2 ^ w ∣ chunks * L) (values : List (BitVec w)) :
    rangeSet (kernelRanges L chunks values) = valueSet values := by
  simp [kernelRanges, rangeSet_collectRanges hlanes hblock]

/-! ### The kernel's ranges are never backwards

Covering the right values is not enough: `RangeCollector::push` and `UnionIter`, which consume the
kernel's ranges, assert that every range is nonempty (`start ≤ stop`). A backwards range covers
nothing, so `rangeSet_kernelRanges` alone cannot rule one out. -/

/-- Every range in the list is nonempty: its start is at most its stop. -/
def AllNonempty (ranges : List (BitVec w × BitVec w)) : Prop :=
  ∀ r ∈ ranges, r.1 ≤ r.2

theorem allNonempty_pushRange {ranges : List (BitVec w × BitVec w)} (hranges : AllNonempty ranges)
    {start stop : BitVec w} (hle : start ≤ stop) : AllNonempty (pushRange ranges start stop) := by
  cases ranges with
  | nil => simpa [AllNonempty, pushRange] using hle
  | cons current older =>
    obtain ⟨currentStart, currentEnd⟩ := current
    have hcurrent := hranges _ List.mem_cons_self
    have holder : AllNonempty older := fun r hr => hranges r (List.mem_cons_of_mem _ hr)
    by_cases hmerge : currentStart ≤ start ∧ (start ≤ currentEnd ∨ start - 1 = currentEnd)
    · simp only [pushRange, if_pos hmerge]
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · simp only [BitVec.le_def] at hcurrent ⊢
        by_cases hlt : currentEnd < stop
        · rw [if_pos hlt]; rw [BitVec.lt_def] at hlt; omega
        · rw [if_neg hlt]; exact hcurrent
      · exact holder r hr
    · simp only [pushRange, if_neg hmerge]
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hle
      · exact hranges r hr

theorem allNonempty_pushValues {ranges : List (BitVec w × BitVec w)}
    (hranges : AllNonempty ranges) (values : List (BitVec w)) :
    AllNonempty (pushValues ranges values) := by
  induction values generalizing ranges with
  | nil => exact hranges
  | cons v values ih =>
    exact ih (allNonempty_pushRange hranges (by rw [BitVec.le_def]))

/-- **The kernel never produces a backwards range**, under the same conditions as
`rangeSet_collectRanges`. -/
theorem allNonempty_collectRanges {L chunks : Nat} (hlanes : L ≤ 2 ^ w)
    (hblock : chunks ≤ 1 ∨ chunks * L ≤ 2 ^ w ∨ 2 ^ w ∣ chunks * L)
    (ranges : List (BitVec w × BitVec w)) (rest : List (BitVec w)) :
    AllNonempty ranges → AllNonempty (collectRanges L chunks ranges rest) := by
  fun_induction collectRanges L chunks ranges rest with
  | case1 ranges rest hlong hchunk afterBlocks afterChunks ih =>
    intro hranges
    apply ih
    apply allNonempty_pushRange hranges
    -- The run starts at the first chunk's first value and ends at or after that chunk's last.
    have hfirst : ((rest.take L).headD 0).toNat ≤ ((rest.take L).getLastD 0).toNat := by
      simp only [chunkCheck, Bool.and_eq_true, decide_eq_true_eq, BitVec.le_def] at hchunk
      exact hchunk.2
    obtain ⟨-, -, hleBlocks, -⟩ :=
      extendByBlocks_spec hblock ((rest.take L).getLastD 0) (rest.drop L)
    obtain ⟨-, -, hleChunks, -⟩ := extendByChunks_spec hlanes afterBlocks.1 afterBlocks.2
    change ((rest.take L).getLastD 0).toNat ≤ afterBlocks.1.toNat at hleBlocks
    change afterBlocks.1.toNat ≤ afterChunks.1.toNat at hleChunks
    rw [BitVec.le_def]
    omega
  | case2 ranges rest hlong hchunk ih =>
    exact fun hranges => ih (allNonempty_pushValues hranges _)
  | case3 ranges rest hshort =>
    exact fun hranges => allNonempty_pushValues hranges rest

theorem allNonempty_kernelRanges {L chunks : Nat} (hlanes : L ≤ 2 ^ w)
    (hblock : chunks ≤ 1 ∨ chunks * L ≤ 2 ^ w ∨ 2 ^ w ∣ chunks * L) (values : List (BitVec w)) :
    AllNonempty (kernelRanges L chunks values) :=
  allNonempty_collectRanges hlanes hblock [] values (by simp [AllNonempty])

/-- **The kernel is correct**: its ranges cover exactly the slice's values, and none is backwards. -/
theorem kernelRanges_correct {L chunks : Nat} (hlanes : L ≤ 2 ^ w)
    (hblock : chunks ≤ 1 ∨ chunks * L ≤ 2 ^ w ∨ 2 ^ w ∣ chunks * L) (values : List (BitVec w)) :
    rangeSet (kernelRanges L chunks values) = valueSet values ∧
      AllNonempty (kernelRanges L chunks values) :=
  ⟨rangeSet_kernelRanges hlanes hblock values, allNonempty_kernelRanges hlanes hblock values⟩

/-- **The shipped configuration is correct for unsigned lanes**: with 512-bit vectors (64 `u8`,
32 `u16`, 16 `u32`, or 8 `u64` lanes) and unroll factor 4, the kernel's ranges cover exactly the
slice's values, and none is backwards. This does not cover the other key types the
kernel also runs on: signed lanes (`i8` … `i64`, `isize`), which compare `first ≤ last` in signed
order; 128-bit keys, which span two lanes; and `char` and `Ipv4Addr`, which are converted lane by
lane. -/
theorem production_kernel_correct_unsigned :
    (∀ values : List (BitVec 8), rangeSet (kernelRanges 64 4 values) = valueSet values ∧
      AllNonempty (kernelRanges 64 4 values)) ∧
    (∀ values : List (BitVec 16), rangeSet (kernelRanges 32 4 values) = valueSet values ∧
      AllNonempty (kernelRanges 32 4 values)) ∧
    (∀ values : List (BitVec 32), rangeSet (kernelRanges 16 4 values) = valueSet values ∧
      AllNonempty (kernelRanges 16 4 values)) ∧
    (∀ values : List (BitVec 64), rangeSet (kernelRanges 8 4 values) = valueSet values ∧
      AllNonempty (kernelRanges 8 4 values)) :=
  ⟨kernelRanges_correct (by norm_num) (by norm_num),
    kernelRanges_correct (by norm_num) (by norm_num),
    kernelRanges_correct (by norm_num) (by norm_num),
    kernelRanges_correct (by norm_num) (by norm_num)⟩

end SimdRunCheck
