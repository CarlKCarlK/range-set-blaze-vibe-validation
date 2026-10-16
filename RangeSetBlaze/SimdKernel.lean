import RangeSetBlaze.SimdRunCheck
import Mathlib.Tactic.Order

/-!
# The SIMD run kernel, generic over the key type

Rust's `collect_ranges` in `from_slice.rs` is generic over `T: SimdInteger`: unsigned and signed
integers, `char`, `Ipv4Addr`, and the 128-bit types all run the same kernel. This module models it
the same way. `SimdKey K` collects what the kernel needs from a key type `K`: its order, `sub_one`,
the chunk test, and the block comparison, together with the facts that make them sound. The kernel
is proved correct once, with its meaning stated as sets of keys, and each key type supplies a
`SimdKey`.

Stating the meaning in key space, rather than lane space, matters for `char`: its `sub_one` skips
the surrogate gap, so the kernel rightly extends a run from `'\u{D7FF}'` to `'\u{E000}'`, which are
adjacent characters but not adjacent lane values.
-/

namespace SimdRunCheck

variable {K : Type} [LinearOrder K] [Inhabited K]

/-- A nonempty list of keys that is exactly the interval from its first key to its last: every
key in between is in the list. -/
def IsKeyRun (chunk : List K) : Prop :=
  chunk ≠ [] ∧ ∀ k, k ∈ chunk ↔ chunk.headD default ≤ k ∧ k ≤ chunk.getLastD default

/-- What the kernel needs from a key type, mirroring Rust's `T: SimdInteger`. -/
structure SimdKey (K : Type) [LinearOrder K] [Inhabited K] where
  /-- How many keys one SIMD chunk holds (Rust's `chunk_len`). -/
  lanes : Nat
  /-- Rust's `T::sub_one`. The kernel only relies on it for keys above some other key. -/
  pred : K → K
  /-- `pred` is the immediate predecessor: if `pred x = y` and `y < x`, nothing lies strictly
  between them. -/
  pred_spec : ∀ x y : K, y < x → pred x = y → ∀ k, y < k ↔ x ≤ k
  /-- Rust's `is_consecutive_with_offsets` on one chunk: the lane test plus `first ≤ last`. -/
  chunkCheck : List K → Bool
  /-- The kernel's lane comparison for a block of `chunks` chunks, chunk by chunk. -/
  blockLanesMatch : Nat → List K → Bool
  /-- The chunk test accepts only real runs. -/
  chunkCheck_sound : ∀ chunk, chunk.length = lanes → chunkCheck chunk = true → IsKeyRun chunk

variable (key : SimdKey K)

/-- Rust's `chunk_continues`: the chunk starts just after `previousEnd` and is a run. -/
def SimdKey.chunkContinues (previousEnd : K) (chunk : List K) : Bool :=
  decide (previousEnd < chunk.headD default) && key.pred (chunk.headD default) == previousEnd &&
    key.chunkCheck chunk

/-- Rust's `block_continues`: the block starts just after `previousEnd`, its first key is at most
its last, and its lanes match chunk by chunk. -/
def SimdKey.blockContinues (chunks : Nat) (previousEnd : K) (block : List K) : Bool :=
  decide (previousEnd < block.headD default) && key.pred (block.headD default) == previousEnd &&
    (decide (block.headD default ≤ block.getLastD default) && key.blockLanesMatch chunks block)

/-- The unrolled loop is sound for `chunks` chunks per block: every block it accepts is a run. -/
def SimdKey.BlockSound (chunks : Nat) : Prop :=
  ∀ previousEnd block, block.length = chunks * key.lanes →
    key.blockContinues chunks previousEnd block = true → IsKeyRun block

/-! ## The kernel -/

/-- The keys a list of ranges covers. -/
def keyRangeSet (ranges : List (K × K)) : Set K :=
  {k | ∃ r ∈ ranges, r.1 ≤ k ∧ k ≤ r.2}

/-- The keys in a list. -/
def keySet (values : List K) : Set K :=
  {k | k ∈ values}

/-- Every range in the list is nonempty: its start is at most its stop. -/
def KeyRangesNonempty (ranges : List (K × K)) : Prop :=
  ∀ r ∈ ranges, r.1 ≤ r.2

/-- Rust's `RangeCollector::push`. Ranges are newest-first; the head is the range being extended.
The new range merges into it when it starts at or after it and touches or overlaps it. -/
def SimdKey.pushRange (ranges : List (K × K)) (start stop : K) : List (K × K) :=
  match ranges with
  | (currentStart, currentEnd) :: older =>
      if currentStart ≤ start ∧ (start ≤ currentEnd ∨ key.pred start = currentEnd) then
        (currentStart, if currentEnd < stop then stop else currentEnd) :: older
      else (start, stop) :: (currentStart, currentEnd) :: older
  | [] => [(start, stop)]

/-- Push each key as a one-key range. -/
def SimdKey.pushValues (ranges : List (K × K)) (values : List K) : List (K × K) :=
  values.foldl (fun ranges value => key.pushRange ranges value value) ranges

/-- Rust's single-chunk extension loop. Returns the run's new end and the keys not consumed. -/
def SimdKey.extendByChunks (stop : K) (rest : List K) : K × List K :=
  if 0 < key.lanes ∧ key.lanes ≤ rest.length then
    if key.chunkContinues stop (rest.take key.lanes) then
      SimdKey.extendByChunks ((rest.take key.lanes).getLastD default) (rest.drop key.lanes)
    else (stop, rest)
  else (stop, rest)
termination_by rest.length
decreasing_by simp; omega

/-- Rust's unrolled extension loop. -/
def SimdKey.extendByBlocks (chunks : Nat) (stop : K) (rest : List K) : K × List K :=
  if 0 < key.lanes ∧ 1 < chunks ∧ chunks * key.lanes ≤ rest.length then
    if key.blockContinues chunks stop (rest.take (chunks * key.lanes)) then
      SimdKey.extendByBlocks chunks ((rest.take (chunks * key.lanes)).getLastD default)
        (rest.drop (chunks * key.lanes))
    else (stop, rest)
  else (stop, rest)
termination_by rest.length
decreasing_by
  have : 0 < chunks * key.lanes := Nat.mul_pos (by omega) (by omega)
  simp; omega

theorem SimdKey.length_extendByChunks_le (stop : K) (rest : List K) :
    (key.extendByChunks stop rest).2.length ≤ rest.length := by
  fun_induction key.extendByChunks stop rest with
  | case1 => simp_all; omega
  | case2 | case3 => simp

theorem SimdKey.length_extendByBlocks_le (chunks : Nat) (stop : K) (rest : List K) :
    (key.extendByBlocks chunks stop rest).2.length ≤ rest.length := by
  fun_induction key.extendByBlocks chunks stop rest with
  | case1 => simp_all; omega
  | case2 | case3 => simp

/-- The kernel's main loop (`collect_ranges`). -/
def SimdKey.collectRanges (chunks : Nat) (ranges : List (K × K)) (rest : List K) : List (K × K) :=
  if 0 < key.lanes ∧ key.lanes ≤ rest.length then
    if key.chunkCheck (rest.take key.lanes) then
      let afterBlocks :=
        key.extendByBlocks chunks ((rest.take key.lanes).getLastD default) (rest.drop key.lanes)
      let afterChunks := key.extendByChunks afterBlocks.1 afterBlocks.2
      SimdKey.collectRanges chunks
        (key.pushRange ranges ((rest.take key.lanes).headD default) afterChunks.1) afterChunks.2
    else
      SimdKey.collectRanges chunks (key.pushValues ranges (rest.take key.lanes))
        (rest.drop key.lanes)
  else key.pushValues ranges rest
termination_by rest.length
decreasing_by
  · have h1 := key.length_extendByChunks_le
      (key.extendByBlocks chunks ((rest.take key.lanes).getLastD default) (rest.drop key.lanes)).1
      (key.extendByBlocks chunks ((rest.take key.lanes).getLastD default) (rest.drop key.lanes)).2
    have h2 := key.length_extendByBlocks_le chunks ((rest.take key.lanes).getLastD default)
      (rest.drop key.lanes)
    rw [List.length_drop] at h2
    omega
  · simp; omega

/-- The whole kernel, starting with no ranges. -/
def SimdKey.kernelRanges (chunks : Nat) (values : List K) : List (K × K) :=
  key.collectRanges chunks [] values

/-! ## Correctness -/

omit [LinearOrder K] [Inhabited K] in
@[simp] theorem keySet_nil : keySet ([] : List K) = ∅ := by simp [keySet]

omit [LinearOrder K] [Inhabited K] in
theorem keySet_append (a b : List K) : keySet (a ++ b) = keySet a ∪ keySet b := by
  ext k; simp [keySet]

omit [LinearOrder K] [Inhabited K] in
theorem keySet_cons (v : K) (values : List K) : keySet (v :: values) = {v} ∪ keySet values := by
  ext k; simp [keySet]

omit [Inhabited K] in
@[simp] theorem keyRangeSet_nil : keyRangeSet ([] : List (K × K)) = ∅ := by simp [keyRangeSet]

omit [Inhabited K] in
theorem mem_keyRangeSet_cons (k : K) (newest : K × K) (older : List (K × K)) :
    k ∈ keyRangeSet (newest :: older) ↔ (newest.1 ≤ k ∧ k ≤ newest.2) ∨ k ∈ keyRangeSet older := by
  simp [keyRangeSet]

/-- **Pushing a range adds exactly its interval**, whether it merges into the current range or not.
The merge case is where `pred_spec` matters: a range starting just after the current one (Rust:
`start.sub_one() == current_end`) leaves no gap. -/
theorem SimdKey.keyRangeSet_pushRange (ranges : List (K × K)) (start stop : K) :
    keyRangeSet (key.pushRange ranges start stop) = keyRangeSet ranges ∪ Set.Icc start stop := by
  cases ranges with
  | nil => ext k; simp [SimdKey.pushRange, keyRangeSet]
  | cons current older =>
    obtain ⟨currentStart, currentEnd⟩ := current
    by_cases hmerge : currentStart ≤ start ∧ (start ≤ currentEnd ∨ key.pred start = currentEnd)
    · simp only [SimdKey.pushRange, if_pos hmerge]
      obtain ⟨hstart, htouch⟩ := hmerge
      -- Nothing lies strictly between the current range's end and the new range's start.
      have hnear : ∀ k, currentEnd < k → start ≤ k := by
        rcases htouch with hle | hpred
        · intro k hk; order
        · intro k hk
          by_cases hlt : currentEnd < start
          · exact (key.pred_spec start currentEnd hlt hpred k).mp hk
          · order
      ext k
      simp only [Set.mem_union, Set.mem_Icc, mem_keyRangeSet_cons]
      by_cases hold : k ∈ keyRangeSet older
      · simp [hold]
      · simp only [hold, or_false]
        split_ifs with hlt
        · constructor
          · rintro ⟨h1, h2⟩
            by_cases hk : k ≤ currentEnd
            · exact Or.inl ⟨h1, hk⟩
            · exact Or.inr ⟨hnear k (lt_of_not_ge hk), h2⟩
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> order
        · constructor
          · rintro ⟨h1, h2⟩; exact Or.inl ⟨h1, h2⟩
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> order
    · simp only [SimdKey.pushRange, if_neg hmerge]
      ext k
      simp only [Set.mem_union, Set.mem_Icc, mem_keyRangeSet_cons]
      tauto

theorem SimdKey.keyRangeSet_pushValues (ranges : List (K × K)) (values : List K) :
    keyRangeSet (key.pushValues ranges values) = keyRangeSet ranges ∪ keySet values := by
  induction values generalizing ranges with
  | nil => simp [SimdKey.pushValues]
  | cons v values ih =>
    have hstep : key.pushValues ranges (v :: values) =
        key.pushValues (key.pushRange ranges v v) values := rfl
    rw [hstep, ih, key.keyRangeSet_pushRange, keySet_cons, Set.Icc_self, Set.union_assoc]

/-- A run's keys are the interval from its first key to its last. -/
theorem keySet_of_isKeyRun {chunk : List K} (hrun : IsKeyRun chunk) :
    keySet chunk = Set.Icc (chunk.headD default) (chunk.getLastD default) ∧
      chunk.headD default ≤ chunk.getLastD default := by
  obtain ⟨hne, hmem⟩ := hrun
  have hvalues : keySet chunk = Set.Icc (chunk.headD default) (chunk.getLastD default) := by
    ext k; simp only [keySet, Set.mem_ofPred_eq, Set.mem_Icc, hmem]
  refine ⟨hvalues, ?_⟩
  obtain ⟨first, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact ((hmem first).mp List.mem_cons_self).2

/-- **A run that continues a run ending at `stop`** holds exactly the keys just past `stop`, up
through its last key. -/
theorem SimdKey.keySet_of_continuation {stop : K} {block : List K} (hrun : IsKeyRun block)
    (hafter : stop < block.headD default) (hpred : key.pred (block.headD default) = stop) :
    keySet block = Set.Ioc stop (block.getLastD default) ∧ stop < block.getLastD default := by
  obtain ⟨hvalues, hle⟩ := keySet_of_isKeyRun hrun
  have hnext := key.pred_spec _ _ hafter hpred
  refine ⟨?_, by order⟩
  rw [hvalues]
  ext k
  simp only [Set.mem_Icc, Set.mem_Ioc, hnext]

/-- **What the single-chunk loop consumes**: exactly the keys just past the old end, up through
the new end. -/
theorem SimdKey.extendByChunks_spec (stop : K) (rest : List K) :
    ∃ consumed, rest = consumed ++ (key.extendByChunks stop rest).2 ∧
      stop ≤ (key.extendByChunks stop rest).1 ∧
      keySet consumed = Set.Ioc stop (key.extendByChunks stop rest).1 := by
  fun_induction key.extendByChunks stop rest with
  | case1 stop rest hlong hcheck ih =>
    obtain ⟨consumed, hrest, hle, hvalues⟩ := ih
    simp only [SimdKey.chunkContinues, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcheck
    obtain ⟨⟨hafter, hpred⟩, hchunk⟩ := hcheck
    have hrun := key.chunkCheck_sound _ (by simp; omega) hchunk
    obtain ⟨hnext, hlt⟩ := key.keySet_of_continuation hrun hafter hpred
    refine ⟨rest.take key.lanes ++ consumed, ?_, by order, ?_⟩
    · rw [List.append_assoc, ← hrest, List.take_append_drop]
    · rw [keySet_append, hnext, hvalues, Set.Ioc_union_Ioc_eq_Ioc hlt.le hle]
  | case2 | case3 => exact ⟨[], by simp, le_refl _, by simp⟩

/-- **What the unrolled loop consumes**, given that it is sound. -/
theorem SimdKey.extendByBlocks_spec {chunks : Nat} (hblock : chunks ≤ 1 ∨ key.BlockSound chunks)
    (stop : K) (rest : List K) :
    ∃ consumed, rest = consumed ++ (key.extendByBlocks chunks stop rest).2 ∧
      stop ≤ (key.extendByBlocks chunks stop rest).1 ∧
      keySet consumed = Set.Ioc stop (key.extendByBlocks chunks stop rest).1 := by
  fun_induction key.extendByBlocks chunks stop rest with
  | case1 stop rest hlong hcheck ih =>
    obtain ⟨consumed, hrest, hle, hvalues⟩ := ih
    have hsound : key.BlockSound chunks := by
      rcases hblock with h | h
      · omega
      · exact h
    have hrun := hsound stop _ (by simp; omega) hcheck
    simp only [SimdKey.blockContinues, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcheck
    obtain ⟨⟨hafter, hpred⟩, -⟩ := hcheck
    obtain ⟨hnext, hlt⟩ := key.keySet_of_continuation hrun hafter hpred
    refine ⟨rest.take (chunks * key.lanes) ++ consumed, ?_, by order, ?_⟩
    · rw [List.append_assoc, ← hrest, List.take_append_drop]
    · rw [keySet_append, hnext, hvalues, Set.Ioc_union_Ioc_eq_Ioc hlt.le hle]
  | case2 | case3 => exact ⟨[], by simp, le_refl _, by simp⟩

omit [Inhabited K] in
/-- A run's keys come in three consecutive pieces: the first chunk, the keys the unrolled loop
added, and those the single-chunk loop added. -/
theorem keyRun_pieces_union {first last blocksEnd stop : K} (others : Set K)
    (h1 : first ≤ last) (h2 : last ≤ blocksEnd) (h3 : blocksEnd ≤ stop) :
    Set.Icc first last ∪ (Set.Ioc last blocksEnd ∪ (Set.Ioc blocksEnd stop ∪ others)) =
      Set.Icc first stop ∪ others := by
  rw [← Set.union_assoc (Set.Ioc _ _), Set.Ioc_union_Ioc_eq_Ioc h2 h3, ← Set.union_assoc,
    Set.Icc_union_Ioc_eq_Icc h1 (le_trans h2 h3)]

/-- The ranges `collectRanges` adds cover exactly the keys it consumes. -/
theorem SimdKey.keyRangeSet_collectRanges {chunks : Nat}
    (hblock : chunks ≤ 1 ∨ key.BlockSound chunks) (ranges : List (K × K)) (rest : List K) :
    keyRangeSet (key.collectRanges chunks ranges rest) = keyRangeSet ranges ∪ keySet rest := by
  fun_induction key.collectRanges chunks ranges rest with
  | case1 ranges rest hlong hchunk afterBlocks afterChunks ih =>
    rw [ih, key.keyRangeSet_pushRange]
    have hrun := key.chunkCheck_sound _ (by simp; omega) hchunk
    obtain ⟨hchunkValues, hchunkLe⟩ := keySet_of_isKeyRun hrun
    obtain ⟨consumedBlocks, hrestBlocks, hleBlocks, hvaluesBlocks⟩ :=
      key.extendByBlocks_spec hblock ((rest.take key.lanes).getLastD default) (rest.drop key.lanes)
    obtain ⟨consumedChunks, hrestChunks, hleChunks, hvaluesChunks⟩ :=
      key.extendByChunks_spec afterBlocks.1 afterBlocks.2
    -- Restate the loop facts in terms of the kernel's `afterBlocks` and `afterChunks`.
    change rest.drop key.lanes = consumedBlocks ++ afterBlocks.2 at hrestBlocks
    change (rest.take key.lanes).getLastD default ≤ afterBlocks.1 at hleBlocks
    change keySet consumedBlocks =
      Set.Ioc ((rest.take key.lanes).getLastD default) afterBlocks.1 at hvaluesBlocks
    change afterBlocks.2 = consumedChunks ++ afterChunks.2 at hrestChunks
    change afterBlocks.1 ≤ afterChunks.1 at hleChunks
    change keySet consumedChunks = Set.Ioc afterBlocks.1 afterChunks.1 at hvaluesChunks
    have hrest : rest = rest.take key.lanes ++ (consumedBlocks ++ (consumedChunks ++ afterChunks.2)) := by
      rw [← hrestChunks, ← hrestBlocks, List.take_append_drop]
    conv_rhs => rw [hrest]
    rw [keySet_append, keySet_append, keySet_append, hchunkValues, hvaluesBlocks, hvaluesChunks,
      keyRun_pieces_union _ hchunkLe hleBlocks hleChunks, Set.union_assoc]
  | case2 ranges rest hlong hchunk ih =>
    rw [ih, key.keyRangeSet_pushValues, Set.union_assoc, ← keySet_append, List.take_append_drop]
  | case3 ranges rest hshort =>
    exact key.keyRangeSet_pushValues ranges rest

theorem SimdKey.nonempty_pushRange {ranges : List (K × K)} (hranges : KeyRangesNonempty ranges)
    {start stop : K} (hle : start ≤ stop) : KeyRangesNonempty (key.pushRange ranges start stop) := by
  cases ranges with
  | nil => simpa [KeyRangesNonempty, SimdKey.pushRange] using hle
  | cons current older =>
    obtain ⟨currentStart, currentEnd⟩ := current
    have hcurrent := hranges _ List.mem_cons_self
    by_cases hmerge : currentStart ≤ start ∧ (start ≤ currentEnd ∨ key.pred start = currentEnd)
    · simp only [SimdKey.pushRange, if_pos hmerge]
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · dsimp only at hcurrent ⊢
        split_ifs <;> order
      · exact hranges r (List.mem_cons_of_mem _ hr)
    · simp only [SimdKey.pushRange, if_neg hmerge]
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hle
      · exact hranges r hr

theorem SimdKey.nonempty_pushValues {ranges : List (K × K)} (hranges : KeyRangesNonempty ranges)
    (values : List K) : KeyRangesNonempty (key.pushValues ranges values) := by
  induction values generalizing ranges with
  | nil => exact hranges
  | cons v values ih => exact ih (key.nonempty_pushRange hranges (le_refl v))

/-- **The kernel never produces a backwards range.** `RangeCollector::push` and `UnionIter`, which
consume its ranges, assert this, and set equality alone cannot rule it out. -/
theorem SimdKey.nonempty_collectRanges {chunks : Nat} (hblock : chunks ≤ 1 ∨ key.BlockSound chunks)
    (ranges : List (K × K)) (rest : List K) :
    KeyRangesNonempty ranges → KeyRangesNonempty (key.collectRanges chunks ranges rest) := by
  fun_induction key.collectRanges chunks ranges rest with
  | case1 ranges rest hlong hchunk afterBlocks afterChunks ih =>
    intro hranges
    apply ih
    apply key.nonempty_pushRange hranges
    obtain ⟨-, hfirst⟩ := keySet_of_isKeyRun (key.chunkCheck_sound _ (by simp; omega) hchunk)
    obtain ⟨-, -, hleBlocks, -⟩ :=
      key.extendByBlocks_spec hblock ((rest.take key.lanes).getLastD default) (rest.drop key.lanes)
    obtain ⟨-, -, hleChunks, -⟩ := key.extendByChunks_spec afterBlocks.1 afterBlocks.2
    change (rest.take key.lanes).getLastD default ≤ afterBlocks.1 at hleBlocks
    change afterBlocks.1 ≤ afterChunks.1 at hleChunks
    order
  | case2 ranges rest hlong hchunk ih =>
    exact fun hranges => ih (key.nonempty_pushValues hranges _)
  | case3 ranges rest hshort =>
    exact fun hranges => key.nonempty_pushValues hranges rest

/-- **The kernel is correct, for any key type**: given a sound unrolled loop (or none), its ranges
cover exactly the input keys, and none is backwards. -/
theorem SimdKey.kernelRanges_correct {chunks : Nat} (hblock : chunks ≤ 1 ∨ key.BlockSound chunks)
    (values : List K) :
    keyRangeSet (key.kernelRanges chunks values) = keySet values ∧
      KeyRangesNonempty (key.kernelRanges chunks values) :=
  ⟨by simp [SimdKey.kernelRanges, key.keyRangeSet_collectRanges hblock],
    key.nonempty_collectRanges hblock [] values (by simp [KeyRangesNonempty])⟩

end SimdRunCheck
