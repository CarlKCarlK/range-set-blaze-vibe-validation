import RangeSetBlaze.SimdKernel

/-!
# The kernel's key types

Each Rust key type that `from_slice` accelerates gets a `SimdKey`, so `SimdKey.kernelRanges_correct`
applies to it. Most key types share one recipe, `LaneKey`: each key maps to a `w`-bit lane, and
keys are ordered like their lanes after adding a fixed `shift`. The shift is `0` for unsigned
integers, `char`, and `Ipv4Addr`, and `2^(w-1)` for signed integers, where adding it turns signed
order into unsigned order. `LaneKey.toSimdKey` proves the chunk and block tests sound once, from
the lane theorems in `SimdRunCheck`.
-/

namespace SimdRunCheck

variable {w : Nat}

/-- Unsigned order on lanes, built from Lean's own `≤` and `<` on `BitVec` so the two agree. -/
instance : LinearOrder (BitVec w) where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl x := by simp
  le_trans _ _ _ := by simp only [BitVec.le_def]; omega
  le_antisymm x y h1 h2 := BitVec.eq_of_toNat_eq (by rw [BitVec.le_def] at h1 h2; omega)
  le_total x y := by simp only [BitVec.le_def]; omega
  lt_iff_le_not_ge x y := by simp only [BitVec.le_def, BitVec.lt_def]; omega
  toDecidableLE := fun _ _ => inferInstance

theorem default_bitVec : (default : BitVec w) = 0 := rfl

/-! ## Moving lists of keys to lanes -/

theorem headD_map_of_ne_nil {α β : Type} [Inhabited α] {l : List α} (hne : l ≠ []) (f : α → β)
    (b : β) : (l.map f).headD b = f (l.headD default) := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne; rfl

theorem getLastD_map_of_ne_nil {α β : Type} [Inhabited α] {l : List α} (hne : l ≠ []) (f : α → β)
    (b : β) : (l.map f).getLastD b = f (l.getLastD default) := by
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_map,
    List.getLast?_eq_some_getLast hne]; rfl

/-- Adding the same constant to every lane does not change whether the lanes form a wrapping run. -/
theorem lanesMatch_map_add (chunk : List (BitVec w)) (shift : BitVec w) :
    lanesMatch (chunk.map (· + shift)) = lanesMatch chunk := by
  by_cases hnil : chunk = []
  · subst hnil; rfl
  have hne := hnil
  apply Bool.eq_iff_iff.mpr
  rw [lanesMatch_iff, lanesMatch_iff, headD_map_of_ne_nil hne, List.length_map]
  have hshift : wrappingRun (chunk.headD default + shift) chunk.length =
      (wrappingRun (chunk.headD default) chunk.length).map (· + shift) := by
    simp only [wrappingRun, List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp]
    ac_rfl
  rw [hshift, default_bitVec]
  have hcancel : ((· - shift) ∘ (· + shift) : BitVec w → BitVec w) = id := by
    funext x; simp [BitVec.add_sub_cancel]
  constructor
  · intro h
    have := congrArg (List.map (· - shift)) h
    simpa [List.map_map, hcancel] using this
  · intro h; exact congrArg (List.map (· + shift)) h

/-- If the lanes of a chunk, read through an order embedding, are a real run, then the chunk is
a run of keys. -/
theorem isKeyRun_of_isRun {K : Type} [LinearOrder K] [Inhabited K] (rank : K → BitVec w)
    (hrank : ∀ a b, a ≤ b ↔ rank a ≤ rank b) {chunk : List K} (hne : chunk ≠ [])
    (hrun : IsRun (chunk.map rank)) : IsKeyRun chunk := by
  have hneLanes : chunk.map rank ≠ [] := by simpa using hne
  obtain ⟨hvalues, -⟩ := valueSet_of_isRun hrun hneLanes
  rw [headD_map_of_ne_nil hne, getLastD_map_of_ne_nil hne] at hvalues
  have hinj : Function.Injective rank := fun a b h =>
    le_antisymm ((hrank a b).mpr (le_of_eq h)) ((hrank b a).mpr (le_of_eq h.symm))
  refine ⟨hne, fun k => ?_⟩
  have hmem : (rank k).toNat ∈ valueSet (chunk.map rank) ↔ k ∈ chunk := by
    simp only [valueSet, List.mem_map, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨v, ⟨c, hc, rfl⟩, hv⟩
      rwa [hinj (BitVec.eq_of_toNat_eq hv)] at hc
    · intro hk; exact ⟨rank k, ⟨k, hk, rfl⟩, rfl⟩
  rw [← hmem, hvalues, Set.mem_Icc, hrank, hrank, BitVec.le_def, BitVec.le_def]

/-! ## The recipe -/

/-- A key type whose keys map to `w`-bit lanes, ordered like their lanes after adding `shift`. -/
structure LaneKey (K : Type) [LinearOrder K] [Inhabited K] (w : Nat) where
  /-- The lane value of a key: what Rust's `SimdInteger::load` and `splat` produce. -/
  lane : K → BitVec w
  /-- Added to a lane to get a value whose unsigned order is the keys' order. -/
  shift : BitVec w
  le_iff : ∀ a b : K, a ≤ b ↔ lane a + shift ≤ lane b + shift
  /-- Rust's `sub_one` for this key type. -/
  pred : K → K
  pred_spec : ∀ x y : K, y < x → pred x = y → ∀ k, y < k ↔ x ≤ k

variable {K : Type} [LinearOrder K] [Inhabited K]

/-- The order-preserving value of a key's lane: its unsigned order is the keys' order. -/
def LaneKey.rank (laneKey : LaneKey K w) (k : K) : BitVec w :=
  laneKey.lane k + laneKey.shift

/-- **The heart of soundness for every lane-based key type.** If a nonempty list of at most `2^w`
keys has lanes that form a wrapping run, and its first key is at most its last, then it is a run
of keys. This reduces to `isRun_of_chunkCheck` on the keys' ranks. -/
theorem LaneKey.isKeyRun_of_lanes (laneKey : LaneKey K w) {chunk : List K} (hne : chunk ≠ [])
    (hlanes : lanesMatch (chunk.map laneKey.lane) = true)
    (hle : chunk.headD default ≤ chunk.getLastD default) (hlen : chunk.length ≤ 2 ^ w) :
    IsKeyRun chunk := by
  apply isKeyRun_of_isRun laneKey.rank laneKey.le_iff hne
  apply isRun_of_chunkCheck _ (by simpa using hlen)
  have hmap : chunk.map laneKey.rank = (chunk.map laneKey.lane).map (· + laneKey.shift) := by
    simp only [List.map_map]; rfl
  simp only [chunkCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by rw [hmap, lanesMatch_map_add]; exact hlanes, ?_⟩
  rw [headD_map_of_ne_nil hne, getLastD_map_of_ne_nil hne]
  exact (laneKey.le_iff _ _).mp hle

/-- The `SimdKey` for a `LaneKey`, with `lanes` keys per chunk. The chunk test is Rust's
`is_consecutive_with_offsets`: the lanes form a wrapping run, and the first key is at most the
last. The block comparison steps chunk by chunk, as `block_continues` does. -/
def LaneKey.toSimdKey (laneKey : LaneKey K w) (lanes : Nat) (hpos : 0 < lanes)
    (hlanes : lanes ≤ 2 ^ w) : SimdKey K where
  lanes := lanes
  pred := laneKey.pred
  pred_spec := laneKey.pred_spec
  chunkCheck chunk := lanesMatch (chunk.map laneKey.lane) &&
    decide (chunk.headD default ≤ chunk.getLastD default)
  blockLanesMatch chunks block :=
    chunksMatch lanes (laneKey.lane (block.headD default)) chunks (block.map laneKey.lane)
  chunkCheck_sound chunk hlen hcheck := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
    have hne : chunk ≠ [] := by rintro rfl; simp at hlen; omega
    exact laneKey.isKeyRun_of_lanes hne hcheck.1 hcheck.2 (by omega)

/-- **The unrolled loop is sound** for a lane-based key type whenever a block holds at most `2^w`
keys. Every shipped configuration qualifies. -/
theorem LaneKey.blockSound (laneKey : LaneKey K w) {lanes chunks : Nat} (hpos : 0 < lanes)
    (hlanes : lanes ≤ 2 ^ w) (hchunks : 0 < chunks) (hblock : chunks * lanes ≤ 2 ^ w) :
    (laneKey.toSimdKey lanes hpos hlanes).BlockSound chunks := by
  intro previousEnd block hlen hcheck
  change block.length = chunks * lanes at hlen
  simp only [SimdKey.blockContinues, LaneKey.toSimdKey, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hcheck
  obtain ⟨-, hle, hmatch⟩ := hcheck
  have hpos' : 0 < chunks * lanes := Nat.mul_pos hchunks hpos
  have hne : block ≠ [] := by rintro rfl; simp at hlen; omega
  have hlanesMatch : lanesMatch (block.map laneKey.lane) = true := by
    rw [chunksMatch_iff _ _ _ _ (by simpa using hlen)] at hmatch
    rw [lanesMatch_iff, headD_map_of_ne_nil hne, List.length_map, hlen]
    exact hmatch
  exact laneKey.isKeyRun_of_lanes hne hlanesMatch hle (by omega)

end SimdRunCheck
