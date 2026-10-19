# SIMD run checks and lane wraparound

Date: 2026-10-16

## Starting state

Work started on branch `simd-run-check`, from `origin/main` at `36abdc5`, with a clean worktree.
The Rust code under study is `range-set-blaze` `src/from_slice.rs` on branch `fearless-simd`
(commit `cda982a4`, plus the follow-up `769630ad` described below).

`RangeSetBlaze::from_slice` scans a slice for runs of consecutive integers with SIMD. A chunk of
`L` values fills one vector, and lane `i` is compared against `first + i`, where `first` is the
chunk's first value. SIMD arithmetic wraps, so the lane test alone also accepts chunks that wrap
past the type's maximum. An earlier version had exactly this bug: the `u8` chunk
`[254, 255, 0, 1, …]` was read as a run. The fix adds `first ≤ last` to the check.

The kernel also has an unrolled loop that checks `N` chunks at once, a *block* of `N·L` values,
but compares `first ≤ last` only once for the whole block.

## Goal

Two parts:

* **A. The bug.** Model the lane test in Lean, and prove the original bug's counterexamples.
* **B. The fix.** Prove that the checks the shipped kernel uses are sound, so SIMD can miss a
  run but can never invent one, and that the kernel built on them computes the right set.

## Design

`RangeSetBlaze/SimdRunCheck.lean` is a standalone module. It does not depend on the range-set
proofs.

* **Lanes.** `BitVec w`, whose `+` wraps exactly like a `w`-bit SIMD lane.
* **`wrappingRun first len`.** Lane `i` holds `first + i`: the vector the kernel compares against.
* **`IsRun`.** Read as natural numbers, the chunk is `first, first + 1, …`, with no wrap.
* **Checks.** `originalCheck` (lane test alone), `chunkCheck` (plus `first ≤ last`), and
  `blockCheck` (plus the unrolled loop's precondition that the block continues the previous run).

Concrete counterexamples are proved with kernel `decide`, not `native_decide`, so they add no
axioms.

## Part A findings

* `originalCheck_accepts_wrapped_chunk`: the 16-lane `u8` chunk `[254, 255, 0, 1, …, 13]` passes
  the lane test and is not a run.
* `originalCheck_wrong_iff`: for 16 `u8` lanes, the original check is wrong exactly for chunks
  starting above `240`. Every chunk that passes the lane test is a wrapping run, so this lists
  every counterexample.
* `blockCheck_unroll_five_accepts_wrapped_block`: **a new finding.** For `u8` (64 lanes) and
  unroll factor 5, a block holds 320 values, more than 256. A block that wraps all the way
  around can pass the block check. This was confirmed against the real kernel: with unroll 5,
  `from_slice` on the 384 `u8` values `0, 1, …, 255, 0, 1, …, 127` returns `0..=127` instead of
  `0..=255`. Unroll factors 1, 2, 3, 4, and 8 return the right answer on that input. Production
  uses unroll 4, so shipped code is not affected, but the condition it depends on was not
  written down anywhere.

## Part B results

### Lane-level facts (`SimdRunCheck.lean`)

* `isRun_wrappingRun_iff`: a wrapping run is a real run exactly when it does not pass the top,
  `first + len ≤ 2^w`.
* `isRun_of_chunkCheck`: **the fixed chunk check is sound** for chunks of at most `2^w` lanes.
* `blockCheck_sound_iff`: **exactly when the unrolled block check is sound** for unsigned lanes:
  blocks of `M` values that continue a run are always real runs if and only if `M ≤ 2^w` or
  `2^w ∣ M`. Production (`u8`: 64 lanes × unroll 4 = 256) sits at the boundary; unroll 8 is sound
  only through divisibility plus the continuation precondition; unroll 5 is not.
* `chunksMatch_iff`, `kernelBlockCheck_eq_blockCheck`, `kernelLanesMatch_eq_lanesMatch`: the
  kernel's chunk-by-chunk comparison and its subtract-offsets lane test are the model's.

### The kernel, generic over the key type (`SimdKernel.lean`)

Rust's `collect_ranges` is generic over `T: SimdInteger`, so the model is too. `SimdKey K`
collects what the kernel needs from a key type: its order, `sub_one` (with the law that it is the
immediate predecessor), the chunk test, and the block comparison. The kernel's meaning is stated
in key space, as sets of keys. This matters for `char`, whose `sub_one` skips the surrogate gap:
the kernel rightly continues a run from `'\u{D7FF}'` to `'\u{E000}'`, which are adjacent
characters but not adjacent lane values.

* `SimdKey.kernelRanges_correct`: **the kernel is correct for any key type**, given a sound
  unrolled loop: its ranges cover exactly the input keys, and none is backwards (`start > stop`).
  `RangeCollector::push` and `UnionIter` both assert the second; set equality alone cannot rule
  it out, since a backwards range covers nothing.

### The key types (`SimdKeys*.lean`)

`LaneKey` (`SimdKeys.lean`) is the shared recipe: keys map to `w`-bit lanes and are ordered like
their lanes after adding a fixed shift. Its chunk test and unrolled loop are proved sound once,
whenever a block holds at most `2^w` keys, which every shipped configuration satisfies.

| Rust key types | Model | Shipped theorem |
|---|---|---|
| `u8` `u16` `u32` `u64` `usize`, `Ipv4Addr` | `unsignedLaneKey` (shift `0`) | `shipped_unsigned_kernel_correct` |
| `i8` `i16` `i32` `i64` `isize` | `signedLaneKey` (shift `2^(w-1)`) | `shipped_signed_kernel_correct` |
| `char` | `charLaneKey` (`sub_one` skips the surrogate gap) | `shipped_char_kernel_correct` |
| `u128`, `Ipv6Addr` | `u128SimdKey` (two `u64` lanes per key) | `shipped_128bit_kernel_correct` |
| `i128` | `i128SimdKey` (two lanes, signed order) | `shipped_128bit_kernel_correct` |
| `TotalF32` `TotalF64` | `totalLaneKey` (the `total_cmp` ordered value; lane `floatKey`) | `shipped_float_kernel_correct` |
| `NotNanF32` `NotNanF64` | `notNanLaneKey` (`sub_one` skips `-0.0`) | `shipped_float_kernel_correct` |

Each shipped theorem covers 512-bit vectors and unroll factor 4. For 128-bit keys, the two-lane
test plus `first ≤ last` rules out a carry from the low half into the high half, so SIMD can miss
a run but never invent one. `Ipv4Addr` and `Ipv6Addr` are converted lane by lane in Rust, with
exactly `u32`'s and `u128`'s lanes and order, so the unsigned models cover them.

Floats (`SimdKeysFloat.lean`) are modeled by their `total_cmp` ordered value, the signed integer
Rust's `total_cmp` compares, so the model's order is Rust's `Ord` by construction. Rust loads the
lane `f32_key` / `f64_key` (`floatKey`); `floatKey_totalOrdered` proves, for every width, that this
lane is the ordered value plus `2^(w-1)`, which reduces floats to the signed-integer proof. `NotNan` values exclude NaN
and `-0.0`; `-0.0` is the only ordered value its `sub_one` skips, as `char` skips the surrogates.

All of these depend only on Lean and Mathlib's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). Two mutations of the unsigned-only first version confirmed the proofs depend on the
fix: dropping `first ≤ last` from the chunk test broke five proofs, and changing the shipped
unroll factor to 5 broke its production theorem.

## Scope and correspondence

* **Modeled:** every key type the Rust kernel runs on, the kernel's control flow (the outer chunk
  loop, both extension loops, the scalar fallbacks), the continuation tests, the lane tests, and
  `RangeCollector::push`.
* **Not modeled:**
  * the sort and union after the kernel, which only operate on the ranges it returns;
  * the map kernel (`from_slices`);
  * the generic block-soundness condition is `M ≤ 2^w`; the exact condition with its
    `2^w ∣ M` case is proved only at the lane level for unsigned lanes (`blockCheck_sound_iff`).
* **Trusted, not proved:** that `fearless_simd`'s lane operations (on every dispatch level,
  including the scalar fallback), `bytemuck`'s reinterpretation, and the compiler behave as the
  model assumes.
* **Correspondence** is by inspection: each Lean definition's doc comment names the Rust code it
  models. The unroll-5 counterexample was confirmed against the real kernel.

## Rust follow-up

`range-set-blaze` commit `769630ad` turns the proved condition into a compile-time check.
`unrolled_block_check_is_sound` computes `block_len <= 2^bits || 2^bits ∣ block_len`, and
`assert_unroll_is_sound` asserts it in both SIMD kernels for every key type and unroll factor
they are instantiated with. Unroll factors 1, 2, 4, and 8 compile for every type; `u8` with
unroll 5 is rejected at compile time, while `u16` with unroll 5 (160-value blocks) is accepted.

## Review against the nine rules

Checked against "Nine Rules for Vibe Validation of Vibe-Coded Algorithms":

* **Guardrails (Rule 3):** the project builds, the module compiles directly, no `sorry`, and only
  the standard axioms; two mutations are caught.
* **Cleanup and metrics (Rules 2 and 4):** one Local/Shared pass, measured with the v3 collector
  on this module:

  | Metric | Before | After |
  |---|---|---|
  | Active code lines | 435 | 434 |
  | Comment-only lines | 108 | 121 |
  | `have` | 49 | 39 |
  | `rw` | 46 | 43 |
  | `simp` | 65 | 62 |
  | `omega` | 49 | 45 |
  | `grind` | 2 | 1 |
  | Theorems | 34 | 37 |

  Active size stayed flat while adding `kernelLanesMatch_eq_lanesMatch`; shared lemmas
  (`chunkCheck_eq_true_iff`, `toNat_one`, `valueSet_of_continuation`) replaced duplicated
  reasoning.
* **Adversarial review (Rule 7):** done by a fresh Codex session, using
  `specs/simd-run-check-review-prompt.md`. It found no Rust/Lean mismatch, no vacuous hypothesis,
  and no wrong result in the shipped configuration, and reported two issues:
  1. *Proof gap:* set equality does not prove that every returned range is nonempty, which the
     kernel's callers assert. Fixed: `allNonempty_kernelRanges`.
  2. *Clarity:* for `char`, whose values don't fill their 32-bit lanes, the Rust compile-time
     condition is sufficient but stricter than necessary, so "exactly when" overstated it. Fixed
     in the Rust doc comment (`range-set-blaze` commit `8806b1ad`): exact for full lane types,
     conservative for converted ones. Shipped unroll 4 is unaffected.
* **Meta-prompting (Rule 1):** partly. The first version was developed directly in one session.
  For the generalization to every key type, the session wrote self-contained prompts for Sonnet
  subagents (integers, `char`, and 128-bit keys), then compiled, axiom-checked, and read each
  result before committing it. One subagent defined its own `LinearOrder Char`; it was replaced
  with Mathlib's, which already exists.
* **Generalization metrics** (all `Simd*` files, v3 collector), from the unsigned-only version
  (`4510c95`) to every key type: active code lines 501 → 1,026, theorems 39 → 72, `have`
  42 → 113. A cleanup pass on the subagent-written files, especially `SimdKeys128.lean`, is
  still to do.

## Possible follow-ups

* A cleanup pass (Rules 2 and 4) on the generalized proof.
* The map kernel (`from_slices`): same as `from_iter` on keys and values, with last-wins
  priority.
* State the kernel's result in the library's range vocabulary (Rule 9).
