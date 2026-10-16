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

All in `RangeSetBlaze/SimdRunCheck.lean`, building on four arithmetic and list facts:

* `isRun_wrappingRun_iff`: a wrapping run is a real run exactly when it does not pass the top,
  `first + len ≤ 2^w`.
* `isRun_of_chunkCheck`: **the fixed chunk check is sound** for chunks of at most `2^w` lanes.
  Every SIMD chunk qualifies.
* `blockCheck_sound_iff`: **exactly when the unrolled block check is sound.** For blocks of `M`
  values that continue a run, it accepts only real runs, for every such block, if and only if
  `M ≤ 2^w` or `2^w ∣ M`. Production (`u8`: 64 lanes × unroll 4 = 256) sits at the boundary;
  unroll 8 is sound only through divisibility plus the continuation precondition; unroll 5 is not.
* `chunksMatch_iff` and `kernelBlockCheck_eq_blockCheck`: the kernel's chunk-by-chunk comparison,
  stepping the expected vector by `L`, is the block check above.
* `kernelLanesMatch_eq_lanesMatch`: the lane test as Rust writes it,
  `(values - offsets) == splat(first)`, is the model's `lanesMatch`.
* `rangeSet_collectRanges`: **the kernel is correct.** A model of `collect_ranges` that follows
  its loops and branches (the outer chunk loop, the unrolled extension loop, the single-chunk
  extension loop, the scalar fallbacks, and `RangeCollector::push` merging) returns ranges whose
  union is exactly the set of slice values, given `L ≤ 2^w` and the block condition.
* `production_kernel_correct_unsigned`: the shipped configuration (512-bit vectors, unroll 4)
  satisfies the conditions for `u8`, `u16`, `u32`, and `u64` lanes. It does not cover the kernel's
  other key types; see "Scope".

The main lemmas depend only on Lean and Mathlib's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). Two mutations confirmed the proofs depend on the fix: dropping
`first ≤ last` from `chunkCheck` breaks five proofs, and changing the production unroll factor to
5 breaks `production_kernel_correct_unsigned`.

## Scope and correspondence

* **Modeled:** unsigned lanes of any width `w`, any lane count `L`, any unroll factor, the
  kernel's control flow, the continuation tests, and `RangeCollector::push`.
* **Not modeled:**
  * signed lanes (`i8` … `i64`, `isize`), whose `first ≤ last` uses signed order;
  * 128-bit keys (`u128`, `i128`, `Ipv6Addr`), which span two 64-bit lanes;
  * key types loaded lane by lane (`char`, `Ipv4Addr`);
  * the sort and union after the kernel, which only operate on the ranges it returns;
  * the map kernel (`from_slices`).
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
* **Adversarial review (Rule 7):** pending. `specs/simd-run-check-review-prompt.md` is the
  prompt for a fresh session with a different model.
* **Meta-prompting (Rule 1):** not followed. The proof was developed directly in one session.

## Possible follow-ups

* Signed lanes, via the order isomorphism that adds `2^(w-1)` (flipping the sign bit), which
  preserves wrapping addition.
* 128-bit lanes: matching `splat(first) + [0, 0, 1, 0, …]` implies a real `u128` run.
* State the kernel's result in the library's range vocabulary (Rule 9).
