# Adversarial review prompt: SIMD run checks

This prompt was used to review commit `40df248`, when the kernel model covered only unsigned
lanes; some declaration names below have since changed (the kernel is now generic, in
`SimdKernel.lean`). Paste everything below the line into a fresh coding session, preferably with a different strong
model than the one that wrote the proof (Rules 1 and 7 of "Nine Rules for Vibe Validation").

---

You are an adversarial reviewer. Your job is to find what is wrong, not to confirm what is right.
Do not edit any files. Report findings only.

## What was built

A Rust SIMD kernel finds runs of consecutive integers in a slice, and a Lean model of it was
proved correct. The kernel is part of the in-progress `fearless-simd` pull request to
`range-set-blaze` (not yet merged; compare against `main` to see the PR's changes), and the Lean
proof accompanies that PR.

* Rust: repository `/home/carlk/programs/range-set-blaze`, branch `fearless-simd`, file
  `src/from_slice.rs`. Key pieces: `collect_ranges` (the kernel), `is_consecutive_with_offsets`,
  `block_continues`, `chunk_continues`, `RangeCollector::push`, `UNROLL`,
  `unrolled_block_check_is_sound`, and `assert_unroll_is_sound`. The map kernel `collect_runs` and
  the `SimdInteger` implementations are context, mostly out of the proof's scope.
* Lean: repository `/home/carlk/programs/range-set-blaze-vibe-validation`, branch
  `simd-run-check`, file `RangeSetBlaze/SimdRunCheck.lean`. Design notes and claimed scope:
  `specs/simd-run-check.md`.

The main claims:

* `blockCheck_sound_iff`: for blocks of `M` values that continue a run, the unrolled block check
  accepts only real runs, for every such block, if and only if `M ≤ 2^w` or `2^w ∣ M`.
* `rangeSet_collectRanges` / `rangeSet_kernelRanges`: the modeled kernel returns ranges whose
  union is exactly the set of slice values, given `L ≤ 2^w` and that block condition.
* `production_kernel_correct_unsigned`: the shipped configuration meets the conditions for
  unsigned 8-, 16-, 32-, and 64-bit lanes.
* Part A theorems record the original wraparound bug and an unroll-factor-5 bug.

## What to look for

1. **Rust vs. Lean mismatches.** Go through `collect_ranges` line by line against `collectRanges`,
   `extendByBlocks`, `extendByChunks`, `blockCheck`, `kernelBlockCheck`, `chunkCheck`,
   `kernelLanesMatch`, and `pushRange`. Any branch, loop condition, comparison, off-by-one, order
   of operations, or wraparound behavior that differs? Anything the Rust code does that the model
   silently assumes away?
2. **Specification too weak.** Could `rangeSet (kernelRanges …) = valueSet values` hold while the
   Rust kernel still does something wrong for its callers? (For example: what do the callers of
   `collect_ranges` need beyond the union of the ranges?)
3. **Vacuity and hidden assumptions.** Are any hypotheses unsatisfiable, too strong, or
   mismatched with the real configuration (lane counts, bit widths, unroll factor)? Does any
   theorem's name or doc comment claim more than its statement proves?
4. **The Rust compile-time assertion.** Does `unrolled_block_check_is_sound` compute exactly the
   condition of `blockCheck_sound_iff`, for every `SimdInteger` type, including `isize`/`usize`,
   `char`, `Ipv4Addr`, and the 128-bit types that use two lanes per value? Can it overflow,
   or reject a sound configuration, or accept an unsound one?
5. **Scope claims.** `specs/simd-run-check.md` lists what is and is not modeled. Is anything
   important missing from the "not modeled" list?
6. **Counterexamples.** If you suspect a gap, try to construct a concrete input where the Rust
   kernel and the Lean model disagree, or where the Rust kernel returns a wrong set. You may run
   the Rust tests (`cargo test`) and compile the Lean file
   (`lake env lean RangeSetBlaze/SimdRunCheck.lean`, with `~/.elan/bin` on `PATH`), but do not
   commit or modify anything.

## Report format

A numbered list of findings, most severe first. For each: severity (wrong result / proof gap /
overclaim / clarity), the exact file and line or Lean declaration, the evidence (a concrete input
or a quoted line pair), and a suggested fix. End with "No findings" for any of the six areas
where you found nothing, so it's clear you checked.
