# Phase 1: replace private list-while helpers with Mathlib theorems

Collected 2026-09-09 in `/home/carlk/programs/range-set-blaze-lean2` as one
uncommitted mechanical Phase 1 review unit.

## Identity

- Immediately preceding v2 artifact: `metrics/phase1-mem-takewhile-imp-v2.json`
- Immediately preceding source commit: `7dcd1bf18d6245325d5ebc6801eb6869605ec8db`
- Current v2 artifact: `metrics/phase1-list-while-batch-v2.json`
- Collector: `scripts/phase0_metrics.py`, version 2
- Collector SHA-256: `4db7973927010a84c2b69cf1eb02d81703050c2a7e5c9ac7a51cb125c12a6ef5`
- Current source manifest SHA-256: `5393d63563a61b867d37792cf8e809ed46283d41b5fafdc94720556c8a20e6ff`
- Current `RangeSetBlaze/AlgoC.lean` SHA-256: `f0ce136768f173ea598b388bc23e4a6405f44a1e7d48beb2d6d5e73629acc0b1`
- Current proof-source patch SHA-256 (`git diff --binary`): `121d71c61249c1618696edf44aab69d62b3d37ad21742d4233ec61d2c20b213f`

## Candidates and exact diff

All three remaining selected candidates were considered and included:

1. Deleted private generic `takeWhile_append_of_all`; replaced its three
   active uses with `List.takeWhile_append_of_pos` and the existing false-head
   simplification.
2. Deleted private generic `dropWhile_append_of_all`; replaced its three
   active uses with `List.dropWhile_append_of_pos` and the existing false-head
   simplification.
3. Deleted private generic `dropWhile_head_not_satisfies`; replaced its one
   active use with `List.dropWhile_get_zero_not`, transporting the result
   across the established `dropWhile = curr :: tail` equality and simplifying
   the zero-index lookup.

The pinned Lean 4.33.1 / Mathlib theorem signatures were checked directly.
The patch is exactly 26 insertions and 59 deletions in `AlgoC.lean`; it adds no
imports. The only deleted declarations are the three private helpers. The
remaining changes are local proof-term substitutions in `ok_internalAdd2NRs`,
`ok_deleteExtraNRs`, `span_split_on_splice`, and
`deleteExtraNRs_sets_after_splice_of_chain`. No executable definition, public
theorem statement, invariant, dependent proof architecture, or unrelated
cleanup changed. None of the three selected candidates was deferred.

The broader remaining Phase 1 inventory was inspected but deliberately kept
outside this measured batch:

- `pairwise_prefix_last` is another generic list helper with two active uses,
  but belongs with the pairwise-ordering cleanup rather than this Boolean
  take/drop-while unit.
- `deleteExtraNRs_loop_preserves_sets`, `chain_replace_suffix_same_lo`,
  `ok_deleteExtraNRs`, and `deleteExtraNRs_sets_after_splice_of_chain` have no
  active callers. Their proofs are materially larger and span distinct loop,
  chain-replacement, invariant, and splice clusters, so their deletion should
  be reviewed as separate units rather than hidden in this batch.
- `loLE_iff` belongs to the endpoint-order API decision; removing it is not a
  direct generic-library-theorem substitution.
- `getLast?_eq_some_getLast` is public, so deleting or changing its interface
  is excluded by this batch's constraints even though Mathlib has a related
  `List.getLast?_eq_getLast_of_ne_nil` theorem.
- Canonicalizing `algoCListSet` crosses module/API boundaries, while retained
  `mkNR` is heavily used and is not the already-removed duplicate `mkNR'`.

## Verification

| Command | Exit | Result |
|---|---:|---|
| `git diff --check` | 0 | Passed. |
| `lake build` | 0 | Completed successfully (1876 jobs). |
| `lake env lean RangeSetBlaze/AlgoC.lean` | 0 | Direct compilation succeeded. |
| `python3 scripts/test_phase0_metrics.py` | 0 | 3 tests passed. |
| `python3 scripts/phase0_metrics.py -o metrics/phase1-list-while-batch-v2.json` | 0 | Corrected-v2 artifact written. |
| raw integrity search | 0 | Only the three known inactive comment matches at AlgoC lines 15, 41, and 55. |
| comment-aware integrity scan | 0 | No active `sorry`, `admit`, `axiom`, or `unsafe`; no active source axiom declarations. |
| temporary `#print axioms RangeSetBlaze.internalAddC_toSet` | 0 | Result recorded below. |
| protected-algorithm-footprint review | 0 | Protected executable definitions and branch/merge structure are unchanged. |

`lake build` emitted only the pre-existing `AlgoB.lean:465` unnecessary-`simpa`
linter warning and the expected five `Main.lean` informational values.

The axiom query returned exactly:

```text
'RangeSetBlaze.internalAddC_toSet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` dependency or new axiom is present.

## Corrected-v2 aggregate metric delta

Comparison is against `metrics/phase1-mem-takewhile-imp-v2.json`.

| Metric | preceding v2 | this v2 | delta |
|---|---:|---:|---:|
| Algo C physical LOC | 3252 | 3219 | -33 |
| Algo C nonblank LOC | 2995 | 2965 | -30 |
| Algo C blank LOC | 257 | 254 | -3 |
| Algo C comment-only LOC | 1071 | 1070 | -1 |
| Algo C active-code LOC | 1924 | 1895 | -29 |
| Algo C definitions | 10 | 10 | 0 |
| Algo C lemma/theorem declarations | 32 | 29 | -3 |
| Algo C private lemma/theorem declarations | 26 | 23 | -3 |
| Repository physical LOC | 4723 | 4690 | -33 |
| Repository nonblank LOC | 4339 | 4309 | -30 |
| Repository blank LOC | 384 | 381 | -3 |
| Repository comment-only LOC | 1146 | 1145 | -1 |
| Repository active-code LOC | 3193 | 3164 | -29 |
| Repository definitions | 52 | 52 | 0 |
| Repository lemma/theorem declarations | 67 | 64 | -3 |
| Repository private lemma/theorem declarations | 30 | 27 | -3 |
| `by_cases` tokens | 24 | 24 | 0 |
| `cases` tokens | 76 | 75 | -1 |
| `grind` tokens | 0 | 0 | 0 |
| `have` tokens | 694 | 691 | -3 |
| `linarith` tokens | 12 | 12 | 0 |
| `omega` tokens | 15 | 15 | 0 |
| `rw` tokens | 173 | 180 | +7 |
| `simp` tokens | 281 | 279 | -2 |
| `simpa` tokens | 85 | 86 | +1 |

## Protected footprint and Git status

The exact diff contains only the three private helper deletions and the local
Mathlib proof substitutions described above. The protected executable bodies
`deleteExtraNRs_loop`, `deleteExtraNRs`, `internalAdd2NRs`,
`internalAddC_extendPrev_safe`, and `internalAddC` are unchanged, including
empty-input handling, the `lo < start`/`lo ≤ start` split behavior, predecessor
gap/coverage/touching branches, the `next.lo ≤ current.hi + 1` merge condition,
lower-endpoint preservation, and `max` upper-endpoint behavior. The exact
`internalAddC_toSet` theorem statement is unchanged.

Current status:

```text
 M RangeSetBlaze/AlgoC.lean
?? metrics/phase1-list-while-batch-v2.json
?? metrics/phase1-list-while-batch-v2.md
```

No commit, tag, push, or staging was performed.
