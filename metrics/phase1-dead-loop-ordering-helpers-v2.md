# Phase 1: delete dead loop-ordering helpers

Collected 2026-09-09 in `/home/carlk/programs/range-set-blaze-lean2` as one
mechanical Phase 1 review unit. No commit, tag, push, or staging was
performed.

## Candidate comparison and scope

The pre-edit source was audited with the comment-aware `strip_comments` logic
from `scripts/phase0_metrics.py`. The selected helpers are private,
proof-only declarations. `ok_deleteExtraNRs_loop` had one active exact
occurrence (its declaration) and zero active callers. `loLE_iff` had one active
exact occurrence (its declaration) and zero active callers. The opening status
text and disabled historical references were excluded from active counts and
were not edited.

| Candidate | Active-code LOC | Active callers | Decision |
|---|---:|---|---|
| `ok_deleteExtraNRs_loop` | 50 | none (declaration only) | selected; obsolete strong loop invariant helper |
| `loLE_iff` | 1 | none (declaration only) | selected; obsolete one-line unfolding helper |
| `ok_deleteExtraNRs_loop_weak` | 59 | active callers | retain; used by production proofs |
| `deleteExtraNRs_loop_lo_ge` | 36 | active callers | retain; used by production proofs |
| `pairwise_before_implies_chain_loLE` | 20 | active callers | retain; supplies the remaining `loLE` chain API |

The deleted blocks are the directly attached documentation/proof comments and
proof declarations only. The combined deletion is 80 physical lines, 51
active-code LOC, 3950 bytes, and SHA-256
`21c09a66587943677ddb1acd90e058f9735c668105b59401df46b8b8a6e607f8`.
The `ok_deleteExtraNRs_loop` block alone was lines 489–566, 3867 bytes, SHA-256
`6699f575bc94e3ffae0bd43ac8d00418d4cbf739d5257858a4be31f8482fdbd9`.
The `loLE_iff` block was lines 221–222, 83 bytes, SHA-256
`0546a21d15b3d22ebf52facfb998cf8e29cfb162d10164f1821b770fbd5c2803`.

No executable definition, public theorem statement, disabled historical block,
`ok_deleteExtraNRs_loop_weak`, or `loLE` definition was changed.

Exact source diff:

```text
 RangeSetBlaze/AlgoC.lean | 80 ------------------------------------------------
 1 file changed, 80 deletions(-)
```

## Identity and evidence

- Baseline corrected-v2 artifact: `metrics/phase1-dead-delete-extra-nrs-loop-preserves-v2.json`
- Baseline artifact SHA-256: `cfea063ee04249c0b598d268480bc7af568bd58027e8f895681adc5eb4912135`
- Baseline source manifest SHA-256: `5b4bdee5cf0b7795d6350e3564ac7525aeb73ce1b12654087d134566aa86000a`
- Baseline manifest check: all 7 entries matched the current pre-edit HEAD (`de1b33af72492b8ca1e6394d86ed6bf9217104a7`) byte-for-byte.
- Current corrected-v2 artifact: `metrics/phase1-dead-loop-ordering-helpers-v2.json`
- Current source manifest SHA-256: `4b02f08b43cc2f7537413dc1e7e4bdc028c2cde2b5abe099c4723bd80a835c9d`
- Current `AlgoC.lean` SHA-256: `176c1b5843d3ee37b4ea9285451ebd1835fa259b0d4e0d38a35b8f36b239b5e9`
- Current artifact SHA-256: `31b1199647caa00ba31cb43d175fa89093313666cf052e92a504d81eac3dc672`
- Proof-source `git diff --binary` SHA-256: `93cd3569bd930b0c460eb99769f13be37239a34e4f70504a4d228b16da46525d`
- Collector: `scripts/phase0_metrics.py`, version 2; SHA-256 `4db7973927010a84c2b69cf1eb02d81703050c2a7e5c9ac7a51cb125c12a6ef5`

The JSON parses successfully, and its manifest, manifest hash, and metrics
match a fresh collector run on the post-edit working tree.

## Checks

| Command/check | Exit | Result |
|---|---:|---|
| `git diff --check` | 0 | Passed. |
| `/home/carlk/.elan/bin/lake build` | 0 | Completed successfully (1876 jobs). |
| `/home/carlk/.elan/bin/lake env lean RangeSetBlaze/AlgoC.lean` | 0 | Direct compilation succeeded with no output. |
| `python3 scripts/test_phase0_metrics.py` | 0 | 3 tests passed. |
| comment-aware integrity scan | 0 | No active `sorry`, `admit`, `axiom`, or `unsafe`; no active source axiom declarations. |
| temporary `#print axioms RangeSetBlaze.internalAddC_toSet` | 0 | Exact output recorded below. |
| corrected-v2 collector | 0 | JSON written and independently compared with a fresh run. |
| protected executable-definition comparison | 0 | All five protected declaration spans match HEAD exactly. |
| active public theorem-statement comparison | 0 | All six active public statements match HEAD exactly. |

The build emitted only the pre-existing linter warning at
`RangeSetBlaze/AlgoB.lean:465` (`try 'simp' instead of 'simpa'`) and the five
expected informational values from `Main.lean`; no new source warning appeared.

Comment-aware integrity output:

```text
active sorry: False
active admit: False
active axiom: False
active unsafe: False
active matches: []
active axiom declarations: []
```

The elaborated axiom query returned exactly:

```text
'RangeSetBlaze.internalAddC_toSet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` dependency.

## Corrected-v2 metric delta from the immediate baseline

| Metric | Baseline | Current | Delta |
|---|---:|---:|---:|
| Algo C physical LOC | 2731 | 2651 | -80 |
| Algo C nonblank LOC | 2519 | 2444 | -75 |
| Algo C blank LOC | 212 | 207 | -5 |
| Algo C comment-only LOC | 958 | 934 | -24 |
| Algo C active-code LOC | 1561 | 1510 | -51 |
| Algo C definitions | 10 | 10 | 0 |
| Algo C lemma/theorem declarations | 25 | 23 | -2 |
| Algo C private lemma/theorem declarations | 19 | 17 | -2 |
| Repository physical LOC | 4202 | 4122 | -80 |
| Repository nonblank LOC | 3863 | 3788 | -75 |
| Repository blank LOC | 339 | 334 | -5 |
| Repository comment-only LOC | 1033 | 1009 | -24 |
| Repository active-code LOC | 2830 | 2779 | -51 |
| Repository definitions | 52 | 52 | 0 |
| Repository lemma/theorem declarations | 60 | 58 | -2 |
| Repository private lemma/theorem declarations | 23 | 21 | -2 |
| `by_cases` | 22 | 21 | -1 |
| `cases` | 63 | 61 | -2 |
| `have` | 608 | 601 | -7 |
| `linarith` | 11 | 11 | 0 |
| `omega` | 11 | 9 | -2 |
| `rw` | 145 | 143 | -2 |
| `simp` | 239 | 233 | -6 |
| `simpa` | 81 | 79 | -2 |

## Cumulative corrected-v2 delta from the Phase 0 baseline

| Metric | Phase 0 | Current | Delta |
|---|---:|---:|---:|
| Algo C physical LOC | 3320 | 2651 | -669 |
| Algo C active-code LOC | 1983 | 1510 | -473 |
| Repository physical LOC | 4791 | 4122 | -669 |
| Repository active-code LOC | 3252 | 2779 | -473 |
| `by_cases` | 24 | 21 | -3 |
| `cases` | 84 | 61 | -23 |
| `have` | 694 | 601 | -93 |
| `linarith` | 12 | 11 | -1 |
| `omega` | 15 | 9 | -6 |
| `rw` | 174 | 143 | -31 |
| `simp` | 289 | 233 | -56 |
| `simpa` | 85 | 79 | -6 |

## Protected executable definitions

Raw declaration-span hashes were compared between HEAD and the current source,
trimming only trailing whitespace at each span boundary. Every protected body
matched exactly:

| Definition | Bytes | SHA-256 |
|---|---:|---|
| `deleteExtraNRs_loop` | 1617 | `f39036c4e1dc107b9cdbcdd9e0f11347044f9bb73edcf0ab16b59fc46387a0a6` |
| `deleteExtraNRs` | 634 | `d945b0e942910e4526bd2e18c1a869e4b835f267547ff73d339b98594669aefb` |
| `internalAdd2NRs` | 606 | `0ab75a1b409efdf4e8c66f52ddf1a48e8fe427a86a705861b04de189edbc2ca2` |
| `internalAddC_extendPrev_safe` | 9347 | `6f0f081bd05c921b3b6f56650178865956d608e8ddc82d6f802d791a5c83c0eb` |
| `internalAddC` | 2467 | `b4519cff69426b54fb1fccc42d4a76eb626df1c6c7fbca1c7212382db8a5e144` |

## Active public theorem statements

Comment-aware declaration statement extraction through `:=` found the same six
active public declarations before and after deletion. All statement hashes
matched:

| Declaration | SHA-256 |
|---|---|
| `deleteExtraNRs_loop_sets` | `c2856d53bec03655ed98ec9a38417490cc169c7b0fa1850a57a92c11ec0cf899` |
| `getLast?_eq_some_getLast` | `4ee8c308d5d24d68b0a7adbd20e5bbba6b4aa055816f18f103b4a769767ac8b3` |
| `internalAdd2_safe_from_le_toSet` | `eaa574bed4a5d30c12a07825d5c9ca86bc19fe62eccc94fdabc90b303ec3c85e` |
| `internalAdd2_safe_toSet` | `55a3b214747448285e7a731921c682b8594d851ad73bfd11d857290ec8204ad4` |
| `internalAddC_extendPrev_safe_toSet` | `69a19bf672c8269c3eaef86098aab538508f020d9867bebddfb15f17f6f84d3b` |
| `internalAddC_toSet` | `23fb2c8e810c4e9193eb96a6115b77df52213f8e98c249e4584e6f3dd514b97e` |

## Final Git status

```text
 M RangeSetBlaze/AlgoC.lean
?? metrics/phase1-dead-loop-ordering-helpers-v2.json
?? metrics/phase1-dead-loop-ordering-helpers-v2.md
```

No commit, tag, push, or staging was performed.
