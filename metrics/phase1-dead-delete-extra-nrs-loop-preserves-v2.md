# Phase 1: delete dead `deleteExtraNRs_loop_preserves_sets`

Collected 2026-09-09 in `/home/carlk/programs/range-set-blaze-lean2` as one
mechanical Phase 1 review unit. No commit, tag, push, or staging was
performed.

## Candidate comparison and scope

The candidate set was re-audited with the comment-aware `strip_comments`
logic from `scripts/phase0_metrics.py`. The selected declaration is a private,
proof-only helper. Its pre-edit exact occurrences were the declaration at
`AlgoC.lean:224` and two references at `AlgoC.lean:2467–2468`, both inside a
disabled historical proof block. Thus its active reference count was one
(the declaration itself), and its active caller count was zero.

| Candidate | Active-code LOC | Active callers | Disabled/raw references | Decision |
|---|---:|---|---|---|
| `deleteExtraNRs_loop_preserves_sets` | 39 | none (declaration only) | 2467–2468 | selected; loop set-preservation cluster |
| `ok_deleteExtraNRs_loop` | 50 | none (declaration only) | none | defer; invariant-preservation cluster |
| `deleteExtraNRs_sets_after_splice_of_chain` | 94 | none in active source | historical block only | defer; splice/set-preservation cluster |
| `deleteExtraNRs_loop_lo_ge` | 36 | active callers | none | retain; used by production proofs |

The deleted block consists of the declaration, its documentation, and the
directly attached internal proof comments. It is 55 physical lines, 39
active-code LOC, 2465 bytes, and SHA-256
`daf7d9ee517b31858575ba78f45310f87a65b5b0d898f9b6da3548c9e5779d0b`.
No executable definition, public theorem statement, disabled historical block,
or unrelated source was changed.

Exact source diff:

```text
 RangeSetBlaze/AlgoC.lean | 55 ------------------------------------------------
 1 file changed, 55 deletions(-)
```

## Identity and evidence

- Baseline corrected-v2 artifact: `metrics/phase1-dead-chain-replace-suffix-same-lo-v2.json`
- Baseline artifact SHA-256: `63f9224ae79df3bfd26bbac0408692f097cdb5feaaf1e56ae5e360dd6ec2c20b`
- Baseline source manifest SHA-256: `88cf968bb40b774c7ed594ab789da9902476e9e8135af94ac195d3108acfcdb0`
- Baseline manifest check: all 7 entries matched the current pre-edit HEAD (`541cf045b89fd7688a68277cb04a4d282fe07a9f`) byte-for-byte.
- Current corrected-v2 artifact: `metrics/phase1-dead-delete-extra-nrs-loop-preserves-v2.json`
- Current source manifest SHA-256: `5b4bdee5cf0b7795d6350e3564ac7525aeb73ce1b12654087d134566aa86000a`
- Current `AlgoC.lean` SHA-256: `622a3ac886bbb20e144cac147836a709e0bb3a70e2256de61f29e6fb2a7087d1`
- Current artifact SHA-256: `cfea063ee04249c0b598d268480bc7af568bd58027e8f895681adc5eb4912135`
- Proof-source `git diff --binary` SHA-256: `db6127b7b0ea2ef3de216a31211d6b7eaa4f6e13777965c7043ceec9d8e58bf9`
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
| Algo C physical LOC | 2786 | 2731 | -55 |
| Algo C nonblank LOC | 2568 | 2519 | -49 |
| Algo C blank LOC | 218 | 212 | -6 |
| Algo C comment-only LOC | 968 | 958 | -10 |
| Algo C active-code LOC | 1600 | 1561 | -39 |
| Algo C definitions | 10 | 10 | 0 |
| Algo C lemma/theorem declarations | 26 | 25 | -1 |
| Algo C private lemma/theorem declarations | 20 | 19 | -1 |
| Repository physical LOC | 4257 | 4202 | -55 |
| Repository nonblank LOC | 3912 | 3863 | -49 |
| Repository blank LOC | 345 | 339 | -6 |
| Repository comment-only LOC | 1043 | 1033 | -10 |
| Repository active-code LOC | 2869 | 2830 | -39 |
| Repository definitions | 52 | 52 | 0 |
| Repository lemma/theorem declarations | 61 | 60 | -1 |
| Repository private lemma/theorem declarations | 24 | 23 | -1 |
| `by_cases` | 23 | 22 | -1 |
| `cases` | 64 | 63 | -1 |
| `have` | 616 | 608 | -8 |
| `linarith` | 12 | 11 | -1 |
| `omega` | 11 | 11 | 0 |
| `rw` | 152 | 145 | -7 |
| `simp` | 243 | 239 | -4 |
| `simpa` | 81 | 81 | 0 |

## Cumulative corrected-v2 delta from the Phase 0 baseline

| Metric | Phase 0 | Current | Delta |
|---|---:|---:|---:|
| Algo C physical LOC | 3320 | 2731 | -589 |
| Algo C active-code LOC | 1983 | 1561 | -422 |
| Repository physical LOC | 4791 | 4202 | -589 |
| Repository active-code LOC | 3252 | 2830 | -422 |
| `by_cases` | 24 | 22 | -2 |
| `cases` | 84 | 63 | -21 |
| `have` | 694 | 608 | -86 |
| `linarith` | 12 | 11 | -1 |
| `omega` | 15 | 11 | -4 |
| `rw` | 174 | 145 | -29 |
| `simp` | 289 | 239 | -50 |
| `simpa` | 85 | 81 | -4 |

## Protected executable definitions

Raw declaration-span hashes were compared between HEAD and the current source,
trimming only trailing whitespace at each span boundary. Every protected body
matched exactly:

| Definition | Bytes | SHA-256 |
|---|---:|---|
| `deleteExtraNRs_loop` | 1602 | `f39036c4e1dc107b9cdbcdd9e0f11347044f9bb73edcf0ab16b59fc46387a0a6` |
| `deleteExtraNRs` | 628 | `d945b0e942910e4526bd2e18c1a869e4b835f267547ff73d339b98594669aefb` |
| `internalAdd2NRs` | 604 | `0ab75a1b409efdf4e8c66f52ddf1a48e8fe427a86a705861b04de189edbc2ca2` |
| `internalAddC_extendPrev_safe` | 9260 | `6f0f081bd05c921b3b6f56650178865956d608e8ddc82d6f802d791a5c83c0eb` |
| `internalAddC` | 2441 | `b4519cff69426b54fb1fccc42d4a76eb626df1c6c7fbca1c7212382db8a5e144` |

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
?? metrics/phase1-dead-delete-extra-nrs-loop-preserves-v2.json
?? metrics/phase1-dead-delete-extra-nrs-loop-preserves-v2.md
```

No commit, tag, push, or staging was performed.
