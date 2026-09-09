# Phase 1: delete dead `deleteExtraNRs_sets_after_splice_of_chain`

Collected 2026-09-09 in `/home/carlk/programs/range-set-blaze-lean2` as one
mechanical Phase 1 review unit. No commit, tag, push, or staging was performed.

## Identity and corrected-v2 artifact

- Baseline corrected-v2 artifact: `metrics/phase1-dead-ok-delete-extra-nrs-v2.json`
- Baseline artifact SHA-256: `5cc2c7718862c5aba1ae456490b08bcd63db2c400733159ef2b904bf6c3bf2c2`
- Baseline artifact source identity: commit `ff4e4f85a5aad34583a2771707adb3f8c5eeac47`, tree `8f17d8ae7f6e2348ec2b823dd7d5d0b743c8ac7e`
- Current HEAD/source identity before this edit: commit `3ed100fcc5a4da7eb51598be75194c8069f9ffd1`, tree `dc82a541260a9cc729ea1662bde55d9f7b5a1044`
- Baseline source manifest SHA-256: `18bf4898ab8131e5802f60f4e4f8daf9133aba4345f048c137e8ddd66ae7821e`
- HEAD source bytes match every baseline manifest entry exactly (the artifact was collected before the prior commit, but against the same source bytes).
- Post-edit source manifest SHA-256: `0442ea2dd685165583d50fd2528203083dbd1f1bd3b7f97eb3fbcdc4a21a81bb`
- Collector: `scripts/phase0_metrics.py`, version 2; collector SHA-256 `4db7973927010a84c2b69cf1eb02d81703050c2a7e5c9ac7a51cb125c12a6ef5`
- Post-edit JSON SHA-256: `79e84815f08ebbdd35efade6953ce109f8d87259426ef0f708be926fa11a6cfc`

## Candidate comparison and scope

Comment-aware token-bounded analysis used `strip_comments` from
`scripts/phase0_metrics.py` on the current pre-edit HEAD. All three candidates
are private proof declarations with declaration-only active references; none is
an executable definition or part of a public theorem interface.

| Candidate | Active proof LOC | Active references before deletion | Raw apparent references in disabled historical blocks | Cluster / decision |
|---|---:|---|---|---|
| `deleteExtraNRs_loop_preserves_sets` | 39 | declaration only (line 224) | 2670–2671 | loop set-preservation cluster; defer as separate unit |
| `chain_replace_suffix_same_lo` | 54 | declaration only (line 303) | 2538–2539 | chain-replacement cluster; defer as separate unit |
| `deleteExtraNRs_sets_after_splice_of_chain` | 94 | declaration only (line 1695) | 2131, 2541, 2550 | splice/set-preservation cluster; selected |

The raw references for the selected candidate at HEAD were lines 1695
(declaration), 2131 (inside historical `internalAdd2_toSet` block), 2541
(historical comment label), and 2550 (inside historical
`internalAddC_extendPrev_toSet` block). After deletion, the active reference
count is zero and all three disabled historical textual references remain
untouched. The declaration had no attached documentation comment; only the
declaration/proof block was removed.

The exact diff is one file, 0 insertions and 128 deletions:

```text
RangeSetBlaze/AlgoC.lean | 128 -----------------------------------------------
1 file changed, 128 deletions(-)
```

The deleted HEAD block is lines 1695–1822, 128 lines / 5604 bytes,
SHA-256 `2b693e55fd1d96df1fe6c6abd20ee0ba783cb9be83316cfe3d05ce120dc29229`.
The binary patch SHA-256 is
`6940e8c924d079bc98a23bf86c1bcce7041aceea86d27f3c7f97f89c9f8f11a4`.

## Commands and results

| Command | Exit | Result |
|---|---:|---|
| `git diff --check` | 0 | Passed. |
| `/home/carlk/.elan/bin/lake build` | 0 | Completed successfully (1876 jobs). |
| `/home/carlk/.elan/bin/lake env lean RangeSetBlaze/AlgoC.lean` | 0 | Direct compilation succeeded with no output. |
| `python3 scripts/test_phase0_metrics.py` | 0 | 3 tests passed. |
| comment-aware integrity scan | 0 | No active `sorry`, `admit`, `axiom`, or `unsafe`; no active source axiom declarations. |
| temporary `#print axioms RangeSetBlaze.internalAddC_toSet` | 0 | Exact output below. |
| corrected-v2 collector | 0 | JSON written at the post-edit path above. |
| footprint/public-statement checks | 0 | All protected bodies and active public theorem statements match HEAD exactly. |

`lake build` warnings were complete and classified as one pre-existing
linter warning, `RangeSetBlaze/AlgoB.lean:465:8: try 'simp' instead of 'simpa'`.
The `Main.lean:52–56` lines were expected informational values, not warnings.
There were no new, unexplained, or source-file warnings. Direct compilation
was silent.

The exact axiom output was:

```text
'RangeSetBlaze.internalAddC_toSet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` dependency was present.

## Corrected-v2 deltas

Comparison is against `metrics/phase1-dead-ok-delete-extra-nrs-v2.json`.

| Metric | Baseline | Current | Delta |
|---|---:|---:|---:|
| Algo C physical LOC | 2989 | 2861 | -128 |
| Algo C nonblank LOC | 2750 | 2637 | -113 |
| Algo C blank LOC | 239 | 224 | -15 |
| Algo C comment-only LOC | 1002 | 983 | -19 |
| Algo C active-code LOC | 1748 | 1654 | -94 |
| Algo C definitions | 10 | 10 | 0 |
| Algo C lemma/theorem declarations | 28 | 27 | -1 |
| Algo C private lemma/theorem declarations | 22 | 21 | -1 |
| Repository physical LOC | 4460 | 4332 | -128 |
| Repository nonblank LOC | 4094 | 3981 | -113 |
| Repository blank LOC | 366 | 351 | -15 |
| Repository comment-only LOC | 1077 | 1058 | -19 |
| Repository active-code LOC | 3017 | 2923 | -94 |
| Repository definitions | 52 | 52 | 0 |
| Repository lemma/theorem declarations | 63 | 62 | -1 |
| Repository private lemma/theorem declarations | 26 | 25 | -1 |
| `by_cases` | 23 | 23 | 0 |
| `cases` | 70 | 68 | -2 |
| `grind` | 0 | 0 | 0 |
| `have` | 652 | 624 | -28 |
| `linarith` | 12 | 12 | 0 |
| `omega` | 11 | 11 | 0 |
| `rw` | 164 | 158 | -6 |
| `simp` | 266 | 253 | -13 |
| `simpa` | 85 | 81 | -4 |

The active-proof reduction is exactly 94 LOC; the additional physical/comment
reductions are reported separately by the collector and are not presented as
proof compression.

## Protected algorithm footprint

Raw source-byte spans for all protected executable definitions were hashed
against HEAD and the current source. Every hash and byte length matched:

| Definition | Lines | Bytes | SHA-256 |
|---|---:|---:|---|
| `deleteExtraNRs_loop` | 39 | 1618 | `8643dd508d2a4de3e723959fff187b54801358d275f418317dc4f212d1f4cd30` |
| `deleteExtraNRs` | 15 | 636 | `c193de7b55fca0240df1732875d90be36705b56c885b2d5b0b93ebab63ddbd7a` |
| `internalAdd2NRs` | 18 | 608 | `3549e490302f47e8bc705593160ba542ad893ea5cd397c86661c31743da5776c` |
| `internalAddC_extendPrev_safe` | 189 | 9348 | `da5bd3dac0a43b8ab9c07dfd89c6db696c48c872a27b327b3805caddcc61fd6f` |
| `internalAddC` | 56 | 2468 | `d18e87349fcc0ec457b956f4b437142b2867646282a63c43d590d828627bd492` |

Thus empty-input handling, the `lo ≤ start` split, predecessor gap/coverage/
touching branches, the `next.lo ≤ current.hi + 1` merge condition, lower
endpoint preservation, and `max` upper-endpoint behavior are unchanged.

## Active public theorem statements

Comment-aware statements (from declaration start through `:=`, excluding proof
bodies) for all six active public lemma/theorem declarations were unchanged.
The statement SHA-256 values are identical for HEAD/current:

| Declaration | SHA-256 |
|---|---|
| `deleteExtraNRs_loop_sets` | `b76e9199a42d19d99da9eb1681da3ea2b7d004871f51bbef3f07ceecd4e6c690` |
| `getLast?_eq_some_getLast` | `66f974219503ef182840ccc775f36f4fe399052b93099143c41acd9638018ef5` |
| `internalAdd2_safe_toSet` | `401edc1069c5c6ee1db2c775a0192cfc05639655f504ec8c353232333fd0a0a8` |
| `internalAdd2_safe_from_le_toSet` | `8da4b593458e4e61fcafde8f0b0067c1197241f4616baad3e776e650927f4099` |
| `internalAddC_extendPrev_safe_toSet` | `36ada6dea97118cdecae00064a7140d025364acd667fc6a6995a11cb48a5a9d7` |
| `internalAddC_toSet` | `bde2f9cca423a9d27f9ac885b181dd6447009436afe76228dc38742a57cd5619` |

The disabled historical blocks containing the apparent callers were not
edited. No executable definition, public theorem statement, or theorem
interface changed.

## Final Git status

```text
 M RangeSetBlaze/AlgoC.lean
?? metrics/phase1-dead-delete-extra-nrs-splice-chain-v2.json
?? metrics/phase1-dead-delete-extra-nrs-splice-chain-v2.md
```
