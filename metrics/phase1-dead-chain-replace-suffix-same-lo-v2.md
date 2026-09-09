# Phase 1: delete dead `chain_replace_suffix_same_lo`

Collected 2026-09-09 in `/home/carlk/programs/range-set-blaze-lean2` as one
mechanical Phase 1 review unit. No commit, tag, push, or staging was performed.

## Candidate comparison and scope

The current source was re-audited with the comment-aware `strip_comments`
collector logic from `scripts/phase0_metrics.py`. Both candidates are private
proof declarations, not executable definitions or public theorem interfaces.

| Candidate | Active-code LOC | Active callers | Disabled-only references | Status / cluster |
|---|---:|---|---|---|
| `deleteExtraNRs_loop_preserves_sets` | 39 | none (declaration only) | 2542–2543 | retained; loop set-preservation cluster |
| `chain_replace_suffix_same_lo` | 54 | none (declaration only) | 2410–2411 | selected; chain-replacement cluster |

The selected declaration was private and proof-only. Its raw pre-edit source
occurrences were the declaration at line 303 and disabled historical references
at lines 2410–2411. After deletion, the two disabled references remain byte-for-
byte untouched and there are no active occurrences. The deleted declaration,
doc comment, and directly attached internal proof comments were lines 301–375:
75 physical lines, 54 active-code LOC, 3194 bytes, SHA-256
`547e1f838d59b0e3bb440bc87fdf0844c044d0be151f89bbbbb80225f1f1fc3d`.

This is a coherent chain-replacement proof cluster. The loop-preservation
candidate is a separate cluster and was not bundled merely to increase LOC.
Removing the selected dead proof improves navigation by removing a 54-line
unreferenced helper and its explanatory proof comments, with no active theorem
dependency. Deletion affects no executable definition, public theorem statement,
or public interface.

Exact source diff:

```text
 RangeSetBlaze/AlgoC.lean | 75 ------------------------------------------------
 1 file changed, 75 deletions(-)
```

## Identity and evidence

- Baseline corrected-v2 artifact: `metrics/phase1-dead-delete-extra-nrs-splice-chain-v2.json`
- Baseline source manifest SHA-256: `0442ea2dd685165583d50fd2528203083dbd1f1bd3b7f97eb3fbcdc4a21a81bb`
- Baseline manifest check: every entry matched the current pre-edit HEAD source bytes exactly.
- Current corrected-v2 artifact: `metrics/phase1-dead-chain-replace-suffix-same-lo-v2.json`
- Current source manifest SHA-256: `88cf968bb40b774c7ed594ab789da9902476e9e8135af94ac195d3108acfcdb0`
- Collector: `scripts/phase0_metrics.py`, version 2; SHA-256 `4db7973927010a84c2b69cf1eb02d81703050c2a7e5c9ac7a51cb125c12a6ef5`
- Current artifact SHA-256: `63f9224ae79df3bfd26bbac0408692f097cdb5feaaf1e56ae5e360dd6ec2c20b`
- The JSON parses successfully and its metrics, manifest entries, and manifest hash match a fresh collector run on the post-edit working tree.

## Commands and results

| Command | Exit | Result |
|---|---:|---|
| `git diff --check` | 0 | Passed. |
| `/home/carlk/.elan/bin/lake build` | 0 | Completed successfully (1876 jobs). |
| `/home/carlk/.elan/bin/lake env lean RangeSetBlaze/AlgoC.lean` | 0 | Direct compilation succeeded with no output. |
| `python3 scripts/test_phase0_metrics.py` | 0 | 3 tests passed. |
| comment-aware integrity scan | 0 | No active `sorry`, `admit`, `axiom`, or `unsafe`; no active source axiom declarations. |
| temporary `#print axioms RangeSetBlaze.internalAddC_toSet` | 0 | Exact output below. |
| corrected-v2 collector | 0 | JSON written and independently compared with the evidence artifact. |

`lake build` emitted one pre-existing linter warning:
`RangeSetBlaze/AlgoB.lean:465:8: try 'simp' instead of 'simpa'`.
The `Main.lean:52–56` lines were expected informational values, not warnings.
No new or unexplained source warnings appeared. Direct compilation was silent.

Exact axiom output:

```text
'RangeSetBlaze.internalAddC_toSet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` dependency was present.

## Corrected-v2 metric deltas

Comparison is against `metrics/phase1-dead-delete-extra-nrs-splice-chain-v2.json`.

| Metric | Baseline | Current | Delta |
|---|---:|---:|---:|
| Algo C physical LOC | 2861 | 2786 | -75 |
| Algo C nonblank LOC | 2637 | 2568 | -69 |
| Algo C blank LOC | 224 | 218 | -6 |
| Algo C comment-only LOC | 983 | 968 | -15 |
| Algo C active-code LOC | 1654 | 1600 | -54 |
| Algo C definitions | 10 | 10 | 0 |
| Algo C lemma/theorem declarations | 27 | 26 | -1 |
| Algo C private lemma/theorem declarations | 21 | 20 | -1 |
| Repository physical LOC | 4332 | 4257 | -75 |
| Repository nonblank LOC | 3981 | 3912 | -69 |
| Repository blank LOC | 351 | 345 | -6 |
| Repository comment-only LOC | 1058 | 1043 | -15 |
| Repository active-code LOC | 2923 | 2869 | -54 |
| Repository definitions | 52 | 52 | 0 |
| Repository lemma/theorem declarations | 62 | 61 | -1 |
| Repository private lemma/theorem declarations | 25 | 24 | -1 |
| `by_cases` | 23 | 23 | 0 |
| `cases` | 68 | 64 | -4 |
| `have` | 624 | 616 | -8 |
| `linarith` | 12 | 12 | 0 |
| `omega` | 11 | 11 | 0 |
| `rw` | 158 | 152 | -6 |
| `simp` | 253 | 243 | -10 |
| `simpa` | 81 | 81 | 0 |

The active-proof reduction is exactly 54 LOC. Physical, blank, and comment-only
reductions are reported separately and are not presented as proof compression.

## Protected executable definitions

Raw declaration-span hashes and byte lengths matched HEAD exactly:

| Definition | Bytes | SHA-256 |
|---|---:|---|
| `deleteExtraNRs_loop` | 1618 | `8643dd508d2a4de3e723959fff187b54801358d275f418317dc4f212d1f4cd30` |
| `deleteExtraNRs` | 636 | `c193de7b55fca0240df1732875d90be36705b56c885b2d5b0b93ebab63ddbd7a` |
| `internalAdd2NRs` | 608 | `3549e490302f47e8bc705593160ba542ad893ea5cd397c86661c31743da5776c` |
| `internalAddC_extendPrev_safe` | 9348 | `da5bd3dac0a43b8ab9c07dfd89c6db696c48c872a27b327b3805caddcc61fd6f` |
| `internalAddC` | 2468 | `d18e87349fcc0ec457b956f4b437142b2867646282a63c43d590d828627bd492` |

## Active public theorem statements

Comment-aware declaration statement extraction through `:=` found the same six
active public declarations before and after deletion. All statement hashes were
identical:

| Declaration | SHA-256 |
|---|---|
| `deleteExtraNRs_loop_sets` | `c663dfa28d00524a015bf5f4eb0861d206fbe9d94703e129128a0696f534281d` |
| `getLast?_eq_some_getLast` | `8e56f5da854d60c60213fc4c4206f2c9a2669f0dcf5e0e55dee1e1d078b452a8` |
| `internalAdd2_safe_from_le_toSet` | `d394daccf1e291371e78839e69a514a3712e3f3360510c981101ef8b18721e08` |
| `internalAdd2_safe_toSet` | `42120b69394c052213adc4652afae570984068dc8d0aaf420d256e219d1e2c2c` |
| `internalAddC_extendPrev_safe_toSet` | `a6c97bc913331ba14e77745d672b9fb86fab79dd3aa93291cd4824ff5cca8511` |
| `internalAddC_toSet` | `6b5d4bfb075ff8726e11bfc3f6609b769d1f27f11d0839d7763612618558ff39` |

## Final Git status

```text
 M RangeSetBlaze/AlgoC.lean
?? metrics/phase1-dead-chain-replace-suffix-same-lo-v2.json
?? metrics/phase1-dead-chain-replace-suffix-same-lo-v2.md
```
