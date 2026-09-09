# Phase 1: replace the local `pairwise_append` helper

Collected 2026-09-09 in `/home/carlk/programs/range-set-blaze-lean2` as an
uncommitted, independently reviewable proof-refactoring step.

## Identity

- Immediately preceding v2 artifact: `metrics/phase1-pairwise-append-cross-v2.json`
- Immediately preceding source commit: `76cf557b9f2f89e7e3c8c03c659ebe0c59938a8a`
- Current v2 artifact: `metrics/phase1-pairwise-append-local-v2.json`
- Collector: `scripts/phase0_metrics.py`, version 2
- Collector SHA-256: `4db7973927010a84c2b69cf1eb02d81703050c2a7e5c9ac7a51cb125c12a6ef5`
- Preceding source manifest SHA-256: `de824b9f2a055f69db89ad59d99d588123ada56078172cfe2cb11d92a7376dd0`
- Current source manifest SHA-256: `ed7cb028186d1f55b86032331846e576fc1b1daf0e10c36a26678ac87a489366`
- Current `RangeSetBlaze/AlgoC.lean` SHA-256: `dfa56ac09a0ebf245a039a2160af183cbe4dce3aa5bc6a554467cf7b9d824228`
- Current proof-source patch SHA-256 (`git diff --binary`): `2a3eab2a9eed0c9b20533d59aaf05b0b8b2ac6318dfb4848ac2d11286f6cb4f1`

## Exact source change

Only `RangeSetBlaze/AlgoC.lean` changed in the proof source:

- Deleted only private local lemma `pairwise_append` (21 physical lines).
- Replaced its three active uses with `List.pairwise_append.mpr`:
  `exact List.pairwise_append.mpr ⟨hpw_before, hpw_result, hcross⟩`,
  `exact List.pairwise_append.mpr ⟨hpw_init, hpw_res, hcross⟩`, and
  `refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩` at `ok_deleteExtraNRs`,
  retaining its three existing bullets in order.
- The diff is exactly 3 insertions and 25 deletions. No theorem statement,
  executable definition, neighboring helper, disabled historical proof text,
  algorithm condition, unrelated comment, or unrelated formatting was changed.

## Verification

| Command | Exit | Result |
|---|---:|---|
| `git diff --check` | 0 | Passed. |
| `lake build` | 0 | Build completed successfully (1874 jobs). |
| `lake env lean RangeSetBlaze/AlgoC.lean` | 0 | Direct compilation succeeded with no output. |
| `python3 scripts/test_phase0_metrics.py` | 0 | 3 tests passed. |
| `python3 scripts/phase0_metrics.py -o metrics/phase1-pairwise-append-local-v2.json` | 0 | Corrected-v2 artifact written. |
| `lake env lean /tmp/range-set-blaze-phase1-local-axioms.lean` | 0 | Axiom result recorded below. |

The aggregate build emitted only the pre-existing warning:

```text
warning: RangeSetBlaze/AlgoB.lean:465:8: try 'simp' instead of 'simpa'
```

It also emitted the five expected informational values from `Main.lean`; no
new or unexplained warning occurred.

The standard raw integrity search:

```text
rg -n --glob '*.lean' --glob '!*.lake/**' --glob '!**/generated/**' --glob '!**/vendor/**' '\b(sorry|unsafe)\b' . || true
```

found only the three known inactive opening-comment matches at AlgoC lines
14, 40, and 54. The comment-aware integrity scan reported:

```text
active sorry: False
active admit: False
active axiom: False
active unsafe: False
active axiom declarations: []
```

The elaborated axiom query returned exactly:

```text
'RangeSetBlaze.internalAddC_toSet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` dependency, and the axiom set is unchanged from the
preceding v2 state.

## Corrected-v2 metric comparison

Comparison is against the immediately preceding corrected-v2 artifact,
`metrics/phase1-pairwise-append-cross-v2.json`.

| Metric | preceding v2 | this v2 | delta |
|---|---:|---:|---:|
| Algo C physical LOC | 3286 | 3264 | -22 |
| Algo C nonblank LOC | 3027 | 3006 | -21 |
| Algo C blank LOC | 259 | 258 | -1 |
| Algo C comment-only LOC | 1073 | 1071 | -2 |
| Algo C active-code LOC | 1954 | 1935 | -19 |
| Algo C definitions | 10 | 10 | 0 |
| Algo C lemma/theorem declarations | 34 | 33 | -1 |
| Algo C private lemma/theorem declarations | 28 | 27 | -1 |
| Repository physical LOC | 4757 | 4735 | -22 |
| Repository nonblank LOC | 4371 | 4350 | -21 |
| Repository blank LOC | 386 | 385 | -1 |
| Repository comment-only LOC | 1148 | 1146 | -2 |
| Repository active-code LOC | 3223 | 3204 | -19 |
| Repository definitions | 52 | 52 | 0 |
| Repository lemma/theorem declarations | 69 | 68 | -1 |
| Repository private lemma/theorem declarations | 32 | 31 | -1 |
| `simp` tokens | 286 | 283 | -3 |
| `cases` tokens | 81 | 79 | -2 |
| `rw` tokens | 173 | 173 | 0 |

All other corrected-v2 lexical token totals are unchanged (`simpa`, `have`,
`linarith`, `omega`, `grind`, and `by_cases`). The measured deltas exactly
match the requested prediction.

## Protected footprint and theorem validation

The exact diff contains only the one private proof-helper deletion and the
three proof-term replacements. The production-shaped behavior in
`deleteExtraNRs_loop`, `deleteExtraNRs`, `internalAdd2NRs`,
`internalAddC_extendPrev_safe`, and `internalAddC` is unchanged, including
empty-input handling, the `lo ≤ start` split, predecessor gap/coverage/touching
branches, the `next.lo ≤ current.hi + 1` merge condition, lower-endpoint
preservation, and `max` upper-endpoint behavior. The
`internalAddC_toSet` theorem statement matches the preceding source exactly.

## Git status

```text
 M RangeSetBlaze/AlgoC.lean
?? metrics/phase1-pairwise-append-local-v2.json
?? metrics/phase1-pairwise-append-local-v2.md
```

No commit, tag, push, or staging was performed.
