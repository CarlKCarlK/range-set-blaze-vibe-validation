# Phase 1: replace `mem_takeWhile_satisfies` with `List.mem_takeWhile_imp`

Collected 2026-09-09 in `/home/carlk/programs/range-set-blaze-lean2` as an
uncommitted, independently reviewed Phase 1 proof-refactoring step.

## Identity

- Immediately preceding v2 artifact: `metrics/phase1-pairwise-append-local-v2.json`
- Immediately preceding source commit: `a5ba71d` (`Use List.pairwise_append constructor`)
- Current v2 artifact: `metrics/phase1-mem-takewhile-imp-v2.json`
- Collector: `scripts/phase0_metrics.py`, version 2
- Collector SHA-256: `4db7973927010a84c2b69cf1eb02d81703050c2a7e5c9ac7a51cb125c12a6ef5`
- Current `RangeSetBlaze/AlgoC.lean` SHA-256: `f6d4e17f04e364308583a1184da88d1e92eafade4704f983fe6f3f50840c5e7a`
- Current proof-source patch SHA-256 (`git diff --binary`): `35782db99c0f4486da9b1e7d981a61faa83c75f372bf110cf761875889dc1017`

## Exact source change

Only `RangeSetBlaze/AlgoC.lean` changed:

- Added the narrow explicit import `Mathlib.Data.List.TakeWhile`.
- Deleted private `mem_takeWhile_satisfies` and its proof body.
- Replaced exactly eight active uses with `List.mem_takeWhile_imp`, passing
  only the local membership hypothesis.
- The two disabled historical occurrences remain unchanged at the current
  source lines 2550 and 3204.
- No other import, executable definition, theorem statement, neighboring
  helper, branch, algorithm condition, or unrelated comment was changed.

The source diff is 9 insertions and 21 deletions. The active replacement lines
are 878, 1030, 1301, 1507, 1834, 1926, 2306, and 3006.

## Verification

| Command | Exit | Result |
|---|---:|---|
| `git diff --check` | 0 | Passed. |
| `lake build` | 0 | Build completed successfully (1876 jobs). |
| `lake env lean RangeSetBlaze/AlgoC.lean` | 0 | Direct compilation succeeded with no output. |
| `python3 scripts/test_phase0_metrics.py` | 0 | 3 tests passed. |
| `python3 scripts/phase0_metrics.py -o metrics/phase1-mem-takewhile-imp-v2.json` | 0 | Corrected-v2 artifact written. |
| `lake env lean /tmp/range-set-blaze-mem-takewhile-review-axioms.lean` | 0 | Axiom result recorded below. |

The aggregate build also emitted the pre-existing warning in `AlgoB.lean:465`
(`try 'simp' instead of 'simpa'`) and the five expected informational values
from `Main.lean`. No new or unexplained warning occurred. The source's known
opening inactive-comment matches remain the only raw `sorry`/`unsafe` matches;
the comment-aware integrity scan reports no active `sorry`, `admit`, `axiom`,
or `unsafe`, and no source axiom declarations.

The elaborated axiom query returned:

```text
'RangeSetBlaze.internalAddC_toSet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Corrected-v2 metric comparison

Comparison is against `metrics/phase1-pairwise-append-local-v2.json`.

| Metric | preceding v2 | this v2 | delta |
|---|---:|---:|---:|
| Algo C physical LOC | 3264 | 3252 | -12 |
| Algo C nonblank LOC | 3006 | 2995 | -11 |
| Algo C blank LOC | 258 | 257 | -1 |
| Algo C comment-only LOC | 1071 | 1071 | 0 |
| Algo C active-code LOC | 1935 | 1924 | -11 |
| Algo C definitions | 10 | 10 | 0 |
| Algo C lemma/theorem declarations | 33 | 32 | -1 |
| Algo C private lemma/theorem declarations | 27 | 26 | -1 |
| Repository physical LOC | 4735 | 4723 | -12 |
| Repository nonblank LOC | 4350 | 4339 | -11 |
| Repository blank LOC | 385 | 384 | -1 |
| Repository comment-only LOC | 1146 | 1146 | 0 |
| Repository active-code LOC | 3204 | 3193 | -11 |
| Repository definitions | 52 | 52 | 0 |
| Repository lemma/theorem declarations | 68 | 67 | -1 |
| Repository private lemma/theorem declarations | 31 | 30 | -1 |
| `simp` tokens | 283 | 281 | -2 |
| `cases` tokens | 79 | 76 | -3 |

All other corrected-v2 lexical token totals are unchanged (`simpa`, `have`,
`rw`, `linarith`, `omega`, `grind`, and `by_cases`).

## Protected footprint and status

The exact source diff contains only the explicit TakeWhile import, the requested
helper deletion, and eight proof-term substitutions. Protected executable
definitions and their branch structure are unchanged, as is the exact
`internalAddC_toSet` theorem statement. No direct call was materially less
readable than its surrounding proof.

Current status:

```text
 M RangeSetBlaze/AlgoC.lean
?? metrics/phase1-mem-takewhile-imp-v2.json
?? metrics/phase1-mem-takewhile-imp-v2.md
```

No commit, tag, push, or staging was performed.
