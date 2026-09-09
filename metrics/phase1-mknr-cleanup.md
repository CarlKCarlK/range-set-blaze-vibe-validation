# Phase 1: remove unused `mkNR'`

Collected 2026-09-09 in `/home/carlk/programs/range-set-blaze-lean2`. This is an
uncommitted, independently reviewable Phase 1 proof-refactoring step.

## Identity

- Base commit: `54893d0f953596b87471b4f74d20e94eefc3726b`
- Base commit tree: `c5fa8ab351e804538113b8454fdb417b030d3b18`
- Branch/upstream before the edit: `main...origin/main`
- Base `RangeSetBlaze/AlgoC.lean` blob: `5052c163fe185ee27491de0b3026699ef0fd617d`
- Post-edit `RangeSetBlaze/AlgoC.lean` blob: `908cde5a1dbf13e4461d22aa160ac2b55a23ab2d`
- Post-edit `RangeSetBlaze/AlgoC.lean` SHA-256:
  `1806fddf67614747571a81b06391e641e9ff2d2ad645b502c1a76a876ddcc2fb`
- Exact proof-source patch SHA-256: `e20782d5b2c2ae7d4c41f445a57a145cfcd33dab7c53fdd0f4bedc5e81658233`
- Frozen collector SHA-256:
  `e848f705d9f221c4b24af3a12f113dd191974ec995595e120f2ea0245dc5833a`
- Frozen baseline JSON SHA-256:
  `9168e4c5444d26bc00f3b16a370dabd724b78ff097ce736e64cce8e46d2fea91`
- Frozen post-change JSON SHA-256:
  `f4f98da42f21bc30b0d6d2d41302c97c7dc95bcd61a0dbfbf96d6ab0879d0c31`

The base commit plus the exact proof-source patch identifies the uncommitted
proof-source tree. The metrics artifacts themselves are not included in that
patch hash. No commit, push, or tag was created.

## Exact source change

```diff
-/-- Pack endpoints as a nonempty range. -/
-private def mkNR' (lo hi : Int) (h : lo ≤ hi) : NR :=
-  ⟨{ lo := lo, hi := hi }, h⟩
```

`git diff --check` succeeded. No other proof-source line changed.

## Verification

Commands were rerun on 2026-09-09 at approximately 06:58 PDT.

| Command | Exit | Elapsed | Result |
|---|---:|---:|---|
| `lake build` | 0 | 0.96 s | Warm replay; build completed successfully (1874 jobs). |
| `lake env lean RangeSetBlaze/AlgoC.lean` | 0 | 3.06 s | Warm direct compilation; no Lean output. |
| temporary `#print axioms RangeSetBlaze.internalAddC_toSet` | 0 | not retained | Axiom set unchanged. |
| `python3 scripts/phase0_metrics.py` | 0 | not retained | Exact output stored in `phase1-mknr-cleanup.json`. |

The aggregate build emitted the pre-existing linter warning:

```text
warning: RangeSetBlaze/AlgoB.lean:465:8: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
```

It also emitted the five expected `Main.lean` informational values recorded in
the Phase 0 baseline. There were no new or unexplained warnings.

The raw integrity search found only the three known inactive matches in Algo C's
opening block comment: `unsafe` at lines 14 and 54 and `sorry` at line 40. It
found no `admit` or source `axiom`. There is no active `sorry`, `admit`, `axiom`,
or `unsafe` proof shortcut.

The elaborated axiom result was exactly:

```text
'RangeSetBlaze.internalAddC_toSet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` dependency.

## Metrics

The frozen collector's exact output is `phase1-mknr-cleanup.json`. Against
`specs/lean-proof-refactoring-baseline.json`, it reports:

| Metric | Phase 0 | Post-change | Delta |
|---|---:|---:|---:|
| Algo C physical LOC | 3,320 | 3,317 | -3 |
| Algo C nonblank LOC | 3,059 | 3,056 | -3 |
| Algo C blank LOC | 261 | 261 | 0 |
| Algo C comment-only LOC (collector) | 866 | 864 | -2 |
| Algo C active-code LOC (collector) | 2,193 | 2,192 | -1 |
| Algo C definitions | 11 | 10 | -1 |
| Algo C `have` tokens (collector) | 503 | 505 | +2 |
| Repository physical LOC | 4,791 | 4,788 | -3 |
| Repository nonblank LOC | 4,403 | 4,400 | -3 |
| Repository comment-only LOC (collector) | 901 | 899 | -2 |
| Repository active-code LOC (collector) | 3,502 | 3,501 | -1 |
| Repository definitions | 53 | 52 | -1 |

All other collector token counts are unchanged.

The exact deletion is one comment-only line and two active-code lines, and it
contains no `have` token. The semantic deltas are therefore comment-only `-1`,
active-code `-2`, and every tactic token `0`. The inconsistent frozen-collector
deltas above are retained verbatim for reproducibility and explained below.

## Frozen collector defect

`scripts/phase0_metrics.py` treats every apostrophe outside a comment or string
as the start of a character literal. In Lean, apostrophes are also valid inside
identifiers. At `mkNR'`, the Phase 0 scanner entered `in_char` state and did not
leave it until a later apostrophe. Removing the identifier therefore changes how
later unchanged text is classified, producing the false comment/active split and
the false `have +2` delta.

This defect does not affect physical LOC, blank LOC, nonblank LOC, or the
definition count for this edit. It does affect the reliability of comment-only,
active-code, and token counts in any snapshot containing identifier primes.
The frozen collector and frozen Phase 0 JSON were deliberately not changed as
part of this proof refactoring.

## Algorithm footprint

The protected bodies `deleteExtraNRs_loop`, `deleteExtraNRs`, `internalAdd2NRs`,
`internalAddC_extendPrev_safe`, and `internalAddC` are textually unchanged. The
statement of `internalAddC_toSet` remains exactly
`(internalAddC s r).toSet = s.toSet ∪ r.toSet`.

The deleted private `mkNR'` was an executable-capable but unused definition. No
referenced or retained executable definition changed. `mkNR`, all computational
endpoints, branch structure, scan conditions, and merge behavior are unchanged.

## Tooling follow-up (not implemented)

Repairing apostrophe handling is a separate tooling-only change. It must not be
mixed with this proof-source refactoring or silently overwrite the frozen Phase 0
artifacts. After repair, generate a new, versioned metric series for both the
base snapshot and this post-change snapshot, retaining the frozen series beside
it so comparisons remain auditable.
