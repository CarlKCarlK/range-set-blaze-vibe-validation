# Current proof-complexity dashboard

This report was collected with schema v3 from the Lean source bytes at
`3eb53fbdbd59d6ab4809c9e6b4c7e2aa99e29076`. The working tree has no Lean
source changes, so those bytes are exactly the current post-Phase-2 source.
The complete machine-readable result is `metrics/current-dashboard-v3.json`.

There is no single Lean equivalent of McCabe cyclomatic complexity. Explicit
case splits and inductions are useful analogues, but elaboration and automation
can create or hide proof alternatives. The headline view therefore combines
size, visible proof branching, and intermediate proof plumbing without
combining them into a score. Automation, representation exposure, and API
shape remain separate supporting evidence.

## Current dashboard

| Category | Metric | Algo C | Repository |
|---|---|---:|---:|
| Size | Physical LOC | 1,486 | 2,973 |
| Size | Nonblank LOC | 1,367 | 2,725 |
| Size | Comment-only LOC | 194 | 272 |
| Size | Active-code LOC | 1,173 | 2,453 |
| Branching | `cases` | 15 | 43 |
| Branching | `by_cases` | 9 | 16 |
| Branching | `induction` | 5 | 12 |
| Plumbing | `have` | 277 | 500 |
| Plumbing | `show` | 7 | 7 |
| Plumbing | `suffices` | 1 | 1 |
| Plumbing | `rw` | 93 | 95 |
| Automation | `simp` | 100 | 187 |
| Automation | `simpa` | 23 | 90 |
| Automation | `omega` | 5 | 5 |
| Automation | `linarith` | 0 | 9 |
| Automation | `grind` | 0 | 0 |
| Representation | `takeWhile` | 47 | 47 |
| Representation | `dropWhile` | 23 | 23 |
| Representation | `getLast?` | 6 | 7 |
| Representation | `dropLast` | 8 | 8 |
| Representation | `pairwise_append` | 7 | 16 |
| Representation | `Sublist` | 2 | 2 |
| Representation | qualified `List.span` | 39 | 39 |
| API shape | Definitions + abbreviations | 11 | 53 |
| API shape | Lemma/theorem declarations | 27 | 72 |
| API shape | Private lemma/theorem declarations | 21 | 25 |
| API shape | Public lemma/theorem declarations | 6 | 47 |

## Reconstructed history

The same v3 collector was run with `--git-ref` against:

- Phase 0: `54893d0f953596b87471b4f74d20e94eefc3726b`
- Phase 1 endpoint: `e4ab63b` (module documentation cleanup, immediately
  before the Phase 2 commits)
- Current post-Phase-2: `3eb53fb`

| Signal | Phase 0 | Phase 1 | Current |
|---|---:|---:|---:|
| Algo C active-code LOC | 1,983 | 1,488 | 1,173 |
| Repository active-code LOC | 3,252 | 2,757 | 2,453 |
| Algo C `cases` / `by_cases` / `induction` | 56 / 17 / 23 | 29 / 13 / 10 | 15 / 9 / 5 |
| Algo C `have` / `rw` | 471 / 172 | 377 / 141 | 277 / 93 |
| Algo C `simp` / `omega` / `linarith` | 203 / 15 / 3 | 140 / 9 / 2 | 100 / 5 / 0 |
| Algo C `takeWhile` / `dropWhile` | 81 / 66 | 64 / 55 | 47 / 23 |

The history shows reductions across several independent dimensions, rather
than LOC alone: explicit branching, intermediate plumbing, arithmetic
automation, and list-structure exposure all fell. The signals are not
monotonic requirements. For example, qualified `List.span` uses moved
44 → 37 → 39 while broader plumbing fell; a small increase can reflect a
clearer explicit abstraction boundary rather than regression.

Likewise, adding a reusable lemma can increase declaration counts while
improving the API, documentation can increase physical LOC without increasing
active proof complexity, and replacing a readable argument with one opaque
automation call is not automatically an improvement.

## Verification

- Collector regression tests: 6 passed.
- Repeated working-tree collection: byte-for-byte identical and identical to
  `current-dashboard-v3.json`.
- Repeated Phase 0 `--git-ref` collection: byte-for-byte identical.
- Corrected-v2 compatibility: all legacy per-file scalar/token fields and both
  legacy totals objects match `phase2-proof-api-naming-v2.json`.
- `git diff --check`: passed.
- `lake build`: passed (1 existing `AlgoB.lean` unnecessary-`simpa` warning).
- `lake env lean RangeSetBlaze/AlgoC.lean`: passed with no output.
- No Lean source file was changed, so the protected executable definitions and
  public theorem statements are unchanged.
- `#print axioms RangeSetBlaze.internalAddC_toSet` remains exactly
  `[propext, Classical.choice, Quot.sound]`; there is no `sorryAx`.
