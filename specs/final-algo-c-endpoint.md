# Final Algo C endpoint audit

This report supersedes `phase3-proof-architecture-endpoint.md` for the
post-inference source. It records the final preservation baseline after the
inference Keeps and does not authorize another proof-compression campaign.

## Repository identity and verification

- Branch: `main`; exact HEAD: `f30ea2200896eeac54d9280c114ecc3c76f6fb74`
- HEAD: `Use direct dropLast membership theorem`, 2026-09-10 16:15:05 -0700
- Working tree at audit start: clean; synchronized with `origin/main`
- Lean: `leanprover/lean4:v4.33.1`, Lean commit
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`
- Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`
- Metrics: collector/schema v3; collector SHA-256
  `a07fc3573ed0134219b1d539c2684d717707ab7360a8e0ba97602ef95549e048`
- Current Lean-source manifest SHA-256:
  `41b18f063824b1877eaf6e5ebb3f04efa1fe0ce9e464d1d6c346eaa888bfe5f2`
- Current `RangeSetBlaze/AlgoC.lean` SHA-256:
  `faaabfec830577667be44fbda06d009183b00e35fc65665eab7c2030b3ab8b9c`

Relevant final inference commits, newest first, are `f30ea22` (direct
`dropLast` membership theorem), `a9f57a0` (covered subset proof), `06a1513`
(`omega` for interval union), and `7505d55` (safe insertion set proof).
The Phase 3 source endpoint remains `ddd1b494`; the pre-inference comparison
point is `34fbcc2`, the documentation/stabilization commit immediately before
those inference Keeps.

`lake build` succeeds. It emits the pre-existing warning at
`RangeSetBlaze/AlgoB.lean:465` recommending `simp` instead of `simpa`, plus
the expected `Main.lean` informational output. Direct compilation of
`RangeSetBlaze/AlgoC.lean` succeeds with no output. No active `sorry`, `admit`,
unsafe proof shortcut, or source axiom was found; the recorded theorem axiom
set remains `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

## Final v3 metrics

The collector is comment-aware and counts exact active syntax tokens. `simp`
includes `simp only`; `simpa` is separate. No composite score is used.

### Algo C

| Category | Metric | Final |
|---|---|---:|
| Size | physical LOC | 942 |
| Size | active LOC | 777 |
| Size | comment-only LOC | 101 |
| API | private lemma/theorem declarations | 11 |
| API | public lemma/theorem declarations | 6 |
| Branching | `cases` / `by_cases` / `induction` | 6 / 5 / 3 |
| Plumbing | `have` / `show` / `suffices` / `rw` | 133 / 3 / 0 / 41 |
| Automation | `simp` / `simpa` / `omega` / `linarith` / `grind` | 50 / 27 / 5 / 0 / 0 |
| Representation | `List.span` / `takeWhile` / `dropWhile` | 22 / 24 / 7 |
| Representation | `getLast?` / `dropLast` | 8 / 2 |
| Representation | `pairwise_append` / `Sublist` | 6 / 2 |

### Repository totals

| Category | Metric | Final |
|---|---|---:|
| Size | physical LOC / active LOC / comment-only LOC | 2429 / 2057 / 179 |
| API | definitions and abbreviations | 52 |
| API | lemma/theorem declarations | 68 |
| API | private / public lemma-theorem declarations | 21 / 47 |
| Branching | `cases` / `by_cases` / `induction` | 34 / 12 / 10 |
| Plumbing | `have` / `show` / `suffices` / `rw` | 356 / 3 / 0 / 43 |
| Automation | `simp` / `simpa` / `omega` / `linarith` / `grind` | 137 / 94 / 5 / 9 / 0 |
| Representation | `List.span` / `takeWhile` / `dropWhile` | 22 / 24 / 7 |
| Representation | `getLast?` / `dropLast` | 9 / 2 |
| Representation | `pairwise_append` / `Sublist` | 15 / 2 |

### Comparison

Historical values below were regenerated with the current v3 collector from
the exact refs. The Phase 0 Markdown artifact contains older comment-only
figures, so its historical values should not be mixed with this table.

| Algo C metric | Phase 0 `5bcfce5` | Phase 3 `ddd1b49` | Pre-inference `34fbcc2` | Final | Final vs Phase 0 |
|---|---:|---:|---:|---:|---:|
| physical LOC | 3320 | 969 | 1005 | 942 | -2378 (-71.6%) |
| active LOC | 1983 | 828 | 828 | 777 | -1206 (-60.8%) |
| comment-only LOC | 1076 | 80 | 113 | 101 | -975 (-90.6%) |
| private declarations | 36 | 17 | 17 | 11 | -25 (-69.4%) |
| public declarations | 6 | 6 | 6 | 6 | 0 |
| `cases` | 56 | 6 | 6 | 6 | -50 (-89.3%) |
| `by_cases` | 17 | 6 | 6 | 5 | -12 (-70.6%) |
| `induction` | 23 | 3 | 3 | 3 | -20 (-87.0%) |
| `have` | 471 | 151 | 151 | 133 | -338 (-71.8%) |
| `show` | 8 | 3 | 3 | 3 | -5 (-62.5%) |
| `suffices` | 1 | 0 | 0 | 0 | -1 (-100%) |
| `rw` | 172 | 45 | 45 | 41 | -131 (-76.2%) |
| `simp` | 203 | 53 | 53 | 50 | -153 (-75.4%) |
| `simpa` | 18 | 25 | 25 | 27 | +9 (+50.0%) |
| `omega` | 15 | 4 | 4 | 5 | -10 (-66.7%) |
| `linarith` | 3 | 0 | 0 | 0 | -3 (-100%) |
| `grind` | 0 | 0 | 0 | 0 | 0 |
| `List.span` | 44 | 22 | 22 | 22 | -22 (-50.0%) |
| `takeWhile` | 81 | 24 | 24 | 24 | -57 (-70.4%) |
| `dropWhile` | 66 | 7 | 7 | 7 | -59 (-89.4%) |
| `getLast?` | 7 | 8 | 8 | 8 | +1 (+14.3%) |
| `dropLast` | 10 | 5 | 5 | 2 | -8 (-80.0%) |
| `pairwise_append` | 4 | 6 | 6 | 6 | +2 (+50.0%) |
| `Sublist` | 0 | 2 | 2 | 2 | +2 |

The inference pass changed active Algo C size from 828 to 777 (-51, -6.2%),
`have` from 151 to 133 (-11.9%), `rw` from 45 to 41 (-8.9%), `by_cases` from
6 to 5, `simp` from 53 to 50, and increased `simpa` from 25 to 27 and `omega`
from 4 to 5. The representation counts are unchanged except for `dropLast`
(5 to 2). These are implementation shifts, not a new architecture.

## Final proof architecture

The semantic contracts are the central reusable units. The unified
`deleteExtraNRs_loop_preserves_order_lower_bound_and_union` contract replaces
separate recursive proofs of ordering, the lower-bound invariant, and set
preservation. `internalAdd2NRs_preserves_order_and_union` replaces separate
insertion ordering and union proof paths. `extend_predecessor_preserves_order_and_union`
shares the extend branch's split, predecessor, pairwise, loop, and set facts
between the safe wrapper and its correctness theorem.

The mathematical bridges isolate genuine mismatches:
- `nonstrict_start_gap_implies_strict_start_gap` converts the `≤ start`
  predecessor split to the `< start` insertion split only under the separated
  gap hypothesis.
- `strict_start_split_suffix_lower_bound` turns the strict split and pairwise
  ordering into the lower-bound fact required by the forward merge scan.

`NR.before` is the single ordering vocabulary in this area. The former
`loLE`/`IsChain loLE` translation layer is gone. Split, predecessor, and
pairwise evidence is kept alive long enough for all consumers, instead of
being repeatedly reconstructed.

The current named-proof inventory is compact: the merge contract is declared
at line 225 and used by the public set projection plus the insertion and
extend proofs; the strict suffix bound is declared at line 200 and consumed
by the insertion contract; the insertion contract is declared at line 383 and
used by both safe-insertion set proofs; the non-strict-to-strict bridge is
declared at line 515 and used by `internalAdd2_safe_from_le`; the optional-last
predecessor helper is at line 570 and is used by the extend contract and the
covered branch; and the extend contract is at line 623 and is used by both
the safe wrapper and its public set theorem. This is the intended current
call/use-site shape, not a proposed new abstraction.

The final local implementation wins are deliberately narrow: direct semantic
theorem composition with focused `simpa`, narrow `omega` for interval facts,
and `List.mem_dropLast_of_mem_of_ne_getLast` for the last-element case. The
proof does not adopt `grind`, `aesop`, broad `simp`, or opaque monolithic
automation.

## Remaining complexity

The largest remaining clusters are ranked as follows.

1. `deleteExtraNRs_loop_preserves_order_lower_bound_and_union` — primarily
   intrinsic algorithmic complexity, with necessary representation plumbing.
   Its induction follows the recursive forward merge scan and must handle
   both merge and first-gap exits while preserving three coupled guarantees.
2. `extend_predecessor_preserves_order_and_union` and its wrapper boundary —
   primarily necessary specification-boundary and representation-modeling
   complexity. Removing the predecessor from `before`, extending it, and
   reassembling the list are facts specific to the production-shaped path.
3. `strict_start_split_suffix_lower_bound` — primarily necessary
   representation modeling. Its induction traverses `dropWhile` after a
   strict `span`; it is structurally different from the merge induction.
4. `internalAddC_toSet` — primarily necessary specification-boundary
   complexity. It mirrors the executable branches, with only the covered case
   proving a local subset argument.

The three remaining inductions are therefore not consolidation opportunities:
the merge induction recurses over pending ranges and carries a semantic
contract; the strict-suffix induction recurses over the source list to expose
the first nonmatching predicate; and the loop contract is consumed by separate
insertion and extension clients. Their distinct recursion measures and
invariants make further unification unjustified.

The remaining list operations classify as follows:

- `List.span`: essential to the production-shaped predecessor and insertion
  splits.
- `takeWhile`/`dropWhile`: harmless local proof machinery used to expose and
  reconstruct `span`; only the explicit final conversion is a possible
  presentation cleanup.
- `getLast?`: essential to predecessor selection.
- `dropLast`: essential to removing the predecessor before replacement; the
  membership proof is now using the current Mathlib theorem directly.
- `pairwise_append` and `Sublist`: ordinary, focused library vocabulary, not
  maintenance debt.

## Narrow maintenance debt

`algoCListSet` and `algoCListSet_eq_foldr` remain the clearest cleanup item:
they are a private local fold and a definitional bridge duplicating the list
set views in `Basic` and Algo B. Classify them as worth later cleanup but
compatibility-sensitive in the short term, because a common fold would move
proof vocabulary across module boundaries. Do not refactor them as part of
this endpoint.

`start_split_predecessor_le_and_mem` is a one-use representation helper, but
its current `span`/`takeWhile` transport is clear and uses appropriate narrow
library facts; leave it alone. The public compatibility wrappers are retained
because their theorem statements form the existing public surface even where
repository-local callers are sparse. Stale historical comments and disabled
proof blocks were removed earlier; no active comment currently describes the
removed helpers. These items are harmless or compatibility-sensitive, not
architectural debt.

## Documentation consistency and preservation rules

The `AlgoC.lean` module documentation matches the final architecture: it
documents the production branches, the three semantic contracts, the strict
versus non-strict bridge, and the representation role of `span`, `getLast?`,
and `dropLast`. The Phase 3 report remains historically accurate for its own
commit but is superseded here because the inference pass changed current
metrics. `AGENTS.md` now names the v3 collector and preserves the Phase 4
stabilization boundary. No document should treat the old Phase 0 stale
comment counts as current v3 values.

Future cursor-based or `RangeMapBlaze` work should preserve: production branch
correspondence; semantic contracts that combine guarantees sharing an
induction; `NR.before` as the ordering relation; evidence lifetime across
split/predecessor/pairwise consumers; and narrow mathematical bridges at
specification boundaries. Cursor/map abstractions should be introduced only
when they represent a stable semantic object, not to hide current list proof
state.
