# Canonical uniqueness audit

Date: 2026-09-13

## Baseline and scope

The work began from clean commit
`ed466d4c42b36866f9404504eecec4af97e11c8e`
(`Unify and simplify cached-length proofs`) on `main`, synchronized with
`origin/main`. The baseline tree was
`de23bcc1d709dcec3ce88d4217a9109f46599302`; its v3 Lean-source manifest was
`469febe84dd384d17553cdf7d8c63b74c5dd18caf9d629dd63bcdae0e8df7a18`.
The final working-tree Lean-source manifest is
`dc30c58687392d4beed0076e157ef379409790c17f4c88fe11cf1f0dfb496308`.

No executable algorithm, Rust source, or existing proof was changed. The only
change to `Basic.lean` is a module comment pointing to the new uniqueness
module. No commit, tag, or push was made.

## Public uniqueness API

`RangeSetBlaze/Canonical.lean` adds four public semantic theorems:

- `RangeSetBlaze.ranges_eq_of_canonical_of_rangesToSet_eq`: canonical raw
  range lists with equal `rangesToSet` denotations are equal;
- `RangeSetBlaze.ext`: packaged range sets with equal `toSet`
  denotations are equal;
- `RangeMapBlaze.runs_eq_of_canonical_of_runsToFunction_eq`: canonical raw run
  lists with equal `runsToFunction` denotations are equal;
- `RangeMapBlaze.ext`: packaged range maps with equal
  `toFunction` denotations are equal.

Both raw-list theorems are public because they state reusable representation
mathematics. The packaged corollaries are the stable client API: canonicality
comes from the structures, so callers supply only semantic equality.

The implementation is in a focused `Canonical` module rather than `Basic`.
This keeps the foundational definitions and elementary interval laws small
while making uniqueness available independently of all insertion algorithms.

## Set proof architecture

The set proof inducts on the two canonical lists. Nonemptiness of every stored
range rules out an empty/nonempty mismatch. For nonempty lists, membership of
the first lower endpoints and canonical lower bounds force equal starts.

If first upper endpoints differed, the integer immediately after the shorter
endpoint would be represented by the longer head. It is represented by neither
the shorter head nor its tail: the canonical `NR.before` relation leaves a
genuine integer gap. This forces equal endpoints and hence equal first ranges.
Canonical tail bounds then cancel the common head semantically, and induction
proves equality of the tails.

Four private helpers express only the needed list-denotation bounds:
`rangesToSet_lower_bound`, `rangesToSet_strict_lower_bound`, and two head/tail
canonical consequences. They remain local rather than expanding the shared
interval API.

## Map proof architecture

The map proof has the same outer induction. Equality at the least represented
key forces equal first lower endpoints and values. Endpoint equality uses the
key immediately after the shorter run.

At that key, a longer head returns its value. A shorter head no longer covers
the key. Its tail cannot return the same value there: a later equal-valued run
starting immediately would violate the genuine-gap clause of `Run.before`,
and a later start leaves the key unmapped. This is the exact point where map
maximality is essential.

After the first runs agree, whole-function equality gives tail equality
outside the head. Inside the head, canonical nonoverlap makes both tails
unmapped. Induction completes the proof. The theorem needs no
`DecidableEq Value`; it reasons from the canonical relation and semantic
function equality alone.

Three private map helpers retain lower-bound and next-key arguments locally.
No generic canonical-piece framework was introduced.

## Cross-algorithm theorem graph

`RangeSetBlaze/CrossAlgorithm.lean` uses one reference implementation per
family:

```text
sets:  B ----> A <---- C
               ^
               |
               D

maps: CMap ---> AMap <--- DMap
```

The five public structural equality theorems are:

- `RangeSetBlaze.internalAddB_eq_internalAddA`;
- `RangeSetBlaze.internalAddC_eq_internalAddA`;
- `RangeSetBlaze.internalAddD_eq_internalAddA`;
- `RangeMapBlaze.internalAddCMap_eq_internalAddAMap`;
- `RangeMapBlaze.internalAddDMap_eq_internalAddAMap`.

Each proof is one application of packaged uniqueness followed by the two
existing denotational correctness theorems. All other pairwise comparisons
follow by equality symmetry and transitivity, so no quadratic theorem family
was added.

CLen and DLen already prove exact `.setResult` equality with C and D;
CMapLen and DMapLen do likewise for `.mapResult`. Those correspondence
theorems plus the new hub results provide the Len structural consequences,
so adding separate redundant public theorems would only clutter the API.

## Cleanup and rejected abstractions

Search found no prior bespoke cross-algorithm structural proof to delete or
simplify. Existing Len correspondence theorems and private algorithm
preservation contracts remain necessary. Consequently:

- private helpers removed: 0;
- bespoke structural-comparison proofs removed or simplified: 0;
- existing algorithm/Len theorem bodies changed: 0.

A generic representation framework was rejected. Sets and maps share the
head-and-tail mathematical outline, but map endpoint uniqueness depends on
value-sensitive maximality and function evaluation. Abstracting over those
differences would add a larger interface than the two direct inductions.

The small head/lower-bound facts were also kept private. Their current purpose
is proof decomposition, while the raw and packaged uniqueness results are the
stable reusable concepts.

## Metrics

Metrics use `scripts/phase0_metrics.py` collector/schema v3, whose SHA-256 is
`a07fc3573ed0134219b1d539c2684d717707ab7360a8e0ba97602ef95549e048`.
Counts are independent dashboard signals, not a composite score.

`Basic.lean` and the algorithm modules are unchanged in active code; the root
aggregator gains one import. The requested grouped baselines therefore also
remain their final values:

| Scope | Physical LOC | Active LOC | Public proofs | Private proofs | `induction` | `cases` | `by_cases` | `have` | `rw` | `show` | `simp` | `simpa` | `omega` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `Basic.lean` | 660 | 454 | 49 | 1 | 4 | 0 | 3 | 10 | 26 | 16 | 51 | 1 | 28 |
| set algorithms A/B/C/D | 2,884 | 2,486 | 10 | 32 | 8 | 31 | 28 | 345 | 100 | 10 | 174 | 124 | 18 |
| map algorithms A/C/D | 3,741 | 3,440 | 9 | 53 | 16 | 29 | 118 | 423 | 62 | 9 | 338 | 193 | 135 |

New modules:

| File | Physical LOC | Active LOC | Public proofs | Private proofs | `induction` | `cases` | `by_cases` | `have` | `rw` | `show` | `simp` | `simpa` | `omega` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `Canonical.lean` | 398 | 372 | 4 | 7 | 6 | 16 | 2 | 63 | 44 | 0 | 23 | 3 | 16 |
| `CrossAlgorithm.lean` | 52 | 34 | 5 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | 0 | 0 | 0 |

Repository totals:

| Metric | Before | After | Delta |
| --- | ---: | ---: | ---: |
| Physical Lean LOC | 7,455 | 7,906 | +451 |
| Active-code LOC | 6,510 | 6,917 | +407 |
| Public proof declarations | 68 | 77 | +9 |
| Private proof declarations | 86 | 93 | +7 |
| `induction` | 28 | 34 | +6 |
| `cases` | 60 | 76 | +16 |
| `by_cases` | 149 | 151 | +2 |
| `have` | 787 | 850 | +63 |
| `rw` | 188 | 237 | +49 |
| `show` | 35 | 35 | 0 |
| `simp` | 565 | 588 | +23 |
| `simpa` | 323 | 326 | +3 |
| `omega` | 182 | 198 | +16 |

New uniqueness/extensionality theorems: 4. New cross-algorithm equality
theorems: 5.

## Axiom inventories

The new set raw/packaged theorems and all five cross-algorithm theorems depend
on exactly `[propext, Classical.choice, Quot.sound]`.

The two raw/packaged map uniqueness theorems have the smaller inventory
`[propext, Quot.sound]`; they do not require `Classical.choice`. No new theorem
depends on `sorryAx`.

All twelve existing public Len theorem inventories remain exactly
`[propext, Classical.choice, Quot.sound]`:

- `internalAddCLen_setResult`, `internalAddCLen_cachedLength`,
  `internalAddCLen_toSet`;
- `internalAddDLen_setResult`, `internalAddDLen_cachedLength`,
  `internalAddDLen_toSet`;
- `internalAddCMapLen_mapResult`, `internalAddCMapLen_cachedLength`,
  `internalAddCMapLen_toFunction`;
- `internalAddDMapLen_mapResult`, `internalAddDMapLen_cachedLength`,
  `internalAddDMapLen_toFunction`.

## Verification

- direct `Basic.lean` compilation: passed, zero warnings;
- direct `Canonical.lean` compilation: passed, zero warnings;
- direct `CrossAlgorithm.lean` compilation: passed, zero warnings;
- direct `RangeSetBlaze.lean` compilation: passed, zero warnings;
- full `lake build`: passed (1,890 jobs); only expected `Main.lean` `#eval`
  informational output;
- v3 metrics regression tests: 6 passed;
- `git diff --check`: passed;
- repository-owned active Lean-source scan: no `sorry`, `admit`, source
  `axiom`, `unsafe`, `implemented_by`, or `sorryAx`;
- axiom inventories: clean as recorded above.

The existing twelve Len public theorems remain unchanged and green.

## Final architectural review

The final Sol review found no architectural, theorem-contract, soundness, API,
or verification blocker. It confirmed the separate `Canonical` module, the
four-theorem uniqueness API with semantic `@[ext]` endpoints, the five-edge
A/AMap reference graph, the decision not to add redundant Len corollaries,
and the rejection of a generic set/map representation framework. It also
independently checked the proof sketch, metrics, source scan, builds, and axiom
inventories.

## Assessment

Canonical uniqueness is now a stable foundation for future query and
cross-implementation proofs. Clients can work at the denotational API and
recover exact representation equality without learning any insertion-specific
scan, split, cursor, or residual machinery.
