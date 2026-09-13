# `range_or_gap_at` proof audit

Date: 2026-09-13

## 1. Starting state

- Lean repository: `/home/carlk/programs/range-set-blaze-lean2`
- starting HEAD: `c4a869acd2ad157e99023a1282ded037acd2aeb3`
- starting tree: `68185176258816d5eda5f0cee009d70dba7e5234`
- branch: `main`, synchronized with `origin/main`
- starting worktree: clean
- Lean: 4.33.1; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`
- no commit, tag, or push was made

The production Rust repository was read only.  It was clean at
`67467ad0945a957a25afd263d3bf1bc0507122b9`, tree
`e7c046d722549bcee4e9b897b133c24c0179db4a`, branch
`map-insert-cursor` synchronized with its upstream.

## 2. Rust specification sources

| Subject | File and lines |
| --- | --- |
| set public documentation and dispatch | `src/set.rs:437-464` |
| set baseline query | `src/set.rs:466-483` |
| set cursor query | `src/set.rs:485-512` |
| set predecessor helper | `src/set.rs:765-772` |
| map public documentation and dispatch | `src/map.rs:889-916` |
| map baseline query | `src/map.rs:918-935` |
| map cursor query | `src/map.rs:937-967` |
| map predecessor helper | `src/map.rs:1145-1152` |
| `Integer` domain/step interface | `src/integer.rs:18-49` |
| set public and exhaustive tests | `tests/set_tests.rs:1674-1731` |
| map public/exhaustive tests | `tests/map_tests.rs:316-365,412-445,502-528` |
| direct cursor/baseline tests | `src/tests_cursor_lookup.rs:9-87` |

The result is not an enum: set returns `(RangeInclusive<T>, bool)`, while map
returns `(RangeInclusive<T>, Option<&V>)`.  Endpoints are finite domain values,
not optional or `Bound` values.

## 3. Rust behavior table

| Rust state | Semantic situation | Lean branch | Obligation |
| --- | --- | --- | --- |
| baseline predecessor contains key | stored range/run contains key | non-strict split, last prefix, contained | exact stored interval and membership/value |
| baseline predecessor, successor, neither contains key | internal gap | last prefix + first suffix | `[pred.hi+1, succ.lo-1]`, absent and maximal |
| baseline predecessor, no successor | trailing gap | empty suffix | `[pred.hi+1, upper]` |
| baseline no predecessor, successor | leading gap | empty prefix | `[lower, succ.lo-1]` |
| baseline neither neighbor | empty representation | both split sides empty | full-domain absent interval |
| cursor predecessor contains key | `peek_prev` contains key | strict split, last prefix | exact stored interval/run |
| cursor next starts exactly at key | exact lower-bound hit | first suffix equality | exact next interval/run and value |
| cursor two neighbors, no exact hit | internal gap | strict split neighbor pair | same finite gap as baseline |
| cursor only predecessor | trailing gap | right empty | domain maximum boundary |
| cursor only non-exact successor | leading gap | left empty | domain minimum boundary |
| cursor no neighbors | empty representation | both sides empty | full-domain gap |

For sets, canonical ranges have a genuine integer gap.  For maps, touching
different-valued runs are legal and are not gaps; touching equal-valued runs
are noncanonical because they should be one maximal run.

## 4. Lean semantic specification

`MaximalConstantInterval` is the shared interval-level definition.  It states
domain containment, key containment, constant state throughout the inclusive
result, and a different state immediately outside either non-domain endpoint.

- `RangeSetBlaze.QueryResultSpec` uses Boolean membership state.
- `RangeMapBlaze.QueryResultSpec` uses `toFunction : Int -> Option Value`.
- `RangeSetBlaze.WithinDomain` and `RangeMapBlaze.WithinDomain` state that all
  stored pieces lie within the explicitly modeled finite domain.

The explicit `lower`/`upper` arguments are necessary because repository keys
are unbounded `Int`, whereas Rust returns concrete `T::min_value()` and
`T::max_value()` endpoints.

## 5. Executable/model correspondence

| Rust operation | Lean model |
| --- | --- |
| `range(..=key).next_back()` | `List.span (lo <= key)` and prefix `getLast?` |
| `range(key..).next()` after baseline predecessor | first element of the non-strict split suffix |
| `lower_bound(Included(key))` | `List.span (lo < key)` |
| `peek_prev()` | strict split prefix `getLast?` |
| `peek_next()` | strict split suffix `head?` |
| inclusive stored range | `IntRange` / `NR` |
| start-to-end/value B-tree entry | `RangeMapBlaze.Run` |
| `add_one` / `sub_one` | dense-`Int` `+ 1` / `- 1` |
| `T::min_value/max_value` | theorem/function parameters `lower/upper` |

The model preserves every query branch but abstracts B-tree implementation,
complexity, references/lifetimes, and the generic non-dense `Integer` step
operation.

## 6. Public theorem statements

```lean
theorem maximalConstantInterval_unique {State : Type*}
    {state : Int → State} {lower upper key : Int}
    {range₁ range₂ : IntRange} {value₁ value₂ : State}
    (h₁ : MaximalConstantInterval state lower upper key range₁ value₁)
    (h₂ : MaximalConstantInterval state lower upper key range₂ value₂) :
    range₁ = range₂ ∧ value₁ = value₂

theorem RangeSetBlaze.rangeOrGapAtBaseline_correct
    (set : RangeSetBlaze) (lower upper key : Int)
    (hdomain : WithinDomain set lower upper)
    (hkeyLower : lower ≤ key) (hkeyUpper : key ≤ upper) :
  QueryResultSpec set lower upper key
    (rangeOrGapAtBaseline set lower upper key)

theorem RangeSetBlaze.rangeOrGapAtCursor_correct
    (set : RangeSetBlaze) (lower upper key : Int)
    (hdomain : WithinDomain set lower upper)
    (hkeyLower : lower ≤ key) (hkeyUpper : key ≤ upper) :
  QueryResultSpec set lower upper key
    (rangeOrGapAtCursor set lower upper key)

theorem RangeSetBlaze.rangeOrGapAtBaseline_eq_cursor
    (set : RangeSetBlaze) (lower upper key : Int)
    (hdomain : WithinDomain set lower upper)
    (hkeyLower : lower ≤ key) (hkeyUpper : key ≤ upper) :
  rangeOrGapAtBaseline set lower upper key =
    rangeOrGapAtCursor set lower upper key

theorem RangeMapBlaze.rangeOrGapAtBaseline_correct {Value : Type*}
    (map : RangeMapBlaze Value) (lower upper key : Int)
    (hdomain : WithinDomain map lower upper)
    (hkeyLower : lower ≤ key) (hkeyUpper : key ≤ upper) :
  QueryResultSpec map lower upper key
    (rangeOrGapAtBaseline map lower upper key)

theorem RangeMapBlaze.rangeOrGapAtCursor_correct {Value : Type*}
    (map : RangeMapBlaze Value) (lower upper key : Int)
    (hdomain : WithinDomain map lower upper)
    (hkeyLower : lower ≤ key) (hkeyUpper : key ≤ upper) :
  QueryResultSpec map lower upper key
    (rangeOrGapAtCursor map lower upper key)

theorem RangeMapBlaze.rangeOrGapAtBaseline_eq_cursor {Value : Type*}
    (map : RangeMapBlaze Value) (lower upper key : Int)
    (hdomain : WithinDomain map lower upper)
    (hkeyLower : lower ≤ key) (hkeyUpper : key ≤ upper) :
  rangeOrGapAtBaseline map lower upper key =
    rangeOrGapAtCursor map lower upper key
```

Each correctness/equivalence theorem assumes representation containment in
the modeled domain and `lower <= key <= upper`.  Map theorems have no
`DecidableEq Value` assumption.

## 7. Set proof architecture

Private list-denotation and neighbor lemmas show that a stored range evaluates
to `true`, and that no range contains a point strictly between the selected
predecessor and successor.  `storedRange_queryResultSpec` establishes
constancy and uses the genuine-gap canonical relation at both outside points.
`gap_queryResultSpec` packages the common maximal-gap conclusion.

The baseline and cursor proofs each expose their production split, obtain the
predecessor/successor facts once, and discharge present/gap branches through
these semantic helpers.

## 8. Map proof architecture

Three evaluation facts connect raw run lists to `runsToFunction`: a successful
lookup comes from a containing run; a canonical containing run is returned;
and absence of any containing run gives `none`.

`storedRun_queryResultSpec` proves every point in the run returns its value.
At an adjacent point, canonical nonoverlap excludes the same run, and the
equal-value clause excludes any touching run with the same value.  Different
values may touch and correctly remain different maximal states.

## 9. Cursor proof architecture

Strict split contracts reconstruct the original list and prove `lo < key` on
the left and `key <= lo` on the right.  `getLast?`/`head?` are the modeled
cursor observations.  Exact-start successor branches are retained explicitly;
all other branches use the same stored-piece and maximal-gap contracts as the
baseline proof.

## 10. Semantic-result uniqueness

`maximalConstantInterval_unique` is public because it is stable mathematics
used by both set and map equivalence theorems.  Its proof compares states at
the shared key, then rules out unequal starts and ends using the immediate
outside-point maximality clauses.

## 11. Equivalence derivation

Both equality theorems consist only of baseline correctness, cursor
correctness, and semantic-result uniqueness, followed by product extensionality.
No branch-by-branch baseline/cursor equivalence proof exists.

## 12. Local cleanup

- related gap facts are packaged by one helper in each semantic family;
- predecessor/successor decompositions are computed once per proof;
- contained stored-piece proofs use one semantic helper;
- redundant simplifier arguments reported by Lean were removed;
- all query-module warnings were eliminated.

## 13. Cross-query cleanup

The one shared abstraction is `MaximalConstantInterval` plus its uniqueness
theorem.  Split geometry remains separate for `NR` and `Run` because their
canonical relations differ materially.  Set and map result structures and
state-specific proof helpers were not forced into a generic query framework.

## 14. Stronger-inference cleanup

The final pass uses direct `List.mem_of_mem_getLast?`, `List.mem_of_head?`,
`List.mem_iff_append`, `List.pairwise_append`, standard take/drop-while
reconstruction, direct canonical projections, and focused `simpa`.  Explicit
arithmetic automation remains at discrete endpoint obligations where it is
the clearest local proof.

## 15. Helpers added/removed

- public semantic/support definitions: 6 (shared maximal interval, set state,
  set/map specs, and set/map domain predicates)
- public executable models: 4
- public proof declarations: 9, including two small set-state simp theorems
- private proof declarations: 16
- recursive proof sites: 7, all small list semantic/split inductions
- manual baseline/cursor branch-equivalence proofs avoided: 2
- pre-existing helpers removed or changed: 0

## 16. Rejected abstractions

A generic “piece with endpoints and payload” query framework was rejected.
Although split mechanics look similar, set canonicality requires genuine gaps,
while map canonicality allows touching different values and needs
value-sensitive maximality.  Sharing those proofs would obscure the central
semantic distinction.

Existing private Algo D cursor structures were not promoted.  The new module
models read-only lookup placement directly and does not expose insertion
cursor state as public query API.

## 17. Metrics

Metrics use collector/schema v3, SHA-256
`a07fc3573ed0134219b1d539c2684d717707ab7360a8e0ba97602ef95549e048`.
Machine-readable files are:

- baseline: `/tmp/range-or-gap-at-baseline-c4a869a-v3.json`
- final: `/tmp/range-or-gap-at-final-v3.json`

| Scope/metric | Baseline | Final | Delta |
| --- | ---: | ---: | ---: |
| repository physical Lean LOC | 7,906 | 9,077 | +1,171 |
| repository active Lean LOC | 6,917 | 8,012 | +1,095 |
| repository comment-only LOC | 541 | 576 | +35 |
| public proof declarations | 77 | 86 | +9 |
| private proof declarations | 93 | 109 | +16 |
| `induction` | 34 | 41 | +7 |
| `cases` | 76 | 108 | +32 |
| `by_cases` | 151 | 171 | +20 |
| `have` | 850 | 1,017 | +167 |
| `rw` | 237 | 307 | +70 |
| `show` | 35 | 41 | +6 |
| `simp` | 588 | 674 | +86 |
| `simpa` | 326 | 348 | +22 |
| `omega` | 198 | 278 | +80 |

`Query.lean` has 1,170 physical LOC, 1,094 active LOC, 35 comment-only LOC,
10 definitions, 9 public proofs, and 16 private proofs.  Exact intermediate
metric snapshots were not retained: cleanup happened within the new untracked
module before its first final metric capture.  The pass-specific declaration
effects above are exact, but no unreproducible intermediate LOC claims are
made.

## 18. Verification

- `lake env lean RangeSetBlaze/Query.lean`: passed, zero warnings
- `lake env lean RangeSetBlaze.lean`: passed, zero warnings after aggregate build
- executable set/map present-and-gap smoke examples: passed
- `lake build`: passed, 1,892 jobs; only expected `Main.lean` `#eval` output
- v3 metrics regression suite: 6 tests passed
- `git diff --check`: passed
- active repository-owned Lean scan: no `sorry`, `admit`, source `axiom`,
  `unsafe`, `implemented_by`, or `sorryAx`
- production Rust repository: not modified

## 19. Axiom inventories

| Theorems | Dependencies |
| --- | --- |
| `maximalConstantInterval_unique` | `[propext, Quot.sound]` |
| set state simp/correctness/equivalence theorems | `[propext, Classical.choice, Quot.sound]` |
| map correctness/equivalence theorems | `[propext, Quot.sound]` |

Both raw and packaged canonical uniqueness theorems, all five cross-algorithm
theorems, and all twelve public Len theorems retain their previous clean
inventories.  No checked theorem depends on `sorryAx`.

## 20. Remaining external assumptions and assessment

The formal model assumes the documented ordered cursor gap semantics rather
than verifying Rust's `BTreeMap` cursor implementation.  It models a dense
finite interval of mathematical integers, so non-dense `Integer`
implementations such as `char` remain externally corroborated by Rust tests.
References, lifetimes, feature dispatch, and asymptotic complexity are outside
the semantic model.

Within that abstraction boundary, query verification is structurally settled:
all four production branch trees satisfy one set or map semantic contract, and
both implementation equalities follow solely from uniqueness of that contract.
