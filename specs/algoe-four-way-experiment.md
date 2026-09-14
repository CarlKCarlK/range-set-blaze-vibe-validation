# AlgoE / AlgoELen Four-Way Experiment

## Purpose

This experiment compared four independent implementations of the same Lean task: add `AlgoE` for `RangeSetBlaze` by transporting set insertion through a `RangeMapBlaze Unit`, add the corresponding cached-length operation `AlgoELen`, integrate the result, and clean up the proof/API design.

The goal was not only to find code that compiles, but to compare proof architecture, abstraction boundaries, API size, reuse of existing map algorithms, regression coverage, and how much proof complexity was genuinely removed rather than moved into helpers.

All candidates started from the same baseline commit:

`83cbc60008024cd2f8d7e3fc6d48b62a3aef8a88` (`improve ordered map semantics`)

The final comparison intentionally excluded a later Luna cleanup continuation and an older Sol-labeled run whose model identity was ambiguous. The four compared one-pass candidates were:

| Candidate | Model | Commit |
|---|---|---|
| A | Sonnet | `304ae50` |
| B | Fable | `a2f2bfd` |
| C | Luna | `abf7fa5` |
| D | Sol | `dd5abb8` |

## Experimental setup

Each candidate was copied into a blinded evaluation tree as `candidate-a` through `candidate-d`. The blind judges were given:

- the exact original task specification;
- the common baseline;
- the four candidate source trees;
- mechanically collected objective metrics and validation results;
- no model identities.

Two independent strong-model judges then inspected the actual source, compared each candidate with the baseline, assessed requirements and architecture, and ranked the candidates without knowing model identity.

Both judges independently produced the same ranking:

1. **Fable (B)**
2. **Sol (D)**
3. **Sonnet (A)**
4. **Luna (C)**

## Objective results

All four candidates passed the basic integrity checks:

| Candidate | `lake build` | Direct `Regression.lean` compile | Warnings | `git diff --check` |
|---|---:|---:|---:|---:|
| Sonnet | PASS | PASS | clean | PASS |
| Fable | PASS | PASS | clean | PASS |
| Luna | PASS | PASS | clean | PASS |
| Sol | PASS | PASS | clean | PASS |

`Regression.lean` is not currently reachable from the normal `lake build` graph, so it was also compiled directly with:

```text
lake env lean RangeSetBlaze/Regression.lean
```

All four direct compiles succeeded.

The repository-level v3 proof metrics were:

| Metric | Baseline | Sonnet | Fable | Luna | Sol |
|---|---:|---:|---:|---:|---:|
| Physical LOC | 9077 | 9308 | 9234 | 9234 | 9248 |
| Active code LOC | 8012 | 8147 | 8104 | 8140 | 8140 |
| Comment-only LOC | 576 | 636 | 614 | 584 | 598 |
| Public theorems | 86 | 101 | 94 | 90 | 93 |
| Private theorems | 109 | 110 | 110 | 115 | 111 |
| `induction` | 41 | 42 | 42 | 43 | 43 |
| `by_cases` | 171 | 172 | 172 | 173 | 173 |
| `cases` | 108 | 108 | 109 | 108 | 110 |
| `have` | 1017 | 1019 | 1018 | 1021 | 1019 |
| `rw` | 307 | 324 | 312 | 313 | 316 |
| `simp` | 674 | 680 | 681 | 682 | 686 |
| `simpa` | 348 | 348 | 348 | 352 | 349 |
| `omega` | 278 | 279 | 278 | 279 | 279 |

These metrics were treated as signals, not as a composite score.

The changed-file integration footprint was:

| Candidate | `Basic.lean` | `CrossAlgorithm.lean` | `Regression.lean` | `Main.lean` |
|---|---:|---:|---:|---:|
| Sonnet | Yes | Yes | Yes | No |
| Fable | Yes | Yes | Yes | Yes |
| Luna | No | No | No | Yes |
| Sol | No | Yes | Yes | No |

## Candidate summaries

### Fable — selected winner

Fable implemented the shared set / Unit-map bridge in `Basic.lean`:

- `RangeSetBlaze.toUnitMap`
- `RangeMapBlaze.toRangeSet`
- the round trip between them;
- support preservation;
- cardinality preservation.

`AlgoE` is then a very thin wrapper over `internalAddCMap`, and `AlgoELen` is a very thin wrapper over `internalAddCMapLen`. No insertion arithmetic is re-proved, and there is no fresh induction in `AlgoE.lean`.

This candidate had the smallest active-code increase of the four (+92 LOC), while still completing the cross-algorithm theorem, regression integration, and `Main.lean` demonstration. Its regression helper uniformly checks all scenarios and uses the existing C-length algorithm as an independent cached-length oracle.

Both blinded judges judged this to be the cleanest design from first principles: the bridge sits at the representation layer, is Unit-specific rather than over-generalized, and makes the algorithm module almost purely transport.

Minor follow-up opportunities identified by the judges:

- consider adding a direct `toUnitMap_support` lemma to make the AlgoE semantic proof even cleaner;
- consider whether the derivable public `internalAddELen_toSet` theorem is worth keeping;
- consider borrowing Sol's more explicit expected-range / expected-cardinality regression assertions.

### Sol — strong second

Sol independently chose `DMap` / `DMapLen` rather than `CMap` / `CMapLen`. The original specification allowed the implementation to determine which existing map algorithm was the appropriate basis, so this was a valid design choice.

Its strongest features were:

- a compact joint `internalAddELen_correct` theorem;
- excellent regression tests with explicit expected ranges and expected cardinalities;
- controlled public API growth (+7 public theorems).

The main reason it ranked behind Fable was the bridge architecture. The Unit-map bridge remained local to `AlgoE.lean`, and two fresh inductions were used for support/cardinality facts that Fable expressed more directly at the shared representation layer. The judges viewed this as proof complexity moved into local conversion machinery rather than eliminated.

### Sonnet — correct but over-generalized

Sonnet also used `CMap` / `CMapLen` and completed cross-algorithm and regression integration. Its shared support and overwrite lemmas were mathematically good and reusable.

However, it generalized several bridge facts from `Unit` to arbitrary `Subsingleton` values without a second consumer. That broader abstraction increased the proof/API surface substantially: +15 public theorems, by far the largest increase of the four candidates.

The bridge was also split across `Basic.lean` and `AlgoE.lean`, so the design was less cohesive than Fable's representation-level Unit bridge.

The judges consistently described Sonnet as correct and thoughtful, but in need of an API-pruning pass.

### Luna — correct core, incomplete end-to-end task

Luna's one-pass solution correctly implemented AlgoE through `CMap` and AlgoELen through `CMapLen`, and kept its public API small.

Its main weakness was that the experiment task was not completed end to end:

- no `CrossAlgorithm.lean` integration;
- no `Regression.lean` additions;
- the set / Unit-map bridge remained private and local to `AlgoE.lean`;
- more support/cardinality reasoning was carried by local private helpers and inductions.

The judges viewed the small public surface as partly an artifact of hiding duplicated infrastructure rather than eliminating it.

## Blind-judge agreement

The strongest result of the experiment was the agreement between the two independent blind reviews.

Both judges ranked:

**Fable > Sol > Sonnet > Luna**

They also converged on essentially the same reasons:

- **Fable** best separated stable representation mathematics from algorithm control flow and removed the most proof complexity.
- **Sol** had the strongest theorem shape and most concrete tests, but kept too much bridge machinery local.
- **Sonnet** over-generalized and over-published an otherwise sound design.
- **Luna** implemented the core correctly but did not complete the requested integration and cleanup scope.

This agreement was notable because the judges did not know which model produced which candidate.

## Validation caveat discovered during judging

The blind review found that `RangeSetBlaze/Regression.lean` is not part of the normal `lake build` dependency graph. Therefore the original successful `lake build` result did not, by itself, prove that the candidate regression files elaborated.

The regression files were subsequently compiled directly for all four candidates, and all four passed.

This suggests a separate repository improvement: make `Regression.lean` part of a build/test target so regression examples are automatically checked by the normal validation workflow.

## Shared reporting gap

All four candidate implementations were missing some of the validation artifacts explicitly requested by the experimental task specification. In particular, the candidate trees did not durably record:

- the requested public-theorem `#print axioms` inventory;
- changed-file before/after v3 metrics;
- a complete validation report showing every requested project-specific check.

This was treated as a tie rather than as a correctness distinction between candidates. The evaluation independently collected repository metrics, build results, warning status, `git diff --check`, forbidden-token scans, and direct regression compilation. An explicit final axiom inventory remains worth recording before considering the experiment completely closed.

## Decision

Fable's implementation was selected as the basis for `main` and cherry-picked as commit:

`d6f7ea4` — `Add Algo E and ELen: set insertion derived from Algo CMap at Unit`

The decision was based on the combination of:

- two independent blinded rankings;
- the smallest active-code increase;
- the cleanest shared Unit-map abstraction;
- no duplicated insertion or cardinality arithmetic;
- complete integration and strong regression coverage;
- a design closest to what the judges would choose if AlgoE/AlgoELen had been planned from the beginning.

## Follow-up ideas

The experiment also identified a few ideas worth considering on top of the Fable implementation rather than replacing it:

1. Borrow Sol's explicit expected-ranges / expected-cardinality regression style where it adds independent checking value.
2. Consider a small `toUnitMap_support` theorem in `Basic.lean` if it simplifies the AlgoE semantic proof without expanding the API unnecessarily.
3. Re-evaluate the public AlgoELen theorem surface after seeing actual downstream use; Fable's current split matches existing repository conventions, while Sol's joint theorem is more compact but couples an unconditional representation fact to a conditional cache hypothesis.
4. Add `Regression.lean` to an actual build/test target.
5. Record the final `#print axioms` inventory and validation evidence.

## Broader lesson

The experiment reinforced a useful proof-engineering principle for this project:

> Share stable mathematics, not algorithm control flow.

The strongest solution did not win by having the fewest declarations or by hiding helpers. It won by identifying the right shared mathematical bridge, putting that bridge at the representation layer, and making the new algorithms nearly trivial transports over already-proved machinery.
