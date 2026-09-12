# Algo C map proof milestone

This checkpoint records the first complete proof of the production-shaped
range-map insertion model, before warning cleanup or proof compression.  It is
a preservation point, not authorization to change the executable algorithm.

## Source identity and verification

- Lean repository branch: `main`, tracking `origin/main`.
- Parent HEAD: `c7526c52a5b808a4c0e3e6cfff638b90b1921416`
  (`Clean up AlgoAMap proof architecture and public API`, 2026-09-11).
- `RangeSetBlaze/AlgoCMap.lean` SHA-256 before this report:
  `22bb7fe570717378129d10950e8a00a4c1a43b6f107ece68f8893714a969c4f8`.
- Metrics collector/schema: v3; collector SHA-256
  `a07fc3573ed0134219b1d539c2684d717707ab7360a8e0ba97602ef95549e048`.
- `lake env lean RangeSetBlaze/AlgoCMap.lean`: succeeds.
- `lake env lean RangeSetBlaze.lean`: succeeds.
- `lake build`: succeeds.
- No active `sorry`, `admit`, source `axiom`, `unsafe`, or `trace_state`
  remains in `AlgoCMap.lean`.
- `RangeMapBlaze.internalAddCMap_toFunction` depends on exactly
  `[propext, Classical.choice, Quot.sound]`; there is no `sorryAx`.

At checkpoint start the Lean worktree contained the intended uncommitted map
module and root import/export:

```text
 M RangeSetBlaze.lean
?? RangeSetBlaze/AlgoCMap.lean
```

## Proof architecture at the milestone

`internalAddCMapRuns_spec` proves both canonical output and exact first-match
function preservation:

```lean
Canonical output ∧
  runsToFunction output = overwrite (runsToFunction runs) input value
```

The proof first unfolds the executable definition and splits on the strict
lower-bound prefix's `getLast?`.  The no-predecessor branch reconstructs that
the suffix is the whole old list.  The predecessor branch derives one shared
set of facts before following the executable decisions:

- `before ++ after = runs`;
- canonical prefix, suffix, and cross-boundary order;
- every suffix start is at least `input.lo`;
- predecessor membership and `prev.lo < input.lo`;
- `before.dropLast ++ [prev] = before`;
- canonicality of `before.dropLast` and its order before `prev`;
- every run in `before.dropLast` ends before the input.

The resulting nonempty branch tree has seven leaves.

### 1. No predecessor

`before.getLast? = none` implies `before = []`, hence `after = runs`.
`scanForward_spec` supplies canonicality and preservation of
`inserted :: after`; `insertedSuffix_toFunction` identifies that list with
pointwise overwrite.

### 2. Same value, touching/overlapping, input covered

Conditions:

```text
prev.value = value
input.lo ≤ prev.hi + 1
input.hi ≤ prev.hi
```

Nonemptiness strengthens these conditions to actual containment of the input
inside `prev`.  The executable output is the original `runs`.  The proof shows
directly that every overwritten key already maps to the same value through
`prev`, then prepends the untouched initial prefix.

### 3. Same value, touching/overlapping, input extends

Conditions:

```text
prev.value = value
input.lo ≤ prev.hi + 1
prev.hi < input.hi
```

The predecessor and insertion are replaced by `mergeForward prev inserted`,
then scanned through `after`.  `mergePredecessor_toFunction` supplies the
overwrite semantics.  Canonical reassembly uses the fact that each run in
`before.dropLast` remains before the merged run and, through the new boundary
lemma, before everything emitted by the scan.

### 4. Same value, separated by a genuine gap

Condition:

```text
prev.value = value
prev.hi + 1 < input.lo
```

The whole `before` prefix stays untouched and the inserted run is scanned
through `after`.  The strict gap proves `Run.before prev inserted`, including
the stronger equal-value gap requirement.  Transitivity and the scan-boundary
lemma reattach the prefix; the function proof uses
`insertedSuffix_toFunction` and `prepend_left_of_overwrite`.

### 5. Different value, overlapping predecessor, right residual

Conditions:

```text
prev.value ≠ value
input.lo ≤ prev.hi
input.hi < prev.hi
```

The output tail is exactly:

```text
left residual :: inserted :: right residual :: after
```

There is no forward scan because the right residual ends the overwrite before
the untouched suffix.  The proof constructs the canonical chain explicitly
and uses `replacePredecessor_toFunction` for exact semantics before prepending
`before.dropLast`.

### 6. Different value, overlapping predecessor, no right residual

Conditions:

```text
prev.value ≠ value
input.lo ≤ prev.hi
prev.hi ≤ input.hi
```

The old predecessor becomes a left residual and the inserted run is scanned
forward.  The proof establishes that the left residual is before both the
inserted run and every old suffix run, transports that boundary through the
scan, and composes `replacePredecessor_toFunction` with `scanForward_spec`.

### 7. Different value, nonoverlapping predecessor

Conditions:

```text
prev.value ≠ value
prev.hi < input.lo
```

The predecessor is unaffected.  Unlike the same-value separated branch, no
extra integer gap is needed: touching differently valued runs are canonical.
The proof otherwise follows the separate-insertion composition used in leaf 4.

The public `internalAddCMap` wrapper contributes the remaining input case:
when `input.hi < input.lo`, it returns the old map and uses
`overwrite_eq_of_hi_lt_lo`.  Thus the complete public proof has one empty case
plus the seven nonempty list-level leaves above.

## New supporting lemmas

### `scanForward_preserves_left_boundary`

Statement, in words: if `left` is canonically before the pending run and every
run in the unprocessed suffix, then `left` is canonically before every run
emitted by `scanForward`.

This was needed because `scanForward_spec` intentionally returns only
canonical output and exact function preservation.  Those facts alone do not
justify appending a previously removed prefix: the composition proof also has
to establish every cross-boundary `Run.before` relation.  The lemma follows all
forward-scan outcomes, including merged pending runs and constructed right
residuals.

It is genuinely reused inside this module: the top-level proof invokes it in
four leaves.  It is not a representation-independent public theorem, because
its conclusion names the private `scanForward` executable.  The stable concept
is preservation of an untouched left boundary; a future cursor proof may use
that concept but should not depend on this list-specific statement.

### `strictStartSuffix_lower_bound`

Statement, in words: after splitting a canonical run list at
`run.lo < start`, every run in the suffix starts at or after `start`.

This fact is the lower-bound precondition required by `scanForward_spec` and by
the inserted-suffix function lemma.  `List.span`/`dropWhile` provides only the
first failed predicate directly; canonical order propagates the bound to the
rest of the suffix.

The lemma is used twice in the top-level proof, for the predecessor and
no-predecessor paths.  It is useful local representation support, not currently
a general proof API: it exposes the exact `List.span` split and private run-list
model.  Its mathematical content (an ordered suffix is bounded by the split
key) is transferable, but cursor proofs should state it in cursor/boundary
vocabulary.

## Assumption audit

- `internalAddCMapRuns_spec` uses both explicit assumptions.  `hnonempty` is
  needed to construct stored runs and to turn covered-branch endpoint tests
  into containment.  `hcanonical` supplies suffix ordering, prefix/suffix
  decomposition facts, and all cross-boundary relations.
- Both hypotheses of `scanForward_preserves_left_boundary` are needed:
  `left` must precede the pending run and all possible untouched or residual
  suffix output.
- `strictStartSuffix_lower_bound` needs only the lower-endpoint-order
  consequence of `Canonical`, not the equal-value non-touching part of the full
  invariant.  Its `Canonical runs` assumption is therefore stronger than the
  minimal mathematical premise, but exactly matches both callers and keeps the
  local interface readable.
- `mergePredecessor_toFunction` has an `hextends : prev.hi < input.hi`
  assumption that is not used by its proof; Lean reports it.  The equality is
  valid without that premise because `max` also handles containment.  The
  assumption documents the only executable branch that calls the lemma, but it
  is a real candidate for later removal.
- No other theorem-level assumption was shown redundant by compilation or by
  the branch composition.  Several linter messages concern redundant tactic
  arguments, not redundant mathematical hypotheses.

## AlgoCMap v3 metrics

These are independent dashboard signals, not a composite score.

| Category | Metric | Value |
|---|---|---:|
| Size | Physical LOC | 914 |
| Size | Nonblank LOC | 886 |
| Size | Comment-only LOC | 34 |
| Size | Active-code LOC | 852 |
| Declarations | Definitions / abbreviations | 6 / 0 |
| Declarations | Lemmas / theorems | 12 / 2 |
| Declarations | Private / public lemma-theorems | 13 / 1 |
| Branching | `cases` / `by_cases` / `induction` | 0 / 33 / 5 |
| Plumbing | `have` / `show` / `suffices` / `rw` | 128 / 2 / 0 / 13 |
| Automation | `simp` / `simpa` / `omega` / `linarith` / `grind` | 95 / 54 / 33 / 0 / 0 |
| Representation | `List.span` / `takeWhile` / `dropWhile` | 5 / 2 / 0 |
| Representation | `getLast?` / `dropLast` | 1 / 17 |
| Representation | `pairwise_append` / `Sublist` | 10 / 0 |

Repository totals at the same working-tree point are 4,123 physical LOC,
3,519 active-code LOC, and 316 comment-only LOC.  The source-manifest SHA-256
reported by the collector is
`640cfe6928bbdfadb321f7371fe257362e4415fb83ef882a0bbc1ab93837146e`.

## Remaining warnings

Direct compilation reports eight warnings, all already present in the supplied
proof skeleton before `internalAddCMapRuns_spec` was completed:

| Line | Warning | Assessment |
|---:|---|---|
| 97 | unused `hpending` simp argument | Safe mechanical cleanup. |
| 188 | unused `↓reduceDIte` simp argument | Safe mechanical cleanup. |
| 192 | unused `↓reduceDIte` simp argument | Safe mechanical cleanup. |
| 200 | unused `↓reduceDIte` simp argument | Safe mechanical cleanup. |
| 286 | unused `↓reduceDIte` simp argument | Safe mechanical cleanup. |
| 431 | unused `rightResidualAfter` simp argument | Safe mechanical cleanup. |
| 459 | unused variable `hextends` | Genuine helper-interface cleanup; review separately. |
| 471 | unused `hinput` simp argument | Safe mechanical cleanup. |

The seven tactic-argument warnings are worth fixing in a small follow-up
because they reduce noise and Lean gives exact edits.  They are not correctness
issues and should not be mixed into this milestone.  Removing `hextends` from
`mergePredecessor_toFunction` changes a helper statement and should be a
separate, explicitly reviewed cleanup even though it is also low risk.

## Rust-to-Lean branch correspondence

The relevant Rust source is the experimental cursor implementation in
`/home/carlk/programs/range-set-blaze/src/map.rs`, not
`internal_add_baseline`.  The Rust checkout was dirty during this audit, so its
identity is recorded as:

- Rust HEAD: `a5ca458739014c323a6a5ba9b4fb9d5f2b003a77`
  (`Enhance cursor functionality and documentation for range collections`).
- Branch: `map-insert-cursor`, one commit ahead of its upstream.
- Current `src/map.rs` SHA-256:
  `16dcad2ae9c0c476d5c6d978188786c8e7e41a0ab0e533e0bc9bdfb579ea40a4`.

The comparison covers `classify_predecessor`, `classify_forward`,
`cursor_scan_forward`, and `internal_add_cursor`.

| Rust cursor behavior | Lean executable/proof leaf | Correspondence |
|---|---|---|
| Reject `pending_end < pending_start` | Public `internalAddCMap` empty branch | Same no-op semantics. |
| `lower_bound_mut(Included(start))`; `peek_prev` | Strict `< input.lo` span; prefix `getLast?` | Both select the greatest stored start strictly below the input start and leave exact-start runs in the forward suffix. |
| No predecessor | Leaf 1 | Both scan/insert from the first suffix run. |
| `PredecessorInsertAction::Unaffected` | Leaves 4 and 7 | Same-value predecessors require a genuine gap; different-value predecessors need only be nonoverlapping. |
| `MergeSameValue`, stored end covers input | Leaf 2 | Both return the old representation unchanged. |
| `MergeSameValue`, input extends | Leaf 3 | Both extend the predecessor, mark/use it as pending, and scan forward. |
| `KeepLeftResidual` with `right_start = Some` | Leaf 5 | Both emit left residual, insertion, and right residual without scanning beyond the residual. |
| `KeepLeftResidual` with no right residual | Leaf 6 | Both retain the left residual and scan the inserted run forward. |
| Forward exact-start same-value cover | `scanForward` exact-cover branch | Both return the existing suffix unchanged when an unstored pending insertion is already represented. In the Lean merged-predecessor path this test is unreachable because the pending lower endpoint is the strictly earlier predecessor start. |
| Forward same-value overlap/touch | `mergeForward` recursion | Both remove/absorb the candidate and update the pending end with `max`. |
| Forward different-value overlap, candidate extends | Right-residual return | Both stop with pending plus the candidate portion beginning at `pending_end + 1`. |
| Forward different-value overlap, candidate covered | Delete-covered recursion | Both delete/skip the candidate and continue. |
| First unaffected candidate | Stop with pending and untouched suffix | Same stopping boundary. |

The proof confirms more than branch resemblance.  Each leaf establishes the
same two semantic obligations needed by the cursor design notes: canonical
ordering after reconstruction and exact pointwise overwrite.  The model
deliberately excludes cursor mutation order, cached-length accounting, and
bounded-integer overflow.  Rust uses checked successor/predecessor operations;
Lean uses unbounded `Int`, so conditions such as overlap-or-same-value-touching
collapse to the corresponding integer inequalities without overflow cases.

No branch drift was found between the completed Lean proof and the current
cursor classifier path at the recorded source identities.
