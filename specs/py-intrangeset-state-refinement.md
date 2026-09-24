# PySnpTools `IntRangeSet` two-field state refinement

Date: 2026-09-23

## Starting state

Work started at `17a110756fd90ecab9a19f98b21111849b19b63c` on branch `python`
with a clean worktree. `RangeSetBlaze/PyIntRangeSet.lean` modeled
`IntRangeSet._internal_add` over the list of ranges that Python's two fields
denote. Its module doc stated that keeping `_start_items` and
`_start_to_length` in sync was "structural here". The list model assumed
that synchronization instead of proving it.

## Goal

Model Python's state as it really is, and prove that it refines the existing
list model:

```text
Python state: sorted `_start_items` + dict `_start_to_length` + invariants
        ↓  Python-shaped mutations of both fields
abstraction to canonical ordered ranges
```

Required: state the concrete Python invariants as named theorems of the
abstraction, rather than leaving synchronization implicit in the refinement
relation. In particular, prove that `_start_items` stays sorted and that its
elements are exactly the keys of `_start_to_length`.

## Design

`RangeSetBlaze/PyIntRangeSetState.lean` is a separate refinement module. The
list model and its correctness proof are unchanged, apart from visibility
(see Common cleanup).

- **State.** `PyIntRangeSet` has `startItems : List Int` and
  `startToLength : Int → Option Int`. Python only gets, sets and deletes
  single dictionary keys. Those operations are function application and
  `Function.update` to `some` or `none`.
- **Failure.** `internalAdd` returns `Option`. `none` is a failed `assert`
  (`length > 0`, `new_length > 0`), a `KeyError` (missing dictionary key), or
  an `IndexError` (`_start_items[index - 1]?`). The refinement theorem
  therefore also proves that Python never raises on a represented state and
  an in-contract call.
- **Algorithm.** `internalAdd` follows Python line by line: `bisect_left`,
  the exact-start test `_start_items[index] == start`, `index == 0`,
  `previous = _start_items[index - 1]`, both early returns, and the merge
  loop. The loop is `mergeLoop`, which recurses on `index` with
  `termination_by len - index`. Python's `if index >= len: break` becomes the
  `index < len` test. The only structural factoring is `addAfterPrevious`.
  It holds Python's `elif index == 0 / else` branches and mirrors the list
  model's `addAfterPredecessor`, so the proof can match the two
  branch by branch.
- **Abstraction.** `Stores py ranges` is a structure. It says `_start_items`
  equals `ranges.map lo` and `_start_to_length` equals
  `startToLengthOf ranges`. `Represents py s := Stores py s.ranges` is the
  canonical case. `Stores` also covers non-canonical lists, which the merge
  loop needs: while it runs, the current range overlaps the ranges after it.
  The loop invariant is `Stores` plus distinct starts.

## Python invariants as named theorems

`structure Invariant` states Python's invariants on the two fields, one named
field each. `Represents.invariant` derives all of them from the abstraction:

| Theorem | Python meaning |
| --- | --- |
| `Represents.startItems_sorted` | `_start_items` is sorted, strictly (`List.SortedLT`) |
| `Represents.mem_startItems_iff` | `k in _start_items` ⇔ `k in _start_to_length` |
| `Represents.length_pos` | every stored length is positive |
| `Represents.stop_lt_later_start` | each range's stop is strictly below every later start (no overlap, no touching) |
| `Invariant.startItems_nodup` | `_start_items` has no duplicates |
| `Invariant.ncard_keys_eq_length` | `len(_start_to_length) == len(_start_items)`, Python's own assertion |

Two further results show how the relation and the invariants fit together:

- `Invariant.exists_represents`: the invariants are all that `Represents`
  requires. Any state satisfying them represents the canonical list
  `storedRanges`.
- `Represents.unique`: the abstraction is a function.

`Represents.toSet_eq` identifies Python's denotation (the union of every
stored `[start, start + length)`) with the abstract set.

## Refinement and specification

- `internalAdd_refines`: from `Represents py s` and `0 < length`,
  `internalAdd py start length = some py'` and
  `Represents py' (internalAddPy s start length)`.
- `internalAdd_spec`: correctness in Python's vocabulary alone. From
  `Invariant py`, `_internal_add` does not raise, `py'` satisfies
  `Invariant`, and `py'.toSet = py.toSet ∪ [start, start + length)`.

Every Python mutation edits one stored range at one list position, and each
kind has one lemma:

- inserting a new start (`insert_stores`);
- assigning a new length to a stored start (`assignLength_stores`);
- deleting an absorbed start inside the loop (`mergeLoop_stores`).

On the dictionary side all three reduce to `startToLengthOf_append_cons`.
Lookups use `startToLengthOf_of_mem`, which needs distinct starts.

Axioms: `internalAdd_refines`, `internalAdd_spec`, and
`Invariant.exists_represents` depend only on `propext`, `Classical.choice`,
and `Quot.sound`, the same set as `internalAddC_toSet`. No `sorry`.

## Differential testing against both Python structures

`scripts/generate_py_intrangeset_cases.py` now records each resulting Python
state three ways: `ranges()`, `_start_items`, and `_start_to_length` in key
order. It also generates seeded random call sequences that start from
`IntRangeSet()`. Output is deterministic; a regeneration was byte-identical.

- 1,379 base-window cases over five base sets. The two-field model starts
  from Python's own fields.
- 300 sequences of 8 calls (2,400 calls). Both Lean models run in lockstep
  with Python from the empty state.
- Python branch coverage, counting cases that reach each branch:
  - exact start, covered: 141
  - exact start, lengthen: 182
  - `index == 0` insert: 1,072
  - touch previous: 1,362
  - previous covers: 314
  - lengthen previous: 1,048
  - gap insert: 1,022
  - merge loop body: 1,519

For every call, `RangeSetBlaze/Regression.lean` checks four things with
`native_decide`:

1. The list model gives Python's `ranges()`.
2. The two-field model does not raise.
3. Its `_start_items` equals Python's.
4. Its `_start_to_length` equals Python's at every key either side could hold.
   These are Python's resulting keys, the earlier keys, and `start`. A Lean
   key outside these is impossible, because a call writes only `start` or an
   earlier key.

It also checks the abstraction: `storedRanges` of the two-field result equals
the list model's result. The earlier agreement check against Algos A, C, and D
is kept, on the new case format.

A hand-corrupted expected state is rejected. This was checked both for a
wrong dictionary value and for a stale extra key.

## Mutation testing

`scripts/mutate_py_intrangeset_state.py` applies one textual mutation at a
time to a temporary copy of the module. It appends the `python-differential`
region of `Regression.lean` and compiles the result. Each mutant is then
classified: killed by the proofs (an error inside the module), by the tests
(a false `native_decide`), by both, or by neither. The source tree is never
modified. The unmutated module must pass first.

| Mutant | Killed by |
| --- | --- |
| loop merges only overlapping, not touching | proofs + tests |
| loop keeps the absorbed dictionary key | proofs + tests |
| loop length measured from `next` | proofs + tests |
| loop new stop ignores the current stop | proofs + tests |
| loop lengthens `next` instead of `previous` | proofs + tests |
| exact start: loop starts at the range itself | proofs + tests |
| `index == 0`: dictionary updated, `_start_items` not | proofs + tests |
| previous: touching start treated as a gap | proofs + tests |
| gap insert: `_start_items` updated, dictionary not | proofs + tests |
| [equivalent] exact start returns only on `length < existing` | proof script |
| [equivalent] previous returns on `new_length <= length` | proof script |
| [equivalent] `bisect_right` instead of `bisect_left` | proof script |
| [equivalent] `assert length >= 0` | proof script |
| [statement] abstraction stores `stop` instead of length | proofs |
| [statement] invariant allows touching ranges | proofs |

There are 15 mutants: 9 real bugs, 4 equivalent, and 2 statement mutants.
All 9 real-bug mutants are killed by both the proofs and the tests.

The four *equivalent* mutants give the same result on every represented state
for every in-contract call, so the theorems stay true for them:

- At equal lengths, both early-return mutants re-store the same range and run
  a merge loop that merges nothing.
- `bisect_right` sends an exact start to the `previous` branch, which computes
  the same result.
- A zero length is outside the `0 < length` contract.

The tests correctly cannot kill these mutants. The proof *script* rejects
them only because it matches Python's branches against the list model's one
by one. That coupling is intended: this repository protects the
production-shaped branch structure, not just extensional behavior. Still, a
proof-script kill here is not evidence of a bug.

The two *statement* mutants change the abstraction or the invariant without
changing the executable code, so no test can see them. Only the proofs catch
them. For example, weakening `stop_lt_later_start` to allow touching ranges
makes `Invariant.exists_represents` false.

Python-side mutation was not run, that is, mutating PySnpTools and confirming
that the regenerated cases fail. The lockstep sequence checks compare full
field contents after every call, so any Python mutation that changes a field
is caught on the cases that exercise it.

## Cleanup passes

### Local

- The in-place length assignment was proved twice, in the exact-start and
  lengthen-previous branches. It is now one lemma, `assignLength_stores`,
  used by both, mirroring `insert_stores`.
- The freshness argument for a stored start is now one lemma,
  `start_not_mem_earlier_starts`, instead of repeated nodup unpacking.
- Proof scaffolding is private: `mergeLoop_stores`,
  `addAfterPrevious_stores`, `internalAdd_stores`, `bisectLeft_starts`,
  `insert_stores`, `assignLength_stores`, `insertIdx_length_append`. The
  public surface is the state, the algorithm, the dictionary API, `Stores`,
  `Represents`, `Invariant`, the invariant theorems, `storedRanges`, and the
  refinement and spec theorems.
- The sections were reordered so that the invariants and the abstraction come
  before the refinement proof, and the module doc was updated to describe the
  final proof.

### Common

- `mem_rangesToSet_iff` was a private lemma in `Query.lean`. It is now public
  in `Basic.lean`, used by `Query.lean` and by `Represents.toSet_eq`.
- `RangeSetBlaze.bisectLeft_spec` is now public in `PyIntRangeSet.lean` and
  reused by the refinement, instead of restating
  `NR.strict_start_split_spec` with an explicit `let`.
- The `NR.ofStartStop` simp lemmas (`lo_`, `stop_`, `length_ofStartStop`)
  and `NR.lo_add_length` moved into the half-open vocabulary section of
  `PyIntRangeSet.lean`, next to `NR.stop` and `NR.length`.
- The list model's executable helpers `bisectLeft`, `mergeFollowing`,
  `addAfterPredecessor`, and `internalAddPyNRs` changed from `private` to
  public so that the refinement can name them. Their bodies are unchanged.

### Larger

- `internalAddPy_python_invariants` was removed. It restated the list
  model's canonicity in near-Python terms. `Represents.invariant`, applied to
  the result of `internalAdd_refines`, now proves those invariants on
  Python's actual fields. It had no callers.
- The list-model module doc no longer calls synchronization "structural". It
  points to this module for the two-field proof.
- The differential checker in `Regression.lean` became one delimited,
  self-contained region, so the mutation harness can reuse it verbatim
  without a second copy.

## Rejected alternatives

- **An association list or `Std.HashMap` for the dictionary.** Python's
  dictionary order is unobservable here, and a function avoids proving
  permutation and uniqueness facts. The differential checker compares the
  function against Python's `dict` at every key that matters.
- **A total model with default values in place of `KeyError`/`IndexError`.**
  That would hide exactly the synchronization failures this module exists to
  rule out.
- **Stating `Represents` directly as the invariants.** The user asked for the
  invariants to be corollaries, not assumptions. `exists_represents` gives
  the converse without making it the definition.
- **A generic "one edit at one position" lemma over all three mutation
  kinds.** The three kinds have different item-list edits (`insertIdx`,
  none, `eraseIdx`), so a common wrapper would move detail around without
  removing it.

## Metrics

Collector/schema v3, SHA-256
`a07fc3573ed0134219b1d539c2684d717707ab7360a8e0ba97602ef95549e048`. The
machine-readable results are `metrics/py-intrangeset-state-baseline-v3.json`
(Git ref `17a1107`) and `metrics/py-intrangeset-state-final-v3.json` (the
working tree on that base).

| File | Physical | Active | Comment-only | Lemmas/theorems | Private |
| --- | ---: | ---: | ---: | ---: | ---: |
| `PyIntRangeSetState.lean` (new) | 670 | 445 | 153 | 26 | 7 |
| `PyIntRangeSet.lean` | 421 → 425 | 261 → 261 | 117 → 117 | 11 → 11 | 5 → 4 |
| `Basic.lean` | 739 → 759 | 497 → 514 | 111 → 113 | 39 → 40 | 2 → 2 |
| `Query.lean` | 1,154 → 1,136 | 1,079 → 1,062 | 35 → 35 | 22 → 21 | 15 → 14 |
| `Regression.lean` | 185 → 285 | 134 → 197 | 28 → 52 | 0 → 0 | 0 → 0 |
| `PyIntRangeSetCases.lean` (generated) | 1,430 → 4,137 | 1,391 → 4,092 | 26 → 31 | 0 | 0 |

Excluding the generated cases file, repository active LOC grew by 509 and
physical LOC by 777. The new module's dashboard counts are:

- branching: `induction` 5, `by_cases` 8, `cases` 3;
- plumbing: `have` 29, `rw` 34;
- automation: `simp` 55, `simpa` 15, `omega` 11, `grind` 1.

These are separate signals, not a score.

## Commands and results

- `lake build`: passed, 2,098 jobs, no warnings.
- `lake test`: passed. The regression build includes all Python
  differential checks.
- `lake env lean RangeSetBlaze/PyIntRangeSetState.lean`: passed, no warnings.
- `python3 scripts/mutate_py_intrangeset_state.py`: 15 mutants, 0 differ from
  the recorded expectation.
- `/home/carlk/programs/PySnpTools/.venv/bin/python scripts/generate_py_intrangeset_cases.py`:
  3,779 cases, every branch covered, byte-identical on regeneration.
