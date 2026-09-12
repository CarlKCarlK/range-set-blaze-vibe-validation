# Why cursor-shaped Algo D map insertion is correct

Date: 2026-09-12

Algo D map models the production Rust `BTreeMap` cursor as a gap in a
canonical list.  The executable definitions preserve the Rust control flow:
locate one predecessor, mutate or retain it locally, scan successors through
`peek_next`, and finally insert the pending run and any right residual.  The
proof does not model cached cardinality or iterator validity.

## Cursor gap

`lowerBoundGap start runs` splits immediately before the first run whose lower
endpoint is at least `start`.  `lowerBoundGap_spec` proves three facts used by
every later branch:

- `runs = gap.left ++ gap.right`;
- every left run starts below `start`;
- every right run starts at or above `start`.

Canonicality then identifies `gap.left.getLast?` as the only left-side run
that can overlap or touch the input.  Earlier left runs are finalized.

## Exact predecessor invariant

The original temporary statement of `cursor_predecessor_mutation_spec` was
too weak.  It allowed a predecessor ending before `input.lo - 1`; replacing
that predecessor by `leftResidualBefore` would then enlarge it up to
`input.lo - 1`.

The weakest natural condition preventing enlargement is

```text
not (predecessor.range ≺ input.range)
```

where `≺` is `IntRange.NR.before`.  In endpoint form this says
`input.lo ≤ predecessor.hi + 1`: the predecessor overlaps or exactly touches
the input.  This is preferable to an ad hoc stronger overlap inequality
because it states precisely when `[predecessor.lo, input.lo - 1]` is contained
in the predecessor.

The executable `trimDifferent` constructor guarantees more: it implies actual
overlap.  Its outer classifier guard is

```text
overlaps || (touches && sameValue)
```

and the constructor is reached only after `sameValue` is false.  Therefore the
guard reduces to `overlaps`.  The top-level proof obtains this fact directly
while reducing the classifier branch and passes its no-gap consequence to the
mutation semantics.  No classifier or executable-algorithm change was needed.

Boundary behavior:

| Predecessor / input | Values | Classifier result | Mutation premise |
| --- | --- | --- | --- |
| `[0,2]` / `[2,4]` | different | `trimDifferent` | true by overlap |
| `[0,1]` / `[2,4]` | different | `unaffected` | true by exact touching, though trim is not selected |
| `[0,0]` / `[2,4]` | any | `unaffected` | false: `0 + 1 < 2` |

Thus the former counterexample `[0,0]` followed by input `[2,3]` is excluded
from the corrected mutation contract.  Exact touching remains semantically
valid for `leftResidualBefore`, while the production classifier intentionally
routes it to merge only for equal values and otherwise leaves it unaffected.

## Forward scan

`scanForward_preserves_canonical_and_overwrite` proves one combined recursive
contract:

```text
Canonical (scanOutput scan)
runsToFunction (scanOutput scan) = runsToFunction (pending :: suffix)
```

The proof follows the classifier actions:

- an unstored exact-start cover returns the untouched suffix;
- equal-valued touching or overlapping runs merge into pending;
- differently-valued covered runs are deleted;
- an overhanging differently-valued run becomes one right residual;
- the first unaffected run stops the scan.

`scanForward_preserves_left_boundary` carries finalized-prefix ordering across
the same actions.  Two small unchanged-result lemmas justify the Rust fast
return: under a strict lower-bound suffix the scan cannot report unchanged,
and an unstored unchanged result means the suffix already represents pending.

## Top-level composition

`internalAddDMapRuns_preserves_canonical_and_overwrite` combines the cursor-gap
facts with each predecessor action.

- No predecessor and unaffected predecessor branches insert at the gap and
  scan forward.
- A same-valued touching or overlapping predecessor either already covers the
  input or becomes the stored pending run before scanning.
- A differently-valued overlapping predecessor keeps its left residual.  If
  it extends beyond the input, the right residual is emitted immediately;
  otherwise the fresh run scans the untouched suffix.

Every branch proves both canonical output and exact pointwise overwrite.  The
public `internalAddDMap` packages canonicality, and
`internalAddDMap_toFunction` projects the denotational result.  No executable
definition was changed while filling the proofs.

## Verification and metrics

The v3 collector (`a07fc3573ed0134219b1d539c2684d717707ab7360a8e0ba97602ef95549e048`)
compares the committed skeleton at
`251ff4b0b624b1b64dc6bd32926bb65c6f5e9c84` with the completed working tree.
The final Lean-source manifest is
`d6b4f7a461723919dcecc9b2f17a9ed70c5e7e35c144014aaf595f6839ebe5ca`.

| Metric | Skeleton | Proved |
| --- | ---: | ---: |
| AlgoDMap physical LOC | 226 | 1,326 |
| AlgoDMap active LOC | 180 | 1,256 |
| AlgoDMap private lemma/theorem declarations | 4 | 19 |
| AlgoDMap `induction` / `cases` / `by_cases` | 0 / 0 / 0 | 6 / 7 / 42 |
| AlgoDMap `have` / `rw` | 1 / 0 | 173 / 22 |
| Repository physical LOC | 4,375 | 5,475 |
| Repository active LOC | 3,709 | 4,785 |

The increase replaces four proof holes with explicit cursor-local reasoning;
definition counts and the public declaration count are unchanged.  Direct
compilation and the full Lake build complete without warnings, and the public
correctness theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`.
