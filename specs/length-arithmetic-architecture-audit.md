# Length arithmetic architecture audit

Date: 2026-09-12

## Scope and source identity

This audit compares the cached-length variants CLen, DLen, CMapLen, and
DMapLen. The exact before-state is clean commit
`5fd6307d4230498727bf10809d0d26280eb72a46` (tree
`55370cf26faf0af29de0ac44511b271ceae88851`). The v3 Lean-source manifest was
`8895f29a062c0bc53830738ec297ab01384093e6205013218b6c05ec131fb659`;
the collector SHA-256 was
`a07fc3573ed0134219b1d539c2684d717707ab7360a8e0ba97602ef95549e048`.

No Rust source is changed. Exact representation correspondence and the
existing algorithm branch structures remain protected.

## Before-state matrix

All semantic cardinalities were already `Nat`: `IntRange.cardinality`,
`rangesCardinality`, `RangeSetBlaze.cardinality`, `Run.cardinality`,
`runsCardinality`, and `RangeMapBlaze.cardinality` all return `Nat`.

| Dimension | CLen | DLen | CMapLen | DMapLen |
| --- | --- | --- | --- | --- |
| Semantic cardinality | `Nat` | `Nat` | `Nat` | `Nat` |
| Public cache input | `Nat` | `Int` | `Nat` | `Nat` |
| Public cache result | `Nat` | `Int` | `Nat` | `Nat` |
| Private cache | `Nat` | `Int` | `Nat` | `Int` |
| Nat/Int boundary | none | every cardinality update and invariant casts `Nat -> Int`; no conversion back | none | public wrapper casts `Nat -> Int`, updates cast cardinalities, result uses `Int.toNat` |
| Internal subtraction | successor removal | successor removal | successor removal and predecessor trim | successor removal and predecessor trim |
| Executable subtraction expressions | 1 | 1 | 3 | 4 |
| Explicit non-underflow facts | 1 | 0 | 4 | 0 |
| Natural invariant | `cache = base + pending suffix` | same, with casts | `cache = base + stored pending + suffix` | same, with casts |
| Rust unsigned correspondence | update order and every reachable subtraction is safe | update order only; signed arithmetic | update order and every reachable subtraction is safe | update order only; signed private arithmetic |
| Conversion noise in section | none | 39 code-only `Int.ofNat` occurrences | none | 43 `Int.ofNat` occurrences plus two `toNat` boundary expressions |
| Type-specific proof cost | one local four-line safety argument | casts throughout executable and proof equations | four local safety facts, about 11 active lines | casts throughout executable, invariant, decompositions, and wrapper |

The difference between conceptual subtraction sites and source expressions is
intentional. The map scans have several branch expressions for removing a
successor but only two kinds of removal: successor removal and predecessor
tail trimming.

## Candidate comparison and decision

The final architecture is Candidate A:

- semantic cardinality: `Nat`;
- public cached-length input and output: `Nat`;
- private cached-length bookkeeping: `Nat`;
- no Nat/Int conversion boundary;
- additive proof invariants that expose every removed cardinality as a summand;
- an explicit local containment fact before reasoning about each `Nat.sub`.

This wins for four reasons.

First, cardinality is intrinsically nonnegative and every semantic cardinality
API already uses `Nat`. DLen's signed public API was the only public outlier,
while DMapLen's private signed layer introduced a conversion boundary that the
other map algorithm did not need.

Second, the completed Nat proofs show that non-underflow is not dominant.
CLen needs one local fact. CMapLen, despite value-sensitive merging, successor
deletion, predecessor trimming, and right residuals, needs four. The facts are
short consequences of the cache decomposition, not new endpoint or ordering
proofs.

Third, DLen and DMapLen already used the correct invariant shape over `Int`.
Removing casts turns those statements directly into the Nat invariants already
used by their C counterparts. In a recursive successor branch,
`runsCardinality (next :: rest)` or `rangesCardinality (next :: rest)` makes
`next.cardinality` a visible summand. In the predecessor-trim branch, the
existing left-residual cardinality equation makes the removed tail a summand of
the predecessor, which is itself a summand of the whole cache.

Fourth, Nat proves a stronger production-relevant property. Rust uses unsigned
`SafeLen`; the Lean proof now establishes that every reachable subtraction is
safe in the unsigned sense. This remains a mathematical, unbounded model: it
does not prove machine-width capacity or overflow bounds for Rust's concrete
`SafeLen` type.

Candidate B, Int internally, does simplify raw subtraction because group
subtraction is total. Its benefit is limited to avoiding one set-scan or four
map-scan safety facts. In exchange it adds casts to every update, invariant,
decomposition, and sometimes the public wrapper. It models control flow and
add/subtract order, and final correctness proves a nonnegative result, but it
does not itself establish unsigned safety at each intermediate removal.
Accordingly, Int-internal is not the final abstraction.

## Evidence from the four completed proofs

- CLen's invariant is
  `cachedLength = base + rangesCardinality pending`. Its merge branch derives
  `next.cardinality <= cachedLength` before using `Nat.sub_eq_iff_eq_add`.
- DLen had exactly the same cached-base invariant with `Int.ofNat` around the
  suffix. Its Nat normalization removes the casts and adds the same single
  local safety fact as CLen.
- CMapLen's invariant is
  `cachedLength = base + storedPendingContribution + runsCardinality suffix`.
  Three scan branches and one predecessor-trim branch name containment facts;
  this is direct evidence that the more complex map family remains clean over
  Nat.
- DMapLen had the same map invariant over `Int`. Its Nat normalization needs
  the expected four local facts and no new proof architecture.

The repository history also supports this interpretation. DLen and DMapLen
were initially scaffolded with Nat; their later Int forms were proof-completion
choices, not consequences of cursor semantics. CMapLen subsequently completed
the harder Nat arithmetic pattern needed by DMapLen.

## Changes made

CLen and CMapLen were already in the chosen final architecture and are
unchanged.

DLen now uses Nat for `DLenResult.cachedLength`, its raw and scan result fields,
all private helper arguments/results, `internalAddDLen`, and the public
cached-length theorem. All `Int.ofNat` bookkeeping casts were removed. The
scan invariant now states its additive equation directly over Nat and supplies
one named successor-removal non-underflow fact.

DMapLen retains its already-Nat public API and now uses Nat in its private raw
and scan result fields and all helper arguments/results. Per-update
`Int.ofNat` casts, the wrapper's `Nat -> Int` conversion, and the final
`Int.toNat` conversion were removed. The scan proof names three successor
removal facts; the dispatcher proof names one predecessor-trim fact.

No executable branch, represented semantics, or exact correspondence theorem
was weakened. No generic Len framework was introduced.

## Shared arithmetic lemmas

No new shared lemma was needed. The existing stable vocabulary is sufficient:

- `IntRange.rightExtensionCardinality`;
- `NR.cardinality_eq_add_right_extension`;
- `rangesCardinality_append` and `runsCardinality_append`;
- the left-residual, right-residual, and three-way interval cardinality
  decompositions in `Basic.lean`.

The remaining non-underflow facts are operation-local consequences of
different scan states. Promoting them would expose algorithm-specific state or
create a generic framework solely for symmetry.

## Before/after v3 section metrics

These are comment-aware v3 slices from each cached-length section marker to
EOF. Metrics are independent review signals, not a composite score.

| Implementation | Physical LOC before/after | Active LOC before/after | `have` before/after | `omega` before/after | Private/public proofs before/after |
| --- | ---: | ---: | ---: | ---: | ---: |
| CLen | 580 / 580 | 507 / 507 | 55 / 55 | 8 / 8 | 9/3 / 9/3 |
| DLen | 504 / 495 | 453 / 442 | 39 / 39 | 6 / 7 | 8/3 / 8/3 |
| CMapLen | 517 / 517 | 455 / 455 | 41 / 41 | 18 / 18 | 6/3 / 6/3 |
| DMapLen | 597 / 603 | 533 / 540 | 40 / 44 | 12 / 16 | 6/3 / 6/3 |

DLen becomes smaller because cast plumbing disappears. DMapLen grows by eight
active lines because the four unsigned-safety facts are now explicit. That
small increase establishes a stronger property and removes 43 casts plus the
wrapper conversion boundary; it is not a proof-complexity regression hidden by
movement to another module.

## Intentional non-uniformity

Arithmetic types and invariant principles are now uniform. Algorithm-specific
state remains intentionally non-uniform: CLen follows Algo C's span/list scan,
DLen follows the cursor gap, and the two map variants retain their distinct
scan results, classifiers, residual handling, and reconstruction. These are
real algorithm/representation differences and are not arithmetic architecture.

## Verification

All required checks passed:

- direct compilation of `RangeSetBlaze/AlgoC.lean`,
  `RangeSetBlaze/AlgoD.lean`, `RangeSetBlaze/AlgoCMap.lean`, and
  `RangeSetBlaze/AlgoDMap.lean`;
- `lake env lean RangeSetBlaze.lean`;
- `lake build` (1,886 jobs; only the executable's expected `#eval` output);
- all six v3 metric collector regression tests;
- `git diff --check`;
- Lean-source scan found no `sorry`, `admit`, source `axiom`, `unsafe`,
  `implemented_by`, or `sorryAx`;
- each of the twelve public Len theorems (representation result,
  cached-length correctness, and inherited semantics for all four variants)
  depends on exactly `[propext, Classical.choice, Quot.sound]`.

The final v3 Lean-source manifest is
`6d6d150c0cd30f2935915a18829282feebe64e02abdfc69450926d706c6885f7`.
The repository-owned Lean totals are 7,575 physical LOC and 6,607 active LOC.
No files were staged, committed, pushed, or tagged.

## Final recommendation

The Nat/Int question is settled for these four mathematical Len models:
use Nat for semantic, public, and private cardinality, with additive invariants
and explicit local non-underflow facts. Reopen the decision only if a future
model introduces genuinely signed intermediate quantities rather than an
absolute cached cardinality. A separate bounded `SafeLen` refinement may add
machine-width overflow proofs without changing this Nat architecture.
