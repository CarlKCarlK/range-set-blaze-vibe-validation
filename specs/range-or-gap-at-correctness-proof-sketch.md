# `range_or_gap_at` correctness proof sketch

## Meaning of the query

For a key `k`, Rust returns an inclusive range and the state throughout that
range.  For a set the state is a `bool`; for a map it is `Option<&V>`.

```text
domain minimum                                            domain maximum
      |                                                           |
      v                                                           v
------+====== stored ======+--------- gap --------+=== stored ===+------
                           hi                    lo
                                      ^ k
result:                    [hi + 1 .......... lo - 1], absent
```

The result is the maximal interval containing `k` on which the query state is
constant.  Thus a present set result is the canonical stored range.  A mapped
result is the canonical maximal same-valued run.  An absent result is the
complete gap between neighboring ranges/runs, extended to the finite domain
boundary when a neighbor is missing.

Set and map behavior differs at touching mapped runs.  Set ranges always have
a genuine absent key between them.  Map runs with different values may touch,
so querying either side returns that run and its value; there is no gap.

## Lean semantic contract

`MaximalConstantInterval state lower upper key range value` says:

1. `range` lies inside `[lower, upper]`;
2. `range` contains `key`;
3. `state x = value` at every point of `range`;
4. either `range.lo = lower`, or the preceding point has a different state;
5. either `range.hi = upper`, or the following point has a different state.

`RangeSetBlaze.QueryResultSpec` instantiates this with Boolean membership.
`RangeMapBlaze.QueryResultSpec` instantiates it with `map.toFunction`, whose
state is `Option Value`.  The map specification and theorems do not require
`DecidableEq Value`, because lookup returns a stored value but never compares
values.

The domain endpoints are explicit Lean arguments.  Rust's `Integer` trait has
concrete `min_value()` and `max_value()` endpoints, while this repository uses
mathematical `Int`.  `WithinDomain` connects the stored representation to the
chosen finite Rust-domain abstraction, and the correctness theorems require
the queried key to lie in it.

## Why the semantic answer is unique

Two candidate answers overlap at `key`, so their returned states agree there.
If one candidate began earlier, the point immediately before the later start
would simultaneously be inside the earlier constant interval and be required
to have a different state by the later interval's maximality.  This is
impossible.  The same next-point argument proves equal upper endpoints.
Consequently both the interval and state are equal.  This argument is shared
by sets and maps and is `maximalConstantInterval_unique`.

## Baseline set algorithm

The model splits canonical ranges after all starts `≤ key`, matching Rust's
`predecessor_range(key)` (`range(..=key).next_back()`).  It inspects the last
range of the prefix:

- if that range ends at or after `key`, it returns the stored range and
  `true`;
- otherwise the first suffix range supplies the right gap boundary;
- a missing predecessor uses the domain minimum;
- a missing successor uses the domain maximum;
- if both are missing, the whole domain is absent.

Canonical ordering proves that no stored range intersects a reported gap and
that the keys immediately outside a finite gap are present.

## Cursor set algorithm

The cursor model splits at starts `< key`, which is the semantics of
`lower_bound(Included(key))`: the last prefix range is `peek_prev`, and the
first suffix range is `peek_next`.  Unlike the baseline split, a range starting
exactly at `key` is on the right, so the model retains Rust's explicit
`key == start_next` branch.  The remaining predecessor, successor, leading,
trailing, and empty cases establish the same set specification.

## Baseline map algorithm

The baseline map model uses the same non-strict predecessor placement but
returns `some run.value` for a contained key.  Canonical `Run.before` proves
nonoverlap.  Its equal-value clause additionally proves that the points just
outside a stored run cannot have the same value; an adjacent run with a
different value is allowed and correctly witnesses maximality.

Gap branches prove `toFunction x = none` throughout the returned interval.
The neighboring endpoints, when present, evaluate to `some` values.

## Cursor map algorithm

The cursor map model uses the strict-start split and preserves the exact-start
`peek_next` branch.  It otherwise has the same seven cursor states as the set
model.  Geometry is proved from nonoverlap, while returned values are proved
from first-match `runsToFunction` semantics and canonical ordering.

## Why correctness implies implementation equivalence

```text
baseline executable ---- correctness ----\
                                         +-- unique semantic answer -- equality
cursor executable   ---- correctness ----/
```

`RangeSetBlaze.rangeOrGapAtBaseline_eq_cursor` and
`RangeMapBlaze.rangeOrGapAtBaseline_eq_cursor` each apply the two correctness
theorems and `maximalConstantInterval_unique`.  They contain no duplicated
algorithm-by-algorithm branch comparison.

## Boundary cases

The proofs cover empty collections, the key before the first range/run, at a
stored lower or upper endpoint, inside a stored piece, between pieces, after
the last piece, and at either modeled domain boundary.  Arithmetic is only
used where canonical/query inequalities prove that predecessor or successor
exists inside the domain.

Rust `Integer` successor/predecessor can skip holes in a non-dense carrier,
notably the invalid Unicode surrogate region for `char`.  The existing Lean
model uses dense mathematical integers, so `+ 1` and `- 1` model the integer
instances directly.  The Rust cursor tests separately validate cursor versus
baseline behavior for `char` around `D7FF/E000`; this proof does not claim a
formal model of Rust's generic `Integer` trait or `BTreeMap` implementation.

## Cursor assumptions modeled versus externally validated

Lean models the documented cursor semantics as an ordered-list gap:
`left` contains starts strictly below the lower bound, `right` contains starts
at or above it, and their last/first elements represent `peek_prev` and
`peek_next`.  It does not formalize B-tree balancing, cursor mutation,
lifetimes, feature gating, or lookup complexity.  Rust's exhaustive `u8`,
randomized `i16`, endpoint, and `char` tests corroborate this cursor-placement
assumption independently of the proof.
