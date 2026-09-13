# Canonical representation uniqueness

This note explains why the canonical range-set and range-map representations
in this repository are unique. It describes the mathematics rather than the
Lean tactic scripts.

## Sets

A canonical range set is a list of nonempty closed integer intervals. Earlier
intervals precede later intervals with at least one missing integer between
them. Consequently, the first interval has the least represented integer.

Suppose two canonical lists represent the same set. Neither list can be empty
unless the other is: the lower endpoint of a nonempty list's first interval is
represented. For two nonempty lists, equality of their represented sets shows
that each first lower endpoint is at least the other, so the lower endpoints
are equal.

The upper endpoints must also be equal. If one first interval ended earlier,
the integer immediately after that endpoint would lie in the other first
interval. It cannot lie in the earlier-ending interval, and it cannot lie in
that list's tail because canonical ranges have a genuine gap. This contradicts
equality of the represented sets.

Thus the first intervals agree. Tail ranges lie strictly above the common
first interval, so equality of the whole represented sets reduces to equality
of the represented tails. Induction finishes the proof.

In Lean, the raw-list result is
`RangeSetBlaze.ranges_eq_of_canonical_of_rangesToSet_eq`. The packaged result
`RangeSetBlaze.ext` obtains both canonicality hypotheses from the
two `RangeSetBlaze` values.

## Maps

A canonical range map is a list of nonempty labeled runs. Runs are ordered and
nonoverlapping. Touching runs may carry different values, but touching runs
with the same value are forbidden: equal-valued neighbors must have a genuine
integer gap.

For two canonical run lists representing the same partial function, the same
least-key argument forces the first lower endpoints to agree. Evaluating the
functions at that common key then forces the first values to agree.

To compare upper endpoints, suppose one first run ends earlier and inspect the
next integer. The longer first run maps it to the common first value. In the
shorter representation, the first run no longer covers the key. A later run
cannot produce that same value there: if it starts at the next integer, the
equal-value maximality condition is violated, and if it starts later, the key
is unmapped. Hence the first upper endpoints agree.

The first runs are therefore identical. Outside their common interval,
equality of the whole functions is equality of the tail functions. Inside the
interval, canonical ordering ensures both tails are unmapped. Induction then
proves that the complete run lists agree.

The maximality clause is essential. Without it, one run labeled `v` on
`[1, 4]` and two touching runs labeled `v` on `[1, 2]` and `[3, 4]` would be
distinct representations of the same function.

In Lean, the raw-list result is
`RangeMapBlaze.runs_eq_of_canonical_of_runsToFunction_eq`. The packaged result
is `RangeMapBlaze.ext`.

## Cross-algorithm equality

Every insertion algorithm already proves the same denotational contract:
set insertion represents union, and map insertion represents pointwise
overwrite. Each algorithm also packages a canonical result. The new packaged
uniqueness theorems therefore turn equal denotations directly into equality of
the complete structures.

`RangeSetBlaze/CrossAlgorithm.lean` uses Algo A as the set reference and Algo
AMap as the map reference. This hub gives three set equalities and two map
equalities without an all-pairs theorem family. Other pairwise facts follow by
symmetry and transitivity. The cached-length variants retain their existing
exact correspondence theorems to C or D, so no redundant Len comparison proof
is needed.
