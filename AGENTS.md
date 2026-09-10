# Repository guidance

Before substantive proof or refactoring work, read:

- `specs/lean-proof-refactoring.md`
- `specs/proof-api-style.md`
- `specs/phase3-proof-architecture-endpoint.md` for the frozen Algo C architecture and Phase 4 boundary

Phase 3 is complete. Treat further Algo C work as stabilization or narrowly
scoped maintenance, not as a continuing proof-compression campaign.

Preserve Algo C's production-shaped algorithm unless the task explicitly authorizes algorithm changes. Do not silently broaden a scoped refactoring unit, and preserve unrelated user and workspace changes.

Treat proof-API naming and documentation quality as first-class concerns. Prefer existing Lean and Mathlib abstractions over local re-proofs when they improve clarity. Measure active proof/code LOC separately from comment-only LOC: useful explanatory comments have no golf penalty.

For measured refactoring work, use the repository's corrected-v2 metric collector and integrity checks. Use Sol for design and review, and Luna for bounded mechanical implementation and verification when Luna is available.

For metric definitions, interpretation rules, schema compatibility, and the
permanent proof-complexity dashboard, read `specs/proof-metrics.md`. Metrics
are a vector of signals, never a composite quality score.
