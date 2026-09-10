# Repository guidance

Before substantive proof or refactoring work, read:

- `specs/lean-proof-refactoring.md`
- `specs/proof-api-style.md`

Preserve Algo C's production-shaped algorithm unless the task explicitly authorizes algorithm changes. Do not silently broaden a scoped refactoring unit, and preserve unrelated user and workspace changes.

Treat proof-API naming and documentation quality as first-class concerns. Prefer existing Lean and Mathlib abstractions over local re-proofs when they improve clarity. Measure active proof/code LOC separately from comment-only LOC: useful explanatory comments have no golf penalty.

For measured refactoring work, use the repository's corrected-v2 metric collector and integrity checks. Use Sol for design and review, and Luna for bounded mechanical implementation and verification when Luna is available.
