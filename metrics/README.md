# Metric artifacts

The `phase1-mknr-cleanup.*` files are v1 historical evidence. They were
collected with the original frozen `scripts/phase0_metrics.py`, whose
apostrophe handling treated primed Lean identifiers such as `mkNR'` as the
start of a character literal. Those artifacts are preserved unchanged.

The `*-v2.json` files are the corrected metric series. The v2 collector is
versioned as `collector_version: 2`, records its SHA-256, and records the
exact Git source identity or working-tree source-byte manifest. It recognizes
plausible character literals while leaving identifier primes in code.

Only like-version comparisons are valid: compare v1 artifacts with v1
artifacts, and v2 artifacts with v2 artifacts. The frozen Phase 0 files in
`specs/` are likewise historical and must not be overwritten.
