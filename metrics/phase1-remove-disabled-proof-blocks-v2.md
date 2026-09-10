# Phase 1: remove disabled historical proof blocks

Collected 2026-09-09 in `/home/carlk/programs/range-set-blaze-lean2` as one
mechanical, comment-only Phase 1 review unit at pre-edit HEAD
`4dc31139bf0450d8ca37b7be996fa8c781b5dee8`.

## Scope and candidate comparison

The selected unit deletes all three large top-level disabled historical proof
blocks in `RangeSetBlaze/AlgoC.lean`, together with their orphan announcement
comments and separating blank lines. The opening session diary remains for a
separate decision. Active helper proofs and the main theorem remain unchanged.

| Candidate | Decision |
|---|---|
| Three disabled historical proof blocks | Selected; exact comment-only deletion with high navigation value. |
| Opening session diary | Deferred; replacing it requires choosing durable module documentation. |
| Active split/helper proofs | Retained; changing them would be a separate proof refactor. |

The path-scoped diff has no additions and 756 deletions. In the pre-edit file,
the two exact contiguous deletion chunks were:

| Pre-edit lines | Lines | Bytes | SHA-256 |
|---|---:|---:|---|
| 1753–2344 | 592 | 27,948 | `e899b27025d80bc4ccd9a64c5a77aa448edb2970c3f0c87091e4a576e9106fc3` |
| 2460–2623 | 164 | 7,791 | `c0929669c1545544afc5b62b7eb7465a7913993cc8892e823e925edc557c0b9a` |

Concatenating the exact deleted source lines gives 35,739 bytes with SHA-256
`a089ac1726553f0514dc0a8b793a7aeba6711e928e3ee43eeb10eed7dd7dc13c`.
The path-scoped binary diff SHA-256 is
`5c4006870d24dbb590a55ce918aa0c4aec7ff70f70c3ed4d47b572478f40c17e`.

No executable definition, active proof term, declaration, public theorem
statement, or opening module comment was changed.

## Identity and evidence

- Baseline artifact: `metrics/phase1-mathlib-list-membership-v2.json`
- Baseline artifact SHA-256: `5076e5aa85fbcdaf6f98c355a916043f9f4e755c2a20ad44190a7312e5171275`
- Baseline source manifest SHA-256: `7f7ecb165bc77fd844d3fece35a1598cc82f6df7802cc0f8b7dff61135458e88`
- Current artifact: `metrics/phase1-remove-disabled-proof-blocks-v2.json`
- Current artifact SHA-256: `4b11051c1ff865a2e2bbf6b8443abc67ad507bda3b1e45cf836f170f1848cff1`
- Current source manifest SHA-256: `850115df3c2befc4dd981cc91f5dcb1bcfaab2f3024902dc4a480791d4f46c85`
- Collector: `scripts/phase0_metrics.py`, version 2, SHA-256 `4db7973927010a84c2b69cf1eb02d81703050c2a7e5c9ac7a51cb125c12a6ef5`

The JSON parses, and a fresh corrected-v2 collection matches it byte-for-byte.

## Verification

Luna ran the complete standard verification set once for the finished batch:

| Check | Result |
|---|---|
| `git diff --check -- RangeSetBlaze/AlgoC.lean` | Passed. |
| `lake build` | Passed (1876 jobs); only the pre-existing AlgoB `unnecessarySimpa` warning and expected Main output. |
| `lake env lean RangeSetBlaze/AlgoC.lean` | Passed with no output. |
| Metric collector regression tests | 3 passed. |
| Comment-aware integrity scan | No active `sorry`, `admit`, `axiom`, or `unsafe`; no source axiom declaration. |
| Axiom query for `RangeSetBlaze.internalAddC_toSet` | `[propext, Classical.choice, Quot.sound]`; no `sorryAx`. |
| Protected executable-definition comparison | All five protected definitions unchanged. |
| Active public theorem-statement comparison | All six public statements unchanged. |

The comment-aware declaration counts, active-code LOC, and all tactic-token
counts are identical before and after, providing deterministic confirmation
that the deletion removed inactive text only.

## Corrected-v2 metric delta

| Metric | Immediate baseline | Current | Delta |
|---|---:|---:|---:|
| Algo C physical LOC | 2,627 | 1,871 | -756 |
| Algo C blank LOC | 207 | 132 | -75 |
| Algo C comment-only LOC | 932 | 251 | -681 |
| Algo C active-code LOC | 1,488 | 1,488 | 0 |
| Repository physical LOC | 4,098 | 3,342 | -756 |
| Repository blank LOC | 334 | 259 | -75 |
| Repository comment-only LOC | 1,007 | 326 | -681 |
| Repository active-code LOC | 2,757 | 2,757 | 0 |

This round claims no active-proof reduction.

From the corrected-v2 Phase 0 baseline, repository and Algo C physical LOC are
down 1,449 (`4,791 → 3,342` and `3,320 → 1,871`), while repository and Algo C
active-code LOC are down 495 (`3,252 → 2,757` and `1,983 → 1,488`).

## Working-tree note

The user-authored `.github/workflows/lean_action_ci.yml` modification is
unrelated, approved, preserved, and excluded from this round. Before commit,
the attributable state is the `AlgoC.lean` deletion plus this Markdown/JSON
pair. No push or tag was performed.
