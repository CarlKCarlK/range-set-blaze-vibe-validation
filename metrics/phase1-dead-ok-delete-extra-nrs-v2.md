# Phase 1: delete dead `ok_deleteExtraNRs`

Collected 2026-09-09 in `/home/carlk/programs/range-set-blaze-lean2` as one
uncommitted mechanical Phase 1 review unit.

## Identity and baseline

- Baseline corrected-v2 artifact: `metrics/phase1-list-while-batch-v2.json`
- Baseline artifact SHA-256: `7f5337973b35e005d5ceae3db248cb28a23097e728cceea254b74886caeef55b`
- Baseline source commit/tree: `7dcd1bf18d6245325d5ebc6801eb6869605ec8db` / `f5d1b17c26b664f15c71ada35e0c28a031ab6d7b`
- Current source commit/tree: `ff4e4f85a5aad34583a2771707adb3f8c5eeac47` / `8f17d8ae7f6e2348ec2b823dd7d5d0b743c8ac7e`
- Collector: `scripts/phase0_metrics.py`, version 2
- Collector SHA-256: `4db7973927010a84c2b69cf1eb02d81703050c2a7e5c9ac7a51cb125c12a6ef5`
- Current source manifest SHA-256: `18bf4898ab8131e5802f60f4e4f8daf9133aba4345f048c137e8ddd66ae782e`
- Current `RangeSetBlaze/AlgoC.lean` SHA-256: `bac3fec775fe5621f1474657affb3df9314ad8385c8606a06b1a632839041437`
- Current evidence JSON SHA-256: `5cc2c7718862c5aba1ae456490b08bcd63db2c400733159ef2b904bf6c3bf2c2`
- Proof-source patch SHA-256 (`git diff --binary`): `626fdb717306cbeafaf35ca76290ffd98e5d4c7d9f2780d6d996a84cf08864e2`

## Candidate, active-reference check, and exact scope

The selected candidate is the unused private lemma `ok_deleteExtraNRs` in
`RangeSetBlaze/AlgoC.lean`.  The directly attached documentation block begins
`/-- Invariant preservation: deleteExtraNRs...` and was deleted with the
lemma.  Comment-aware token-bounded analysis using the `strip_comments` logic
from `scripts/phase0_metrics.py` found no active exact references after the
deletion (before deletion, the only active exact occurrence was the
declaration itself).  The disabled historical references and opening status
comments were not edited.

The exact source diff is one file, with **0 insertions and 230 deletions**:

```text
RangeSetBlaze/AlgoC.lean | 230 -----------------------------------------------
1 file changed, 230 deletions(-)
```

The deleted block is 230 lines / 11,626 bytes, SHA-256
`4fc371bc7c04ba034bd80b26871c1dab368636b752edfdbc2b74708b3fb07c97`.
No executable definition, theorem statement, disabled historical block, or
unrelated source was changed.

### Four-candidate audit

All four audited private proof candidates had declaration-only active
references before deletion under the same comment-aware analysis.  The
active-code LOC estimates and disabled raw-reference coordinates below are
from the pre-delete source (so later line shifts do not apply):

| Candidate | Active-code LOC | Active references before deletion | Disabled raw references (pre-delete) | Scope/decision |
|---|---:|---|---|---|
| `deleteExtraNRs_loop_preserves_sets` | 39 | Declaration only | `AlgoC.lean:2900–2901` | Deferred: loop set-preservation proof cluster. |
| `chain_replace_suffix_same_lo` | 54 | Declaration only | `AlgoC.lean:2768–2769` | Deferred: chain-replacement proof cluster. |
| `ok_deleteExtraNRs` | 147 | Declaration only; deleted here | Opening status references at `AlgoC.lean:18,25` | Selected: dead invariant-preservation proof. |
| `deleteExtraNRs_sets_after_splice_of_chain` | 94 | Declaration only | `AlgoC.lean:2361,2771,2780` | Deferred: splice/set-preservation proof cluster. |

Each candidate is private, proof-only, and has no public/API or executable
impact.  The other three are deferred as separate review units because their
proofs belong to materially different loop, chain-replacement, and
splice/set-preservation clusters; they should not be bundled into this narrow
deletion.

## Commands and results

| Command | Exit | Result |
|---|---:|---|
| `git diff --check` | 0 | Passed. |
| `lake build` | 0 | Completed successfully (1876 jobs). |
| `lake env lean RangeSetBlaze/AlgoC.lean` | 0 | Direct compilation succeeded with no output. |
| `python3 scripts/test_phase0_metrics.py` | 0 | 3 tests passed. |
| `python3 scripts/phase0_metrics.py -o metrics/phase1-dead-ok-delete-extra-nrs-v2.json` | 0 | Corrected-v2 artifact written. |
| raw integrity search | 0 | Only the three known inactive opening-comment matches at AlgoC lines 15, 41, and 55. |
| comment-aware integrity scan | 0 | No active `sorry`, `admit`, `axiom`, or `unsafe`; no active source axiom declarations. |
| temporary `#print axioms RangeSetBlaze.internalAddC_toSet` | 0 | Exact output recorded below. |
| protected footprint and public statement verification | 0 | All protected bodies and listed public statements match HEAD byte-for-byte. |

`lake build` emitted only the pre-existing `AlgoB.lean:465` unnecessary-
`simpa` linter warning and the five expected informational values from
`Main.lean`; there were no new or unexplained warnings.

The comment-aware scan output was:

```text
active sorry: False
active admit: False
active axiom: False
active unsafe: False
active matches: []
active axiom declarations: []
```

The exact axiom output was:

```text
'RangeSetBlaze.internalAddC_toSet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` dependency.

## Corrected-v2 aggregate delta

Comparison is against `metrics/phase1-list-while-batch-v2.json`.

| Metric | Baseline | Current | Delta |
|---|---:|---:|---:|
| Algo C physical LOC | 3219 | 2989 | -230 |
| Algo C nonblank LOC | 2965 | 2750 | -215 |
| Algo C blank LOC | 254 | 239 | -15 |
| Algo C comment-only LOC | 1070 | 1002 | -68 |
| Algo C active-code LOC | 1895 | 1748 | -147 |
| Algo C definitions | 10 | 10 | 0 |
| Algo C lemma/theorem declarations | 29 | 28 | -1 |
| Algo C private lemma/theorem declarations | 23 | 22 | -1 |
| Repository physical LOC | 4690 | 4460 | -230 |
| Repository nonblank LOC | 4309 | 4094 | -215 |
| Repository blank LOC | 381 | 366 | -15 |
| Repository comment-only LOC | 1145 | 1077 | -68 |
| Repository active-code LOC | 3164 | 3017 | -147 |
| Repository definitions | 52 | 52 | 0 |
| Repository lemma/theorem declarations | 64 | 63 | -1 |
| Repository private lemma/theorem declarations | 27 | 26 | -1 |
| `by_cases` tokens | 24 | 23 | -1 |
| `cases` tokens | 75 | 70 | -5 |
| `grind` tokens | 0 | 0 | 0 |
| `have` tokens | 691 | 652 | -39 |
| `linarith` tokens | 12 | 12 | 0 |
| `omega` tokens | 15 | 11 | -4 |
| `rw` tokens | 180 | 164 | -16 |
| `simp` tokens | 279 | 266 | -13 |
| `simpa` tokens | 86 | 85 | -1 |

## Protected executable footprint

The following declaration spans were compared between HEAD and the current
source after excluding the removed target block where needed.  Every hash
matched exactly:

| Protected body | Lines | SHA-256 |
|---|---:|---|
| `deleteExtraNRs_loop` | 39 | `f39036c4e1dc107b9cdbcdd9e0f11347044f9bb73edcf0ab16b59fc46387a0a6` |
| `deleteExtraNRs` | 15 | `d945b0e942910e4526bd2e18c1a869e4b835f267547ff73d339b98594669aefb` |
| `internalAdd2NRs` | 18 | `0ab75a1b409efdf4e8c66f52ddf1a48e8fe427a86a705861b04de189edbc2ca2` |
| `internalAddC_extendPrev_safe` | 189 | `6f0f081bd05c921b3b6f56650178865956d608e8ddc82d6f802d791a5c83c0eb` |
| `internalAddC` | 53 | `c76f99bb4f265212eb06bf28a5afb4b83d158ed4e5a5fd8b938e2bc720db8c7b` |

Thus empty-input handling, the `lo ≤ start` split, predecessor gap/coverage/
touching branches, the `next.lo ≤ current.hi + 1` merge condition, lower
endpoint preservation, and `max` upper-endpoint behavior are unchanged.

## Public theorem statements unchanged

The active public theorem statements were captured exactly from HEAD and the
current source.  Their statement hashes are unchanged:

```lean
theorem getLast?_eq_some_getLast {α : Type*} {xs : List α} {x : α} (h : xs.getLast? = some x) :
    ∃ hne : xs ≠ [], xs.getLast hne = x

theorem internalAdd2_safe_toSet
    (s : RangeSetBlaze) (r : IntRange)
    (hgap_lt :
      let split := List.span (fun nr => decide (nr.val.lo < r.lo)) s.ranges
      let before := split.fst
      before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < r.lo) :
  (internalAdd2_safe s r hgap_lt).toSet = s.toSet ∪ r.toSet

theorem internalAdd2_safe_from_le_toSet
    (s : RangeSetBlaze) (r : IntRange)
    (hgap_le :
      let split := List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges
      let before := split.fst
      before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < r.lo) :
  (internalAdd2_safe_from_le s r hgap_le).toSet = s.toSet ∪ r.toSet

theorem internalAddC_extendPrev_safe_toSet
    (s : RangeSetBlaze) (r : IntRange)
    (start stop : Int)
    (before after : List NR) (prev : NR)
    (hDecomp : List.span (fun nr => decide (nr.val.lo ≤ start)) s.ranges = (before, after))
    (hLast : List.getLast? before = some prev)
    (hNoGap : ¬ (prev.val.hi + 1 < start))
    (hExtend : prev.val.hi < stop)
    (hStartEq : start = r.lo)
    (hStopEq : stop = r.hi) :
  (internalAddC_extendPrev_safe s r start stop before after prev hDecomp hLast hNoGap hExtend).toSet
    = s.toSet ∪ r.toSet

theorem internalAddC_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAddC s r).toSet = s.toSet ∪ r.toSet
```

Statement SHA-256 values, in the same order, are
`26c5561c8078309c09e3273e562f4af0dbc0e2de7445a8ee827593206c971f1a`,
`6d1083268f3e292e89fd33b96346fd100bc29b29bc739e393de33892873dd3ba`,
`8e2203fdcdc7ce43e990d659b43ef3512b02a1c2a68c86706c2d3c5fdbe9b15d`,
`2b1c51d8adf1df6e41617da47efa473ed3b43d68b79fa8df569e044adc1fed6e`, and
`979cda627e9e7c546fedddb1455db7560f72de1ee25c04e656792e7fecdcf3e2`.
The two disabled historical public theorem blocks (`internalAdd2_toSet` and
`internalAddC_extendPrev_toSet`) were also left untouched.

## Git status

```text
 M RangeSetBlaze/AlgoC.lean
?? metrics/phase1-dead-ok-delete-extra-nrs-v2.json
?? metrics/phase1-dead-ok-delete-extra-nrs-v2.md
```

No commit, tag, push, or staging was performed.
