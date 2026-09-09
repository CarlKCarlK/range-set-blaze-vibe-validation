# Phase 1: replace `pairwise_append_cross` with `List.pairwise_append`

Collected 2026-09-09 in `/home/carlk/programs/range-set-blaze-lean2`. This is
an uncommitted, independently reviewable Phase 1 proof-refactoring step.

## Identity

- Immediately preceding v2 source/artifact: commit `45f49aadea7960e3e3469568f455d696f338e5d3`, `metrics/phase1-pairwise-append-left-v2.json`
- Current v2 artifact: `metrics/phase1-pairwise-append-cross-v2.json`
- Collector: `scripts/phase0_metrics.py`, version 2
- Collector SHA-256: `4db7973927010a84c2b69cf1eb02d81703050c2a7e5c9ac7a51cb125c12a6ef5`
- Preceding source manifest SHA-256: `fa61cfb4bd5eb825e65330f6ba8679c532312f4417314c8e2250fdbd5b048111`
- Current source manifest SHA-256: `de824b9f2a055f69db89ad59d99d588123ada56078172cfe2cb11d92a7376dd0`
- Current `RangeSetBlaze/AlgoC.lean` SHA-256: `ad56fc7ac62c807908d41a091891110eb998b416be81ca9a885d80d7a647f2de`
- Current proof-source patch SHA-256 (`git diff --binary`): `38d87fa639c6fabbc8360a41b9f71e9fe78bf5269809228b6b04b370da8db318`

The JSON artifact was generated with:

```text
python3 scripts/phase0_metrics.py -o metrics/phase1-pairwise-append-cross-v2.json
```

## Exact source diff

```diff
diff --git a/RangeSetBlaze/AlgoC.lean b/RangeSetBlaze/AlgoC.lean
index af8830f..6d0d487 100644
--- a/RangeSetBlaze/AlgoC.lean
+++ b/RangeSetBlaze/AlgoC.lean
@@ -438,17 +437,0 @@ private lemma pairwise_prefix_last {α : Type _} (R : α → α → Prop)
-/-- Extract the cross-product property from Pairwise on an append. -/
-private lemma pairwise_append_cross {α : Type _} (R : α → α → Prop)
-    (xs ys : List α) (h : List.Pairwise R (xs ++ ys)) :
-    ∀ x ∈ xs, ∀ y ∈ ys, R x y := by
-  induction xs generalizing ys with
-  | nil => intros; contradiction
-  | cons x xs' ih =>
-      cases h with
-      | cons hx hrest =>
-          intro a ha y hy
-          simp at ha
-          cases ha with
-          | inl heq =>
-              rw [heq]
-              exact hx y (by simp [hy])
-          | inr hmem => exact ih ys hrest a hmem y hy
-
@@ -1598 +1581 @@ private def internalAddC_extendPrev_safe
-      have h_cross := pairwise_append_cross NR.before (init ++ [prev]) after h_ok_decomp
+      have h_cross := (List.pairwise_append.mp h_ok_decomp).2.2
@@ -1634 +1617 @@ private def internalAddC_extendPrev_safe
-        have hcross_init_prev := pairwise_append_cross NR.before init [prev] hpw_before
+        have hcross_init_prev := (List.pairwise_append.mp hpw_before).2.2
@@ -1908 +1891 @@ private lemma ok_deleteExtraNRs
-          exact pairwise_append_cross NR.before before rest hpw
+          exact (List.pairwise_append.mp hpw).2.2
@@ -2389 +2372 @@ theorem internalAddC_extendPrev_safe_toSet
-    have h_cross := pairwise_append_cross NR.before (init ++ [prev]) after h_ok_decomp
+    have h_cross := (List.pairwise_append.mp h_ok_decomp).2.2
```

No other Lean source changed. The helper's four active uses are:

1. `RangeSetBlaze/AlgoC.lean:1581`: `h_ok_decomp` in `internalAddC_extendPrev_safe`.
2. `RangeSetBlaze/AlgoC.lean:1617`: `hpw_before` in `internalAddC_extendPrev_safe`.
3. `RangeSetBlaze/AlgoC.lean:1891`: `hpw` in `ok_deleteExtraNRs`.
4. `RangeSetBlaze/AlgoC.lean:2372`: `h_ok_decomp` in `internalAddC_extendPrev_safe_toSet`.

The old helper has no remaining occurrences, including no disabled historical
occurrence. The existing `pairwise_append_left` projections, local
`pairwise_append` helper, theorem statements, and executable definitions were
not changed.

## Verification

| Command | Exit | Result |
|---|---:|---|
| `git diff --check` | 0 | Passed. |
| `lake build` | 0 | Build completed successfully (1874 jobs). |
| `lake env lean RangeSetBlaze/AlgoC.lean` | 0 | Direct compilation succeeded with no output. |
| `python3 scripts/test_phase0_metrics.py` | 0 | 3 tests passed. |
| `python3 scripts/phase0_metrics.py -o metrics/phase1-pairwise-append-cross-v2.json` | 0 | Corrected-v2 artifact written. |
| `lake env lean /tmp/range-set-blaze-phase1-cross-axioms.lean` | 0 | Axiom result recorded below. |

The aggregate build emitted only the pre-existing warning:

```text
warning: RangeSetBlaze/AlgoB.lean:465:8: try 'simp' instead of 'simpa'
```

It also emitted the five expected informational values from `Main.lean`; no
new or unexplained warning occurred.

The raw integrity search found only the known inactive opening comment matches:

```text
./RangeSetBlaze/AlgoC.lean:14:STATUS: Migrating away from unsafe constructors. Core invariant proofs COMPLETE!
./RangeSetBlaze/AlgoC.lean:40:  - some prev with gap: prev.val.hi + 1 < start (gap provided directly) ✅ WIRED (with sorry)
./RangeSetBlaze/AlgoC.lean:54:Current unsafe constructors (to eventually remove):
```

The comment-aware integrity scan reported:

```text
active sorry: False
active admit: False
active axiom: False
active unsafe: False
```

The axiom query returned exactly:

```text
'RangeSetBlaze.internalAddC_toSet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` dependency, and the set is unchanged from the preceding
v2 state.

## Corrected-v2 metric comparison

The comparison is against the immediately preceding v2 state at commit
`45f49aadea7960e3e3469568f455d696f338e5d3`, not the original Phase 0 baseline.

| Metric | preceding v2 | this v2 | delta |
|---|---:|---:|---:|
| Algo C physical LOC | 3303 | 3286 | -17 |
| Algo C nonblank LOC | 3043 | 3027 | -16 |
| Algo C blank LOC | 260 | 259 | -1 |
| Algo C comment-only LOC | 1074 | 1073 | -1 |
| Algo C active-code LOC | 1969 | 1954 | -15 |
| Algo C definitions | 10 | 10 | 0 |
| Algo C lemma/theorem declarations | 35 | 34 | -1 |
| Algo C private lemma/theorem declarations | 29 | 28 | -1 |
| Repository physical LOC | 4774 | 4757 | -17 |
| Repository nonblank LOC | 4387 | 4371 | -16 |
| Repository blank LOC | 387 | 386 | -1 |
| Repository comment-only LOC | 1149 | 1148 | -1 |
| Repository active-code LOC | 3238 | 3223 | -15 |
| Repository definitions | 52 | 52 | 0 |
| Repository lemma/theorem declarations | 70 | 69 | -1 |
| Repository private lemma/theorem declarations | 33 | 32 | -1 |
| `simp` tokens | 288 | 286 | -2 |
| `cases` tokens | 83 | 81 | -2 |
| `rw` tokens | 174 | 173 | -1 |

All other corrected-v2 lexical token totals are unchanged (`simpa`, `have`,
`linarith`, `omega`, `grind`, and `by_cases`). The measured deltas match the
prediction: deleting the 17-line helper removes 17 physical lines, including
one blank and one comment-only line, and 15 active-code lines. Its body
contained two `simp`, two `cases`, and one `rw`; the four direct projections
add none of those counted tactic tokens. The one removed lemma declaration
accounts for the declaration deltas. No measured delta differs from
prediction.

## Protected footprint

The diff contains only one private proof helper deletion and four proof-term
replacements. The protected production behavior in
`deleteExtraNRs_loop`, `deleteExtraNRs`, `internalAdd2NRs`,
`internalAddC_extendPrev_safe`, and `internalAddC` is unchanged: empty-input
handling, the `lo ≤ start` split, predecessor gap/coverage/touching branches,
the `next.lo ≤ current.hi + 1` merge condition, lower-endpoint preservation,
and `max` upper-endpoint behavior remain intact. The theorem statements,
including `internalAddC_toSet`, are unchanged. The exact diff has no changes to
an executable branch or algorithm condition.

## Git status

```text
## main...origin/main [ahead 1]
 M RangeSetBlaze/AlgoC.lean
?? metrics/phase1-pairwise-append-cross-v2.json
?? metrics/phase1-pairwise-append-cross-v2.md
```

No commit, tag, push, or staging was performed.
