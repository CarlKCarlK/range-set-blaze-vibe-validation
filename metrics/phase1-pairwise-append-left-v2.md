# Phase 1: replace `pairwise_append_left` with `List.pairwise_append`

Collected 2026-09-09 in `/home/carlk/programs/range-set-blaze-lean2`. This is
an uncommitted, independently reviewable Phase 1 proof-refactoring step.

## Identity

- Immediately preceding v2 artifact: `metrics/phase1-mknr-cleanup-v2.json`
- Current v2 artifact: `metrics/phase1-pairwise-append-left-v2.json`
- Collector version: `2`
- Collector SHA-256: `4db7973927010a84c2b69cf1eb02d81703050c2a7e5c9ac7a51cb125c12a6ef5`
- Preceding v2 source base commit: `54893d0f953596b87471b4f74d20e94eefc3726b`
- Current source base commit: `b141f966aac8071ff94eb3eda3a1d0df74a4a35e`
- Current `RangeSetBlaze/AlgoC.lean` SHA-256: `5b4f3e92d67f1c463f74851c14bdc45bcfd7a3195e7f11464439da0f0bd51cab`
- Current v2 source-byte manifest SHA-256: `fa61cfb4bd5eb825e65330f6ba8679c532312f4417314c8e2250fdbd5b048111`
- Current patch SHA-256 (`git diff --binary`): `903c8efed8960a4b2ff17314d61fcb6ee612a50cb99e8e621924f56d80b79182`

The source metrics artifact was generated with:

```text
python3 scripts/phase0_metrics.py -o metrics/phase1-pairwise-append-left-v2.json
```

The metrics artifacts are evidence and were not included in the proof-source
patch comparison.

## Exact source diff

```diff
diff --git a/RangeSetBlaze/AlgoC.lean b/RangeSetBlaze/AlgoC.lean
index 908cde5..af8830f 100644
--- a/RangeSetBlaze/AlgoC.lean
+++ b/RangeSetBlaze/AlgoC.lean
@@ -435,20 +435,6 @@ private lemma pairwise_prefix_last {α : Type _} (R : α → α → Prop)
           | cons _ hrest =>
               exact ih hrest htail

-/-- Extract Pairwise on the left part of an append. -/
-private lemma pairwise_append_left {α : Type _} (R : α → α → Prop)
-    (xs ys : List α) (h : List.Pairwise R (xs ++ ys)) :
-    List.Pairwise R xs := by
-  induction xs generalizing ys with
-  | nil => constructor
-  | cons x xs' ih =>
-      cases h with
-      | cons hx hrest =>
-          constructor
-          · intro y hy
-            exact hx y (by simp [hy])
-          · exact ih ys hrest

 /-- Extract the cross-product property from Pairwise on an append. -/
 private lemma pairwise_append_cross {α : Type _} (R : α → α → Prop)
@@ -1009,7 +995,7 @@ private lemma ok_internalAdd2NRs (xs : List NR) (start stop : Int) (h_le : start
             exact this.2
           rw [h1, h2]
     rw [h_xs_decomp] at hpw
-    exact pairwise_append_left NR.before before after hpw
+    exact (List.pairwise_append.mp hpw).1

  -- Step 2: Extract Pairwise on after
   have hpw_after : List.Pairwise NR.before after := by
@@ -1400,7 +1386,7 @@ def internalAdd2_safe_from_le (s : RangeSetBlaze) (r : IntRange)
                 have h_ok_decomp : List.Pairwise (· ≺ ·) (s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) ++
                                                            s.ranges.dropWhile (fun nr => decide (nr.val.lo ≤ r.lo))) := by
                   rw [h_decomp]; exact s.ok
-                exact pairwise_append_left (· ≺ ·) _ _ h_ok_decomp
+                exact (List.pairwise_append.mp h_ok_decomp).1

              -- Now apply it to before_le
               have h_pw_before : List.Pairwise (· ≺ ·) before_le := by
@@ -1515,7 +1501,7 @@ private def internalAddC_extendPrev_safe
             rw [h1, h2]
       have h_ok_decomp : List.Pairwise NR.before (before ++ after) := by
         rw [← h_s_decomp]; exact s.ok
-      exact pairwise_append_left NR.before before after h_ok_decomp
+      exact (List.pairwise_append.mp h_ok_decomp).1

    -- Extract Pairwise for init using dropLast
     have hpw_init : List.Pairwise NR.before init := by
@@ -1523,7 +1509,7 @@ private def internalAddC_extendPrev_safe
       have : before = init ++ [before.getLast hne'] := (List.dropLast_append_getLast hne').symm
       rw [heq] at this
       rw [this] at hpw_before
-      exact pairwise_append_left NR.before init [prev] hpw_before
+      exact (List.pairwise_append.mp hpw_before).1

    -- Extract Pairwise for after from s.ok
     have hpw_after : List.Pairwise NR.before after := by
@@ -1756,7 +1742,7 @@ private lemma ok_deleteExtraNRs
     -- Extract Pairwise on before and rest
     have hpw_before : List.Pairwise NR.before before := by
       rw [h_xs_decomp] at hpw
-      exact pairwise_append_left NR.before before rest hpw
+      exact (List.pairwise_append.mp hpw).1

    have hpw_rest : List.Pairwise NR.before rest := by
```

## Five active replacement sites

1. `RangeSetBlaze/AlgoC.lean:998`: `hpw` in `ok_internalAdd2NRs` → `(List.pairwise_append.mp hpw).1`.
2. `RangeSetBlaze/AlgoC.lean:1389`: `h_ok_decomp` in `internalAdd2_safe_from_le` → `(List.pairwise_append.mp h_ok_decomp).1`.
3. `RangeSetBlaze/AlgoC.lean:1504`: `h_ok_decomp` in `internalAddC_extendPrev_safe` → `(List.pairwise_append.mp h_ok_decomp).1`.
4. `RangeSetBlaze/AlgoC.lean:1512`: `hpw_before` in `internalAddC_extendPrev_safe` → `(List.pairwise_append.mp hpw_before).1`.
5. `RangeSetBlaze/AlgoC.lean:1745`: `hpw` in `ok_deleteExtraNRs` → `(List.pairwise_append.mp hpw).1`.

The textual occurrence at line 2886 remains in a disabled historical proof block,
as required. `pairwise_append_cross` and the local `pairwise_append` helper are
unchanged.

## Verification

`git diff --check` succeeded.

| Command | Exit | Elapsed | Result |
|---|---:|---:|---|
| `lake build` | 0 | 0.96 s | Warm replay; build completed successfully (1874 jobs). |
| `lake env lean RangeSetBlaze/AlgoC.lean` | 0 | 3.08 s | Warm direct compilation; no output. |
| `lake env lean /tmp/range-set-blaze-phase1-axioms.lean` | 0 | ~2 s | Axiom result recorded below. |
| `python3 scripts/phase0_metrics.py -o metrics/phase1-pairwise-append-left-v2.json` | 0 | 0.5 s | Corrected-v2 artifact written. |

The aggregate build emitted only this pre-existing warning:

```text
warning: RangeSetBlaze/AlgoB.lean:465:8: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
```

It also emitted the five expected `Main.lean` informational values:

```text
info: Main.lean:52:0: [0, 1, 2, 5, 6, 7]
info: Main.lean:53:0: [0, 1, 2, 3, 4, 5, 6, 7]
info: Main.lean:54:0: [0, 1, 2, 3, 4, 5, 6, 7]
info: Main.lean:55:0: [-5, -4, -3, 0, 1, 2, 5, 6, 7]
info: Main.lean:56:0: [0, 1, 2, 5, 6, 7]
```

The comment-aware integrity scan reported:

```text
active sorry: False
active admit: False
active axiom declarations: []
active unsafe: False
```

The raw search had only the three known inactive matches in the opening block
comment of `AlgoC.lean` (two `unsafe`, one `sorry`).

The elaborated axiom query returned exactly:

```text
'RangeSetBlaze.internalAddC_toSet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` dependency is present, and the axiom set is unchanged from the
preceding v2 state.

## Corrected-v2 metric comparison

Comparison is against the immediately preceding corrected-v2 artifact,
`metrics/phase1-mknr-cleanup-v2.json`, not the original Phase 0 baseline.

| Metric | preceding v2 | this v2 | delta |
|---|---:|---:|---:|
| Algo C physical LOC | 3317 | 3303 | -14 |
| Algo C nonblank LOC | 3056 | 3043 | -13 |
| Algo C blank LOC | 261 | 260 | -1 |
| Algo C comment-only LOC | 1075 | 1074 | -1 |
| Algo C active-code LOC | 1981 | 1969 | -12 |
| Algo C definitions | 10 | 10 | 0 |
| Algo C lemma/theorem declarations | 36 | 35 | -1 |
| Algo C private lemma/theorem declarations | 30 | 29 | -1 |
| Repository physical LOC | 4788 | 4774 | -14 |
| Repository nonblank LOC | 4400 | 4387 | -13 |
| Repository blank LOC | 388 | 387 | -1 |
| Repository comment-only LOC | 1150 | 1149 | -1 |
| Repository active-code LOC | 3250 | 3238 | -12 |
| Repository definitions | 52 | 52 | 0 |
| Repository lemma/theorem declarations | 71 | 70 | -1 |
| Repository private lemma/theorem declarations | 34 | 33 | -1 |
| `simp` tokens | 289 | 288 | -1 |
| `cases` tokens | 84 | 83 | -1 |

All other corrected-v2 lexical token totals are unchanged (`simpa`, `rw`,
`have`, `linarith`, `omega`, `grind`, and `by_cases`).

The measured deltas exactly match the prediction: the deleted helper occupies
19 physical lines, while its five call-site lines remain one-for-one, giving
physical `-14`; its removed blank/comment-only lines give `-1` each, and its
remaining active proof lines give active-code `-12`. The helper body contained
one `simp` and one `cases`; the five direct projections add no counted tactic
tokens. No delta differs from prediction.

## Protected algorithm footprint

The diff changes only one private proof helper and proof terms at five call
sites. The executable bodies of `deleteExtraNRs_loop`, `deleteExtraNRs`,
`internalAdd2NRs`, `internalAddC_extendPrev_safe`, and `internalAddC` retain
their production branch/merge structure. In particular, empty input handling,
the `lo ≤ start` split, predecessor gap/coverage/touching branches, the
`next.lo ≤ current.hi + 1` merge condition, preserved lower endpoint, `max`
upper endpoint, and the exact `internalAddC_toSet` theorem statement are
unchanged. `pairwise_append_cross`, the local `pairwise_append`, theorem
statements, and executable definitions outside the requested proof terms were
not altered.

## Git status

At evidence collection:

```text
 M RangeSetBlaze/AlgoC.lean
?? metrics/phase1-pairwise-append-left-v2.json
?? metrics/phase1-pairwise-append-left-v2.md
```

No commit, tag, or push was created.
