# RangeSetBlaze Lean proof-refactoring Phase 0 baseline

Collected 2026-09-08 in /home/carlk/programs/range-set-blaze-lean2. No Lean source files were modified.

## Identity

- Commit: 5bcfce5517024171625cc781636f1c67a7eab470
- Commit metadata: Tue Sep 8 21:25:42 2026 -0700, Carl Kadie, "Add refactoring specification for RangeSetBlaze Lean proof"
- Pre-artifact branch/status: main...origin/main [ahead 2]; porcelain status, diff stat, and diff check were empty.
- Lean: Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
- Lake: Lake version 5.0.0-src+819816b (Lean version 4.33.1)
- lean-toolchain: leanprover/lean4:v4.33.1
- Mathlib manifest revision: 0df444a360eaa60ab8c11dca51a86af692955474; lakefile requirement v4.33.1
- Platform: Linux carlk23 6.6.114.1-microsoft-standard-WSL2 #1 SMP PREEMPT_DYNAMIC Mon Dec 1 20:46:23 UTC 2025 x86_64 x86_64
- Recommended future tag (not created): proof-refactor-baseline-20260908

Source SHA-256 values:

    4e766b25b35dff762fa09d72589df1608d2cdb1d9c4c8d522642a3116cff451a  RangeSetBlaze/Basic.lean
    eca4bd0af6753501a5368d6be0efb258c56414ad9445ffba9d1d5d8b640353b4  RangeSetBlaze/AlgoB.lean
    fddc240563abc63b5571b513cf504d96b5d1233e8ebda8cd69b3fcd69aefc743  RangeSetBlaze/AlgoC.lean
    b01f5194dbe377411330a7df27ebb9c98e724c93cd639d9e6b2d820b344bd42e  RangeSetBlaze.lean
    d5cd1418fa342d7eaabae9f236b1e197d51ce28cb851b616e004f576fe22f8ec  Main.lean

## Verification

| Command | Exit | Elapsed | Result |
|---|---:|---:|---|
| lake build | 0 | 5.33 s | Build completed successfully (1874 jobs). |
| lake env lean RangeSetBlaze/AlgoC.lean | 0 | 13.39 s | Successful; no warnings or informational output. |

Aggregate build output, verbatim:

    ⚠ [940/1271] Replayed RangeSetBlaze.AlgoB
    warning: RangeSetBlaze/AlgoB.lean:465:8: try 'simp' instead of 'simpa'

    Note: This linter can be disabled with set_option linter.unnecessarySimpa false
    ℹ [943/1271] Replayed Main
    info: Main.lean:52:0: [0, 1, 2, 5, 6, 7]
    info: Main.lean:53:0: [0, 1, 2, 3, 4, 5, 6, 7]
    info: Main.lean:54:0: [0, 1, 2, 3, 4, 5, 6, 7]
    info: Main.lean:55:0: [-5, -4, -3, 0, 1, 2, 5, 6, 7]
    info: Main.lean:56:0: [0, 1, 2, 5, 6, 7]
    Build completed successfully (1874 jobs).

The AlgoB line 465 linter warning is classified pre-existing because no source was changed. The five Main lines are expected informational output. No unexplained warnings occurred. The direct compilation log was empty apart from elapsed-time output.

## Proof integrity

A simple comment-aware scanner removed nested block comments and line comments, then matched whole tokens over repository-owned Lean files, excluding .lake, generated, and vendor paths:

    active sorry: none
    active admit: none
    active source axiom declarations: none
    active unsafe: none

Raw comment matches are excluded; the stale Algo C opening session text contains the word sorry.

The temporary-file axiom query returned exactly:

    'RangeSetBlaze.internalAddC_toSet' depends on axioms: [propext, Classical.choice, Quot.sound]

No sorryAx dependency was present.

## Metrics

Definitions: physical LOC is source lines; total LOC is nonblank (physical minus blank); blank is whitespace-only; comment-only is a nonblank line erased by comment removal; active code is remaining nonblank lines. Declaration counts are simple active-source, line-oriented counts, including private declarations. Token counts are whole tokens after comment removal; simp only counts as simp and simpa is separate. Parser-based proof-body metrics are deferred.

| File | Physical | Total | Blank | Comment-only | Active | def/abbrev | lemma/theorem | private lemma/theorem |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| RangeSetBlaze/Basic.lean | 477 | 420 | 57 | 13 | 407 | 14 | 22 | 3 |
| RangeSetBlaze/AlgoB.lean | 890 | 838 | 52 | 18 | 820 | 16 | 13 | 1 |
| RangeSetBlaze/AlgoC.lean | 3,320 | 3,059 | 261 | 866 | 2,193 | 11 | 36 | 30 |
| RangeSetBlaze.lean | 7 | 6 | 1 | 2 | 4 | 0 | 0 | 0 |
| Main.lean | 95 | 78 | 17 | 2 | 76 | 11 | 0 | 0 |
| requested-file total | 4,789 | 4,401 | 388 | 901 | 3,500 | 52 | 71 | 34 |

All repository-owned Lean files, including tracked auxiliary RangeSetBlazeLean2.lean and RangeSetBlazeLean2/Basic.lean, total 4,791 physical, 4,403 nonblank, 388 blank, 901 comment-only, 3,502 active; 53 def/abbrev, 71 lemma/theorem, and 34 private lemma/theorem.

| File | simp | simpa | rw | have | linarith | omega | grind | by_cases | cases |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| RangeSetBlaze/Basic.lean | 23 | 25 | 1 | 41 | 3 | 0 | 0 | 5 | 5 |
| RangeSetBlaze/AlgoB.lean | 62 | 37 | 1 | 173 | 6 | 0 | 0 | 2 | 23 |
| RangeSetBlaze/AlgoC.lean | 216 | 18 | 191 | 503 | 3 | 15 | 0 | 20 | 61 |
| RangeSetBlaze.lean | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Main.lean | 2 | 5 | 0 | 9 | 0 | 0 | 0 | 0 | 0 |
| requested-file total | 303 | 85 | 193 | 726 | 12 | 15 | 0 | 27 | 89 |

Disabled historical Algo C proof blocks: lines 2433–2505, 2512–3021, and 3154–3315, totaling 745 physical lines, reported separately from active proof size. The opening session log at lines 10–57 is not included.

## Algorithm footprint

Reviewed in AlgoC.lean: deleteExtraNRs_loop lines 70–83, deleteExtraNRs lines 164–178, internalAdd2NRs lines 180–187, internalAddC_extendPrev_safe, and internalAddC. The specification footprint is unchanged: empty input returns the original set; the split uses lo <= start; absent/gap/covered/touching predecessor branches remain distinct; the scan merges while next.lo <= current.hi + 1, preserves the current lower endpoint, and uses max for the upper endpoint; representation ordering and the exact internalAddC_toSet set theorem remain present. Phase 0 made no executable changes.

## Audit supplement

The frozen collector is scripts/phase0_metrics.py. Reproduce the machine-readable artifact with:

    python3 scripts/phase0_metrics.py > specs/lean-proof-refactoring-baseline.json

Its documented method handles -- comments through newline, nested /- ... -/ comments with a depth counter, strings and character literals with escapes, and preserves newlines during comment removal. Python splitlines() means a final unterminated line counts as one physical line. Declarations are line-start optional-private followed by def/abbrev or lemma/theorem. Tactic counts use whole-token boundaries [A-Za-z0-9_?]; simp only counts as simp and simpa is separate. This is a small lexical fallback, not a parser.

Raw integrity-search command:

    rg -n --glob '*.lean' --glob '!*.lake/**' --glob '!**/generated/**' --glob '!**/vendor/**' '\\b(sorry|unsafe)\\b' . || true

Raw output:

    ./RangeSetBlaze/AlgoC.lean:14:STATUS: Migrating away from unsafe constructors. Core invariant proofs COMPLETE!
    ./RangeSetBlaze/AlgoC.lean:40:  - some prev with gap: prev.val.hi + 1 < start (gap provided directly) ✅ WIRED (with sorry)
    ./RangeSetBlaze/AlgoC.lean:54:Current unsafe constructors (to eventually remove):

Classification: one sorry (line 40) and two unsafe matches (lines 14 and 54); all are inactive in the opening block comment.

Temporary axiom file contents, exactly:

    import RangeSetBlaze.AlgoC
    #print axioms RangeSetBlaze.internalAddC_toSet

Exact command:

    lake env lean /tmp/range-set-blaze-phase0-axioms.lean

Result:

    'RangeSetBlaze.internalAddC_toSet' depends on axioms: [propext, Classical.choice, Quot.sound]

Qualitative Phase 0 rubric (0 clear, 1 minor friction, 2 repeated friction, 3 major obstacle):

| Dimension | Score | Evidence |
|---|---:|---|
| Discoverability | 2 | Main theorem is findable, but list-set folds and ordering vocabulary are split across Basic, Algo B, and Algo C. |
| Interface complexity | 3 | Algo C helpers expose endpoint equalities, dependent lets, and proof witnesses; callers reconstruct substantial evidence. |
| Duplication | 3 | Three list-set folds, duplicate constructor vocabulary, overlapping loop/splice specifications, and repeated split/predecessor derivations exist. |
| High-level proof readability | 2 | Production branches are visible, but generic list plumbing and repeated invariant reconstruction interrupt the narrative. |

The retained timings are warm/cached: lake build was a warm replay and direct compilation used a warm import cache. No timing rerun was made.

## Post-artifact status

Only this Markdown file was added; no Lean file, tag, commit, or remote state was changed.

    ## main...origin/main [ahead 2]
    ?? scripts/phase0_metrics.py
    ?? specs/lean-proof-refactoring-baseline.json
    ?? specs/lean-proof-refactoring-baseline.md
