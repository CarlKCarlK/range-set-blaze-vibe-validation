# Proof-complexity metrics

## Purpose

This repository treats proof metrics as a dashboard of independent signals,
not as a weighted score. No composite complexity score may be introduced
without explicit user approval. A lower count is not automatically better:
the dashboard supports review; it does not replace it.

Lean proofs do not have one faithful equivalent of McCabe cyclomatic
complexity. Tactic scripts construct terms through elaborator state, branches
may be explicit syntax or hidden inside terms and automation, and the same
mathematical argument can be expressed in several styles. We therefore count
reproducible lexical indicators and call the relevant category **proof
branching**, not cyclomatic complexity.

## Permanent dashboard

### Headline metrics

- **Size:** physical, nonblank, comment-only, and active-code LOC. Active LOC
  asks how much active source must be maintained. Physical and comment-only
  LOC keep deletion of historical comments distinguishable from proof
  compression. Useful comments carry no penalty.
- **Proof branching:** exact active-code tokens `cases`, `by_cases`, and
  `induction`. These ask how many explicit eliminations, decisions, and
  induction sites are visible. They do not count resulting alternatives,
  branches hidden in term-level `match`, or branching performed by automation.
- **Proof plumbing:** exact active-code tokens `have`, `show`, `suffices`, and
  `rw`. These ask how much intermediate-fact, goal-shaping, and manual rewrite
  plumbing is explicit. Such structure is often explanatory; fewer is not an
  unconditional goal.

### Supporting metrics

- **Automation:** `simp`, `simpa`, `omega`, `linarith`, and `grind`, reported
  separately. `simp only` counts as `simp`; `simpa` does not also count as
  `simp`. One call says nothing about proof-search cost or transparency.
- **Representation detail:** `takeWhile`, `dropWhile`, `getLast?`, `dropLast`,
  `pairwise_append`, the `Sublist` type token, and qualified `List.span` uses.
  These were selected because they expose recurring list/split machinery in
  Algo C. They are not a general-purpose list-complexity measure. Qualified
  names such as `List.Pairwise.sublist` do not accidentally count `Sublist`;
  exact token matching still counts `List.pairwise_append` as an occurrence of
  `pairwise_append`.
- **Declaration/API shape:** definitions, abbreviations, lemmas, theorems, and
  private/public lemma-theorem declarations. Public here means syntactically
  non-`private`, not a curated supported API. Same-line attributes such as
  `@[simp]` are recognized. Adding a reusable lemma may raise these counts
  while materially improving the proof.

The default review should show both `RangeSetBlaze/AlgoC.lean` and repository
totals. Repository totals guard against making Algo C appear smaller merely by
moving one-use reasoning elsewhere.

## Collection and compatibility

Run the collector from the repository root:

```text
python3 scripts/phase0_metrics.py
python3 scripts/phase0_metrics.py --git-ref REF
```

Collector/schema v3 extends the corrected-v2 collector. The existing per-file
LOC/declaration fields, `tokens`, `totals`, and `token_totals` retain their v2
semantics for historical consumers. New dashboard counts live under
`files[].dashboard` and `dashboard_totals`; they mask nested comments, line
comments, strings, and plausible character literals, preserve primed Lean
identifiers, and count exact tokens. Historical dashboard values must be
reconstructed by running the same v3 collector against an exact Git ref.

This remains documented lexical analysis, not a Lean parser. Counts can
include syntax in executable definitions as well as proofs, do not assign
tokens to individual declarations, and cannot reliably distinguish every
term/tactic role. Compare only results produced by the same dashboard schema
and collector behavior, and retain the source identity and byte manifest.

## Experimental, deferred, and rejected candidates

The candidate groups have these final dispositions:

| Candidate | Disposition |
|---|---|
| A. Proof/code size | **Headline** |
| B. `cases`, `by_cases`, `induction` | **Headline** |
| B. proof-body `match` branches | **Experimental/deferred** |
| C. `have`, `show`, `suffices`, `rw` | **Headline** |
| D. selected automation tactics | **Supporting** |
| E. selected Algo C list machinery | **Supporting** |
| E. generic decomposition-pattern mining | **Rejected** |
| F. declaration/API shape | **Supporting** |
| F. one-use private helpers | **Experimental/deferred** |
| G. dependency/proof architecture | **Experimental/deferred** |
| H. goal counts and proof nesting | **Experimental/deferred** |
| H. compile/elaboration timing as routine metrics | **Rejected** |

- **Experimental/deferred:** term-level `match` branches inside proofs. A
  reliable count requires parsed declaration boundaries and proof/body role;
  a global `match` token count would mix protected executable control flow
  with proof structure.
- **Experimental/deferred:** helper dependencies, dependency depth, fan-in,
  fan-out, and helpers used by `internalAddC_toSet`. These could be valuable if
  obtained from stable Lean/compiler information. A text-derived call graph
  would be fragile around namespaces, notation, local bindings, and generated
  terms.
- **Experimental/deferred:** one-use private helpers. This has the same
  call-graph problem and is not worth brittle static analysis.
- **Experimental/deferred:** generated subgoal count and maximum simultaneous
  goals. They would require stable instrumentation of elaboration/tactic state
  and a defined aggregation policy.
- **Experimental/deferred:** maximum proof nesting. Syntax-tree nesting may be
  useful after a parser-based collector exists, but indentation or delimiter
  heuristics are too style-sensitive.
- **Rejected as a routine dashboard metric:** elaboration time per declaration
  and total direct compile time. They may be captured for controlled
  experiments with toolchain, cache state, machine load, and repeated samples,
  but are too noisy for ordinary structural comparisons.
- **Rejected:** generic prefix/suffix decomposition-pattern counts. There is no
  small stable lexical signature, so the result would be subjective or
  brittle.
- **Rejected:** indiscriminate counts of all list operations or all tactics.
  They dilute the Algo C representation question and invite token gaming.

## Required qualitative review

Every comparison must still ask:

- Does the proof read more like the mathematics?
- Did complexity merely move to another module or into opaque automation?
- Is the proof API clearer and more reusable?
- Would the abstraction help future cursor-based or `RangeMapBlaze` proofs?
- Did added declarations capture reusable concepts, or only add scaffolding?

Do not claim improvement merely because totals fell. Do not penalize useful
comments, reward opaque automation, or reward deletion of reusable API that
causes reasoning to be duplicated elsewhere.
