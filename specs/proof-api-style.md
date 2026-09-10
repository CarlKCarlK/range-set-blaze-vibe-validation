# Proof API style

Future fresh-chat refactoring sessions begin with `AGENTS.md`, which routes readers here and to `specs/lean-proof-refactoring.md`.

## Naming

1. Follow normal Lean conventions and make proposition direction clear.
2. Name the mathematical or domain concept, not the proof mechanism.
3. As a tie-breaker, prefer names that also feel natural to a Rust or C# programmer: readable, explicit, stable, and neither needlessly abbreviated nor tied to incidental implementation details.
4. Avoid abbreviations and field-name soup when a clearer semantic name exists.
5. Do not encode operations such as `getLast?`, `dropWhile`, decomposition mechanics, or tactic structure unless that operation is genuinely part of the concept.
6. Prefer names that read naturally at call sites.
7. While the API is young, rename mediocre names instead of preserving them solely to avoid churn.
8. Choose vocabulary that can remain meaningful in proofs about cursor-based `BTreeMap` insertion, `RangeMapBlaze`, and other sorted-disjoint-range implementations.

Do not trade away idiomatic Lean merely to resemble another language, and do not rename a clear name merely because it is long.

## Documentation

Add doc comments for non-obvious invariants, abstraction boundaries, and reusable proof concepts. Explain mathematical meaning, intent, and why a fact matters to the range-set proof—not tactic history, editing history, or merely the Lean type.

Good comments have **no golf penalty**. Do not reduce physical LOC by deleting useful explanation. Measure active proof/code LOC separately from comment-only LOC. A small active LOC increase is acceptable when an abstraction materially improves clarity, reuse, or the proof vocabulary.

## Review questions

For every new or renamed API concept, ask:

- What mathematical fact does the name communicate?
- Does the call site read naturally?
- Does the name express the invariant we care about or a representation mechanism?
- Is there an equally clear, more idiomatic Lean name?
- Would the name still fit a cursor-based or `RangeMapBlaze` proof?
- When the type does not make its purpose obvious, does its doc comment explain why it exists?
