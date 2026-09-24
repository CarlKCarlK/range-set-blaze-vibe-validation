# RangeSetBlaze Vibe Validation

![A robot inspects a tree hung with numbered balls](docs/banner.png)

This repository contains the Lean proofs and supporting experiments for the Medium article, **"Nine Rules for Vibe Validation of Vibe-Coded Algorithms: Using AI-Written Lean to Validate AI-Written Rust."**

For now, see [Carl Kadie's Medium profile](https://medium.com/@carlmkadie) for the article.

- Earlier proof project: [range-set-blaze-lean](https://github.com/CarlKCarlK/range-set-blaze-lean)
- Earlier article: [Vibe Validation with Lean, ChatGPT-5, Claude 4.5 (Part 1)](https://medium.com/@carlmkadie/vibe-validation-with-lean-chatgpt-5-claude-4-5-part-1-c57b430b3d7a)
- Rust project being validated: [range-set-blaze](https://github.com/CarlKCarlK/range-set-blaze)

The project explores **vibe validation**: using AI to model production algorithms in Lean, write machine-checked proofs of their high-level correctness, and then review and test the connection between the Lean models and the Rust implementations.

## What is validated

The repository includes proofs and supporting tests for several RangeSetBlaze and RangeMapBlaze operations, including:

- production and cursor-based range-set insertion;
- production and cursor-based range-map insertion;
- cached-length updates for the insertion algorithms;
- uniqueness of canonical range-set and range-map representations; and
- baseline and cursor-based `range_or_gap_at` operations; and
- insertion in the older Python predecessor, PySnpTools `IntRangeSet._internal_add` (`RangeSetBlaze/PyIntRangeSet.lean`), whose merge loop is proved identical to the production RangeSetBlaze scan, together with a refinement proof over Python's actual two fields, the sorted `_start_items` list and the `_start_to_length` dictionary, including their synchronization invariants (`RangeSetBlaze/PyIntRangeSetState.lean`).

The project also includes a small formalization of the subset of `BTreeMap` semantics used by these algorithms. Rust comparison tests check that a simple sorted-`Vec` implementation and the real `BTreeMap` implementation have the same observable behavior for that interface.

## Scope

These proofs validate **high-level algorithms**, not every detail of the compiled Rust implementations. The Rust algorithms are modeled in Lean in a form that preserves the decisions and state transitions relevant to correctness while abstracting away implementation details such as tree navigation.

The AI writes the proofs; Lean checks them. Separately, tests and review check that the Rust implementations faithfully correspond to the proved algorithms.

## Relationship to the earlier project

This repository is a new proof project based on the earlier `range-set-blaze-lean` work. The earlier repository remains unchanged as the reproducible artifact associated with its own article.

This project extends that work to additional algorithms and properties while also refactoring the Lean proof library to make it smaller, cleaner, and more reusable.

## Validation

Run the normal production build and the compile-time regression checks with:

```text
lake build
lake test
```

`lake test` builds `RangeSetBlaze/Regression.lean`, whose examples use `native_decide` to check concrete scenarios across the algorithms.

The Python differential cases in `RangeSetBlaze/PyIntRangeSetCases.lean` are generated from the real PySnpTools implementation by `scripts/generate_py_intrangeset_cases.py`; they record both `_start_items` and `_start_to_length` after every call. `python3 scripts/mutate_py_intrangeset_state.py` runs mutation testing of the two-field model against its proofs and those cases.

The proof project is intended to build without `sorry` placeholders or new axioms introduced to bypass the proofs.

## License

The project is dual-licensed under the Apache License, Version 2.0 and the MIT License. You may use this code under the terms of either license. See `LICENSE-APACHE` and `LICENSE-MIT` for details.
