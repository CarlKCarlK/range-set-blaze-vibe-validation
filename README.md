# RangeSetBlaze Vibe Validation

> **Status: OK for now.** This repo is a working experiment, not a polished
> or reviewed artifact. Expect rough edges; treat conclusions here as
> provisional until the proof is cleaned up and cross-checked.

This repository accompanies a forthcoming Medium article by [Carl
Kadie](https://medium.com/@carlmkadie), tentatively titled "Nine Rules for
Vibe Validation of Vibe-Coded Algorithms: Using AI-Written Lean to Validate
AI-Written Rust."

It is a new proof experiment based on the earlier `range-set-blaze-lean` and
`range-set-blaze-lean2` work. Those repositories remain unchanged as the
reproducible artifacts associated with their own articles.

This project validates production RangeSetBlaze insertion algorithms,
including new cursor-based algorithms, in Lean. Its goals are to keep the
proofs small, readable, and reusable by both people and AI as the set of
validated algorithms grows.

## Validation

Run the normal production build and the compile-time regression checks with:

```text
lake build
lake test
```

`lake test` builds `RangeSetBlaze/Regression.lean`, whose examples use
`native_decide` to check concrete insertion scenarios across the algorithms.

## License

The project is dual-licensed under the Apache License, Version 2.0 and the
MIT License. You may use this code under the terms of either license. See
`LICENSE-APACHE` and `LICENSE-MIT` for details.
