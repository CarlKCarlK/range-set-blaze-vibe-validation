# RangeSetBlaze Vibe Validation

> **Status: OK for now.** This repo is a working experiment, not a polished
> or reviewed artifact. Expect rough edges; treat conclusions here as
> provisional until the proof is cleaned up and cross-checked.

This repository is a new proof experiment based on the earlier
`range-set-blaze-lean` work. The original repository remains unchanged as the
reproducible artifact associated with the 2025 article.

This project will validate the same production RangeSetBlaze insertion
algorithm. Its goals are to reduce the size of the proof and make the proof
more readable and reusable by both people and AI.

## Validation

Run the normal production build and the compile-time regression checks with:

```text
lake build
lake test
```

`lake test` builds `RangeSetBlaze/Regression.lean`, whose examples use
`native_decide` to check concrete insertion scenarios across the algorithms.
