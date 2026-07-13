# lean-eval submissions

Self-contained comparator workspaces for the [leanprover/lean-eval](https://github.com/leanprover/lean-eval)
benchmark. Each directory is a full workspace (`lakefile.toml` + `Submission.lean`
+ `Submission/`): the benchmark CI only reads `Submission.lean` and `Submission/**`.

| Problem | Result | Notes |
|---------|--------|-------|
| [`morley_theorem`](morley_theorem/) | verified locally by the official comparator (pinned toolchain v4.32.0-rc1): *"Your solution is okay!"* | Independent proof via our oriented-ray complex-plane development + an unoriented→oriented bridge (barycentric coordinates recover the orientation sign from the convex-hull hypothesis). Pure kernel: no `sorry`, no extra axioms. See [`UnicoProofs/Morley.lean`](../UnicoProofs/Morley.lean) for the standalone theorem with `∃!` and non-degeneracy companions. |
