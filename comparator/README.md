# Comparator workspaces

[Comparator](https://github.com/leanprover/comparator) is the Lean community's standard way to
verify a formalization without reading the whole proof or trusting the author's build
environment. You read a short `Challenge.lean` to see *what* is claimed, then run one command to
mechanically confirm that the proof establishes *exactly* that statement, using only the standard
axioms, accepted by the Lean kernel.

Each directory here is a self-contained workspace pinned to `leanprover/lean4:v4.32.0-rc1`.

| Theorem | Statement rests on | Comparator |
|---|---|---|
| [`sylvester_gallai/`](sylvester_gallai/) | two project definitions (`lineThrough`, `IsOrdinaryLine`), stated in `ChallengeDeps.lean` | ✅ `Your solution is okay!` |
| [`feuerbach/`](feuerbach/) | mathlib API only (`insphere`, `exsphere`, `ninePointCircle`, `IsIntTangent`/`IsExtTangent`) | ✅ `Your solution is okay!` |

Both were verified locally with `comparator v4.32.0-rc1`. Morley has its own comparator
workspace under [`../lean-eval/morley_theorem/`](../lean-eval/morley_theorem/) (accepted by the
official lean-eval comparator).

To run one:

```bash
cd sylvester_gallai   # or feuerbach
lake exe cache get
lake env comparator config.json
```

Comparator requires [`landrun`](https://github.com/Zouuup/landrun) and
[`lean4export`](https://github.com/leanprover/lean4export) on `PATH` at the pinned toolchain.
`landrun` is a Linux Landlock sandbox; on non-Linux hosts the kernel comparison still runs, but
the sandboxed build guarantee needs Linux.
