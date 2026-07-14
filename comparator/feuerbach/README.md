# Feuerbach's theorem (Wiedijk #29) — Comparator workspace

A self-contained [Comparator](https://github.com/leanprover/comparator) workspace for the
classical form of Feuerbach's theorem. Trust the result in two independent steps:

1. **Read [`Challenge.lean`](Challenge.lean).** It states the two theorems and nothing else.
   Every symbol is mathlib's own — `Triangle`, `insphere`, `exsphere`, `ninePointCircle`,
   `Sphere.IsIntTangent`, `Sphere.IsExtTangent` — so there are **no project-specific
   definitions to audit**: reading these few lines tells you exactly *what* is claimed. The
   proofs are deliberately `sorry`.

2. **Run Comparator.** It mechanically checks that `FeuerbachMain.feuerbach_insphere` and
   `FeuerbachMain.feuerbach_exsphere` in [`Solution.lean`](Solution.lean) (the full proof, in
   11 modules under [`Solution/`](Solution/)) prove the *exact* statements of `Challenge.lean`,
   using only the three standard axioms, and are accepted by the Lean kernel.

```bash
lake exe cache get
lake env comparator config.json
```

On success Comparator prints `Your solution is okay!`, guaranteeing that both theorems:

1. prove the same statements declared in `Challenge.lean`;
2. use only `propext`, `Quot.sound`, `Classical.choice`;
3. are accepted by the Lean kernel.

Comparator needs [`landrun`](https://github.com/Zouuup/landrun) (a Linux Landlock sandbox) and
[`lean4export`](https://github.com/leanprover/lean4export) on `PATH`, both matching the pinned
toolchain (`v4.32.0-rc1`). See the comparator README for the exact `systemd-run` invocation.

> Verified locally with `comparator v4.32.0-rc1`: **`Your solution is okay!`**
> (On macOS the local check used a no-sandbox shim in place of `landrun`, since Landlock is
> Linux-only; the kernel comparison itself is unaffected. On Linux, run the real `landrun` for
> the full sandboxed guarantee.)

The standalone development is in
[`../../UnicoProofs/Feuerbach/`](../../UnicoProofs/Feuerbach/).
