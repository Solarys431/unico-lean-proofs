# Sylvester–Gallai — Comparator workspace

A self-contained [Comparator](https://github.com/leanprover/comparator) workspace for the
Sylvester–Gallai theorem. It lets you trust the result in two independent steps, without
reading the full proof or trusting our build environment:

1. **Read [`Challenge.lean`](Challenge.lean) and [`ChallengeDeps.lean`](ChallengeDeps.lean).**
   Between them they state the theorem and the two definitions it rests on — `lineThrough`
   (the affine line through two points) and `IsOrdinaryLine` (a line meeting the set in
   exactly two points). That is all you need to read to know *what* is claimed. The proof in
   `Challenge.lean` is deliberately `sorry`.

2. **Run Comparator.** It mechanically checks that `SylvesterGallai.sylvester_gallai` in
   [`Solution.lean`](Solution.lean) proves the *exact* statement of `Challenge.lean`, over the
   *exact* definitions of `ChallengeDeps.lean`, using only the three standard axioms, and is
   accepted by the Lean kernel. `Solution.lean` imports `ChallengeDeps` — it does not redefine
   `lineThrough` or `IsOrdinaryLine`, so it cannot quietly weaken them.

```bash
lake exe cache get
lake env comparator config.json
```

On success Comparator prints `Your solution is okay!`, guaranteeing that the theorem:

1. proves the same statement declared in `Challenge.lean`;
2. uses only `propext`, `Quot.sound`, `Classical.choice`;
3. is accepted by the Lean kernel.

Comparator needs [`landrun`](https://github.com/Zouuup/landrun) (a Linux Landlock sandbox) and
[`lean4export`](https://github.com/leanprover/lean4export) on `PATH`, both matching the pinned
toolchain (`v4.32.0-rc1`). See the comparator README for the exact `systemd-run` invocation.

> Verified locally with `comparator v4.32.0-rc1`: **`Your solution is okay!`**
> (On macOS the local check used a no-sandbox shim in place of `landrun`, since Landlock is
> Linux-only; the kernel comparison itself is unaffected. On Linux, run the real `landrun` for
> the full sandboxed guarantee.)

The standalone theorem, with the surrounding development, is in
[`../../UnicoProofs/SylvesterGallai.lean`](../../UnicoProofs/SylvesterGallai.lean).
