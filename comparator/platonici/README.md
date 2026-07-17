# The Platonic solids classification (Wiedijk #50) — Comparator workspace

A self-contained [Comparator](https://github.com/leanprover/comparator) workspace
for the geometric classification of the Platonic solids (local Schläfli types).
Trust the result in two independent steps:

1. **Read [`Challenge.lean`](Challenge.lean).** Unlike our Feuerbach challenge,
   the definitions here are NOT mathlib's (mathlib has no polytope theory): the
   file states them in full, and they are the whole contract. What to audit:
   the angular inequality `q(p-2) < 2p` appears in **no definition**; facet
   regularity postulates only an isometry orbit (no angles, no lengths);
   the vertex fan is pure incidence structure. The two theorems
   (`cyclicallyRegular_schlafli`, `exists_cyclicallyRegular`) are deliberately
   `sorry`.

2. **Run Comparator.** It mechanically checks that `Solution.lean` (25 modules
   under `Solution/`, importing the Challenge's definitions) proves those exact
   statements using only `propext`, `Classical.choice`, `Quot.sound`.

```bash
comparator config.json
```
