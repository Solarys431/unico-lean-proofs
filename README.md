# unico-lean-proofs

> **Highlight (July 12, 2026).** [`UnicoProofs/Morley.lean`](UnicoProofs/Morley.lean):
> **Morley's trisector theorem (Wiedijk #84) — to our knowledge the first geometric
> formalization in Lean.** Trisectors are rays in the complex plane, the Morley points
> are intersection-membership hypotheses, and the conclusion is about distances between
> actual points — together with an existence/uniqueness companion (the intersections
> are nonempty and unique) and a non-degeneracy companion (the three points are
> pairwise distinct). Morley #84 is listed among the 16 theorems of Freek Wiedijk's
> list [not yet formalized in Lean](https://leanprover-community.github.io/100-missing.html)
> (checked 2026-07-12). Pure kernel: 0 `sorry`, 0 custom axioms, no `native_decide`.


Machine-verified Lean 4 proofs produced by the **UNICO / NOUS** project — an
autonomous discovery-and-certification pipeline (statement selection → numeric
falsification → multi-engine proof search → local kernel verification) run by
Solarys431.

Every file in this repository compiles with Lean 4 and contains no `sorry`.
Trust level is stated per file: **pure kernel** (no axioms beyond mathlib) vs
**compiler** (`native_decide`, which additionally trusts `Lean.ofReduceBool`
and the compiler). We label each proof honestly rather than blur the distinction.

## Proofs

| File | Statement | Trust | Author of proof |
|------|-----------|-------|-----------------|
| [`UnicoProofs/Morley.lean`](UnicoProofs/Morley.lean) | **Morley's trisector theorem (Wiedijk #84)** — in any non-degenerate triangle in ℂ, the three intersection points of adjacent angle trisectors form an equilateral triangle. Geometric statement (rays + intersections + distances), with `∃!` existence/uniqueness and pairwise-distinctness companions. First geometric formalization in Lean to our knowledge (previously: HOL Light, Isabelle, Rocq, Mizar; partial trigonometric identities in [lean-genius](https://github.com/rjwalters/lean-genius)) | ✅ pure kernel | Claude (Anthropic) — see disclosure in file |
| [`UnicoProofs/Erdos1064K2.lean`](UnicoProofs/Erdos1064K2.lean) | **Erdős Problem 1064, variant k2** — there are infinitely many `n` with `φ(n) < φ(n − φ(n))` (solved informally by Grytczuk–Luca–Wójtowicz, 2001; no `formal_proof` recorded in [formal-conjectures](https://github.com/google-deepmind/formal-conjectures); an equivalent independent proof appeared in [rjwalters/lean-genius](https://github.com/rjwalters/lean-genius) on July 8, 2026 — see the prior-art note in the file) | ✅ pure kernel | Aristotle (Harmonic AI) — see disclosure in file |
| [`UnicoProofs/Erdos1148Counterexample.lean`](UnicoProofs/Erdos1148Counterexample.lean) | **Erdős Problem 1148, the counterexample `6563`** — `6563` is not representable as `x² + y² − z²` with `max(x², y², z²) ≤ 6563` (the largest such integer known) | ⚙️ compiler (`native_decide`, depends on `Lean.ofReduceBool`) | Claude (Anthropic) — see disclosure in file |

## How to verify

```bash
# requires elan (https://leanprover-community.github.io/get_started.html)
lake exe cache get   # downloads precompiled mathlib
lake build           # kernel-checks every proof — should end with no errors
```

Toolchain: `leanprover/lean4:v4.32.0-rc1` · mathlib `v4.32.0-rc1`.
CI runs the same build on every push.

## AI disclosure

Proofs in this repository are produced with AI assistance (Aristotle by
Harmonic, Codex by OpenAI, Claude by Anthropic) and are labeled
**LLM-generated**, with per-file provenance notes. The Lean kernel is the
sole arbiter of correctness: nothing is published here unless it compiles.

## License

Apache 2.0 — see [LICENSE](LICENSE).
