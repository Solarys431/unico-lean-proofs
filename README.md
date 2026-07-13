<div align="right">🌐 <b>English</b> · <a href="README.it.md">Italiano</a></div>

# unico-lean-proofs

[![Verify proofs](https://github.com/Solarys431/unico-lean-proofs/actions/workflows/build.yml/badge.svg)](https://github.com/Solarys431/unico-lean-proofs/actions/workflows/build.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.32.0--rc1-blue)](https://leanprover.github.io/)
[![mathlib](https://img.shields.io/badge/mathlib-pinned-blue)](https://github.com/leanprover-community/mathlib4)
[![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-green)](LICENSE)

**Machine-verified Lean 4 proofs from the UNICO / NOUS autonomous
certification pipeline** — statement selection → numeric falsification →
multi-engine proof search → local kernel certification → public CI
re-verification. Run by [Solarys431](https://github.com/Solarys431).

Every file compiles with Lean 4 and contains no `sorry`. The trust level is
stated per file — **pure kernel** (nothing beyond the mathlib axioms) versus
**compiler** (`native_decide`, which additionally trusts `Lean.ofReduceBool`
and the Lean compiler) — because honesty about the trusted base matters more
than a longer list of green check marks.

---

## Highlight — Morley's Trisector Theorem (Wiedijk #84)

*An independent geometric formalization in Lean (July 12, 2026) — see the prior-art note below.*

> In any non-degenerate triangle, the three intersection points of adjacent
> angle trisectors form an equilateral triangle. — F. Morley, 1899

```lean
theorem morley_classico (A B C P₁ P₂ P₃ : ℂ)
    (hnc : ¬ Collinear ℝ ({A, B, C} : Set ℂ))
    (h₁ : P₁ ∈ trisettore A B C ∩ trisettore B A C)
    (h₂ : P₂ ∈ trisettore B C A ∩ trisettore C B A)
    (h₃ : P₃ ∈ trisettore C A B ∩ trisettore A C B) :
    dist P₁ P₂ = dist P₂ P₃ ∧ dist P₂ P₃ = dist P₃ P₁
```

The statement is genuinely geometric — in the style of Harrison's HOL Light
`MORLEY`: `trisettore` (*trisector*) is a ray in the complex plane, the Morley
points enter as membership hypotheses in the ray intersections, and the
conclusion is about distances between actual points. Two companions close the
classical loopholes: [`morley_esistenza_classico`](UnicoProofs/Morley.lean)
(each pair of adjacent trisectors meets in **exactly one** point, `∃!`) and
[`morley_non_degenere_classico`](UnicoProofs/Morley.lean) (the three points are
**pairwise distinct** — a genuine triangle, never a collapsed one).

**Prior-art note (July 13, 2026).** Morley's theorem is #84 on
[Freek Wiedijk's list](https://www.cs.ru.nl/~freek/100/) and was listed among
the [16 theorems not yet formalized in Lean](https://leanprover-community.github.io/100-missing.html)
at publication time — but within an hour of the announcement, Jeremy Chen on
the Lean Zulip kindly pointed out the [lean-eval benchmark](https://leanprover.github.io/lean-eval-leaderboard/problems/morley_theorem),
whose geometric `morley_theorem` had already been solved by several AI systems
between June 10 and July 11, 2026. **So this is not the first geometric
formalization of Morley's theorem in Lean**, and we are glad to correct the
record. It remains an independent formalization with a different statement
(oriented rays via `arg`/3 in ℂ) and with `∃!`/non-degeneracy companions the
benchmark statement does not ask for. Other systems: HOL Light (Harrison),
Isabelle (Puyobro), Rocq (Guilhot), Mizar (Coghetto); partial trigonometric
identities in [lean-genius](https://github.com/rjwalters/lean-genius).

**Trust: pure kernel** — 0 `sorry`, 0 custom axioms, no compiler-trusted
evaluation. Tagged [`morley-2026-07-12`](https://github.com/Solarys431/unico-lean-proofs/releases/tag/morley-2026-07-12).

---

## All proofs

| File | Statement | Trust | Proof author |
|------|-----------|:-----:|--------------|
| [`Morley.lean`](UnicoProofs/Morley.lean) | **Morley's trisector theorem** (Wiedijk #84) — geometric statement, with `∃!` and non-degeneracy companions; independent formalization (see prior-art note: solved earlier on the [lean-eval benchmark](https://leanprover.github.io/lean-eval-leaderboard/problems/morley_theorem)) | ✅ pure kernel | Claude (Anthropic) |
| [`Erdos1064K2.lean`](UnicoProofs/Erdos1064K2.lean) | **Erdős Problem 1064, variant k2** — infinitely many `n` with `φ(n) < φ(n − φ(n))` (Grytczuk–Luca–Wójtowicz 2001; independent equivalent proof in [lean-genius](https://github.com/rjwalters/lean-genius), July 8, 2026 — see prior-art note in file) | ✅ pure kernel | Aristotle (Harmonic AI) |
| [`Erdos1148Counterexample.lean`](UnicoProofs/Erdos1148Counterexample.lean) | **Erdős Problem 1148** — `6563` is not representable as `x² + y² − z²` with `max(x², y², z²) ≤ 6563` (largest such integer known) | ⚙️ compiler | Claude (Anthropic) |

Each file carries its own provenance and prior-art notes in the header.

## Verifying the proofs yourself

```bash
# requires elan: https://leanprover-community.github.io/get_started.html
git clone https://github.com/Solarys431/unico-lean-proofs
cd unico-lean-proofs
lake exe cache get   # download precompiled mathlib
lake build           # kernel-checks every proof — ends with no errors
```

Toolchain: `leanprover/lean4:v4.32.0-rc1` · mathlib pinned by
[`lake-manifest.json`](lake-manifest.json). The
[CI workflow](.github/workflows/build.yml) runs this exact build on every push
— the badge above is the public, independent verification.

## Methodology

UNICO / NOUS is an autonomous mathematical discovery-and-certification
pipeline. Candidate statements are selected, numerically falsified where
possible, then attacked by multiple engines (Claude, Codex, Aristotle) with
exact symbolic computation (sympy) supplying certified cofactors for
`linear_combination`-style proofs. Nothing reaches this repository unless the
local Lean kernel certifies it — and CI re-certifies it in public.

## AI disclosure

All proofs are **LLM-generated** (Aristotle by Harmonic, Codex by OpenAI,
Claude by Anthropic), with per-file provenance notes, under human direction.
The Lean kernel is the sole arbiter of correctness: nothing is published here
unless it compiles.

## Citing

See [`CITATION.cff`](CITATION.cff), or cite the repository directly with the
relevant tag (e.g. `morley-2026-07-12`).

## License

[Apache 2.0](LICENSE).
