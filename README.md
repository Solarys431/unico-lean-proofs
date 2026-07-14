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

## Highlight — The Sylvester–Gallai Theorem

*Proved July 14, 2026 by the UNICO / NOUS autonomous certification pipeline —
in a ninety-minute evening session.*

> A finite set of points in the plane, not all on one line, always admits an
> *ordinary line*: a line passing through exactly two of the points.
> — conjectured by J. J. Sylvester (1893), proved by T. Gallai (1944)

```lean
theorem sylvester_gallai (S : Set P) (hfin : S.Finite) (hncol : ¬ Collinear ℝ S) :
    ∃ a ∈ S, ∃ b ∈ S, IsOrdinaryLine S a b
```

The statement holds in any real inner-product space with its affine torsor, with
**no dimension hypothesis**. The proof is Kelly's (1948), made purely vectorial:
no areas, no angles, no similar triangles — only the inner product. The strict
inequality driving the minimal-distance argument is the one-line computation
`⟪A, w⟫ = ‖A‖² > 0` (the minimizing point is not the foot of the perpendicular),
and the pigeonhole step is isolated as a lemma about three distinct **real**
numbers — exactly where the proof must use the order of ℝ, since the theorem is
**false over ℂ** (the Hesse configuration). A satisfiability witness (a concrete
non-collinear triangle) accompanies the development, so the theorem is not
vacuously true.

**Prior art & novelty.** At publication time the theorem is not in mathlib, and
chapter 11 of the [Formal Book project](https://github.com/mo271/FormalBook)
("Lines in the plane") is an open TODO. A Lean 3 development exists
([Happyves/Master_Thesis](https://github.com/Happyves/Master_Thesis), containing
a `sorry`). In Lean 4, [Yaël Dillies' misc-yd](https://github.com/YaelDillies/misc-yd)
proves the **Sylvester–Chvátal theorem** (Chen's 2006 generalization to finite
metric spaces, with betweenness lines); its Euclidean corollary — the classical
statement proved here — is sketched there in a commented-out block containing a
`sorry`. To our knowledge the classical Euclidean statement had not previously
been formalized in Lean 4; we make no priority claim beyond the commit date.

**Trust: pure kernel** — 0 `sorry`, 0 custom axioms; all declarations in
[`UnicoProofs/SylvesterGallai.lean`](UnicoProofs/SylvesterGallai.lean) depend on
`[propext, Classical.choice, Quot.sound]` only. Verify with `lake build`.

---

## Highlight — Feuerbach's Theorem (Wiedijk #29)

*The classical statement, in full, proved July 13, 2026 by the UNICO / NOUS
autonomous certification pipeline — in a single evening session.*

> In any triangle, the nine-point circle is internally tangent to the incircle
> and externally tangent to each of the three excircles. — K. W. Feuerbach, 1822

```lean
theorem feuerbach_insphere (t : Triangle ℝ P) :
    t.insphere.IsIntTangent t.ninePointCircle

theorem feuerbach_exsphere (t : Triangle ℝ P) (i : Fin 3) :
    (t.exsphere {i}).IsExtTangent t.ninePointCircle
```

Both statements hold for **every** triangle in a two-dimensional real inner
product torsor, with **no side conditions** — existence of the in/excenters and
positivity of the radii are derived internally from mathlib. Tangency is
mathlib's own `Sphere.IsIntTangent` / `Sphere.IsExtTangent` (which, per
mathlib's explicit convention, count coincident circles as internally tangent —
relevant only for the equilateral triangle, where the two circles coincide).

**Prior art & novelty.** Feuerbach's theorem is #29 on
[Freek Wiedijk's list](https://www.cs.ru.nl/~freek/100/). It had been
formalized in **HOL Light** (John Harrison, Gröbner-basis approach), **Rocq**
(the CertiGeo team, reflexive external certificates) and **Isabelle/HOL**
(Lawrence C. Paulson, May 2026 — an AI-assisted translation of the HOL Light
proof). The proof here is independent of all three: it normalizes the in/excircle to the unit circle,
where the touchpoints `t₁ t₂ t₃` parametrize everything; the nine-point
center acquires the closed form `e₂²/P` with `P = (t₁+t₂)(t₁+t₃)(t₂+t₃)`;
and the branch (internal vs. external tangency) is pinned by a **barycentric
sign certificate**: with `W` the real model parameter and `λᵢ` the barycentric
weights of the center,

```
W · λ₀λ₁λ₂ · ‖t₀−t₁‖²‖t₀−t₂‖²‖t₁−t₂‖² = −1     and     W · (‖t₀+t₁+t₂‖² − 1) = 1
```

— two rational identities certified by `linear_combination` with
sympy-generated cofactors. mathlib's `excenterWeights` signs (all positive for
the incenter, exactly one negative for an excenter) then decide the branch:
`W ≤ −1` gives internal, `W > 1/8` external. No arcs, no case analysis on
angles.

**Trust: pure kernel** — 0 `sorry`, 0 custom axioms across all 11 modules
([`UnicoProofs/Feuerbach/`](UnicoProofs/Feuerbach/)); the two theorems depend
on `[propext, Classical.choice, Quot.sound]` only. Verify with `lake build`.

**Status:** standalone Lean formalization; an upstream contribution to mathlib
is under consideration.

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
| [`SylvesterGallai.lean`](UnicoProofs/SylvesterGallai.lean) | **The Sylvester–Gallai theorem** — a finite non-collinear point set always admits a line through exactly two of its points; Kelly's proof made purely vectorial, no dimension hypothesis (see prior-art note: Sylvester–Chvátal exists in Lean 4, the classical Euclidean statement did not) | ✅ pure kernel | Claude (Anthropic) |
| [`Feuerbach/`](UnicoProofs/Feuerbach/) | **Feuerbach's theorem** (Wiedijk #29) — nine-point circle internally tangent to the incircle (`feuerbach_insphere`) and externally tangent to the three excircles (`feuerbach_exsphere`); independent proof, 11 modules | ✅ pure kernel | Claude (Anthropic) |
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
