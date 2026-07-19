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

**How the pipeline works** — architecture, the *taste canon* (a second judge
ruling on mathematical quality, not just truth), adversarial gates, and how to
verify our claims without trusting our build: see **[PIPELINE.md](PIPELINE.md)**.

<a href="PIPELINE.md">
<picture>
  <source media="(prefers-color-scheme: dark)" srcset="assets/pipeline-schema-dark.svg">
  <img alt="The UNICO/NOUS two-judge pipeline — click for the full architecture" src="assets/pipeline-schema-light.svg" width="100%">
</picture>
</a>

---

## The exact count in dimension three

The benchmark's own counting function is now settled for d = 3:

```lean
theorem platonicCount_three : platonicCount 3 = 5
```

([`TeoremaPlatonici.lean`](UnicoProofs/Platonici/TeoremaPlatonici.lean),
depends on `propext`, `Classical.choice`, `Quot.sound` only.)

The lower bound was already available from the five explicit witnesses. The
upper bound needed rigidity: two regular 3-polytopes of the same cyclic type
are similar
([`Chiusura2.lean`](UnicoProofs/Platonici/Chiusura2.lean)). The proof works
through canonical invariants only, and uses neither Cauchy's rigidity theorem
nor a global identification of facets:

1. the scaling factor comes from the diameters of exposed edges, so it does
   not depend on the orbit generator of a facet
   ([`Fattore.lean`](UnicoProofs/Platonici/Fattore.lean));
2. two vertex fans with equal Gram matrices are related by an affine isometry
   ([`Registro.lean`](UnicoProofs/Platonici/Registro.lean)); the argument
   transports linear relations directly, so it tolerates redundant families;
3. positive homotheties leave unit rays unchanged and isometries act on them
   through their linear part alone
   ([`RaggiTrasporto.lean`](UnicoProofs/Platonici/RaggiTrasporto.lean));
4. fan alignment propagates from one vertex to its neighbours
   ([`Orientazione.lean`](UnicoProofs/Platonici/Orientazione.lean)) and then,
   along the vertex graph, to the whole polytope
   ([`InduzioneFinale.lean`](UnicoProofs/Platonici/InduzioneFinale.lean));
5. equal vertex sets give equal convex hulls
   ([`CorpiUguali.lean`](UnicoProofs/Platonici/CorpiUguali.lean)).

Dimensions 2, 4 and d >= 5 are still open in this repository.

## The plane: infinitely many

```lean
theorem platonicCount_two : platonicCount 2 = ⊤
```

([`TeoremaDim2.lean`](UnicoProofs/Platonici/TeoremaDim2.lean), same three
axioms.)

This is the easiest of the four conjuncts: no upper bound is needed, since
`⊤` only asks for infinitely many classes. The regular `n`-gon is built from
the `n`-th roots of unity
([`PoligonoRegolare.lean`](UnicoProofs/Platonici/PoligonoRegolare.lean)) and
shown regular through the dihedral action on its flags: rotations move the
vertex, the reflection swaps the two incident edges
([`PoligonoDiedrale.lean`](UnicoProofs/Platonici/PoligonoDiedrale.lean)).
Since similar polytopes have the same number of vertices, polygons with
different side counts fall in different classes.

## Where this stands against the benchmark

The lean-eval statement is a conjunction of four claims:

```lean
platonicCount 2 = ⊤ ∧ platonicCount 3 = 5 ∧
platonicCount 4 = 6 ∧ ∀ d, 5 ≤ d → platonicCount d = 3
```

Two of them are proved here (d = 2 and d = 3). The other two are open in
this repository: dimension 4 needs six classes, among them the 24-cell,
the 120-cell and the 600-cell; dimensions d >= 5 need an upper bound, that
is a classification argument, not just the three witnesses.

## Highlight — The Platonic Solids Classification (Wiedijk #50)

*The theorem that closes Euclid's Elements (XIII.18 and scholium), proved
July 17, 2026 by the UNICO / NOUS autonomous certification pipeline.*

> A three-dimensional convex polytope whose facets are regular p-gons and
> whose vertices are all q-cyclic satisfies q(p−2) < 2p; hence (p, q) is one
> of the five Platonic types: (3,3), (4,3), (3,4), (5,3), (3,5).

```lean
theorem cyclicallyRegular_schlafli (P : FiniteConvexPolytope A) {p q : ℕ}
    (h : P.IsCyclicallyRegularOfType p q) :
    q * (p - 2) < 2 * p ∧
    ((p = 3 ∧ q = 3) ∨ (p = 4 ∧ q = 3) ∨ (p = 3 ∧ q = 4) ∨
     (p = 5 ∧ q = 3) ∨ (p = 3 ∧ q = 5))

theorem tetraedro_cyclicallyRegular :
    tetraedro.IsCyclicallyRegularOfType 3 3
```

The statement lives on an **abstract real inner-product space**: facet
regularity is defined *by orbit* (an affine isometry generates the p vertices
cyclically), with no angle or length ever postulated; the vertex fan is pure
incidence structure. The angular inequality is the **theorem**, never an
assumption. The witness (`tetraedro_cyclicallyRegular`) shows the predicate
is not vacuous. Scope, stated precisely: this is the *local Schläfli-type
classification* (necessity of the five pairs, plus one existence witness) —
not the enumeration of all five solids, which is the declared next phase.

The proof builds a small convex-polytope theory that mathlib currently lacks
(exposed-face restriction, argmax faces of finite hulls, translated orbits,
the planar rotation/reflection dichotomy, a cosine-argmax lemma handling
star-polygon orbits via modular inverses) — 25 modules, 158 kernel-pure
theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only.

Prior art, checked the same day: the geometric theorem exists in **HOL Light**
(Harrison); in Lean we found only numerological versions (Schläfli pairs as
bare naturals with the inequality postulated). A related but **stronger**
problem, the dimension-by-dimension `platonicCount` (`p_3 = 5`, `p_4 = 6`,
`p_d = 3` for `d ≥ 5`, with flag transitivity and similarity), is posed on the
[lean-eval leaderboard](https://leanprover.github.io/lean-eval-leaderboard/);
our result does **not** claim it (that is our declared later phase), and the
leaderboard is submission-based, so its status reflects submitted solutions,
not an evaluation of every model. If you know of earlier geometric work on
this theorem in Lean, please open an issue and we will cite it prominently.

**Update (July 18, 2026) — all five witnesses and the full characterization.**
The classification bounds the possible types; the converse direction is now
certified as well: kernel-pure witnesses for all five Platonic types — the
tetrahedron (3,3), the cube (4,3), the octahedron (3,4), the dodecahedron (5,3)
with its golden-ratio pentagon rotation, and the icosahedron (3,5) — and the
characterization theorem:

```lean
theorem realizzabile_iff (p q : ℕ) :
    (∃ P : FiniteConvexPolytope E3, P.IsCyclicallyRegularOfType p q)
    ↔ ((p = 3 ∧ q = 3) ∨ (p = 4 ∧ q = 3) ∨ (p = 3 ∧ q = 4)
        ∨ (p = 5 ∧ q = 3) ∨ (p = 3 ∧ q = 5))
```

A type is realizable **iff** it is one of the five Platonic pairs: neither
direction is vacuous. The engine behind the five witnesses is a reusable
transfer module ([`Trasferimento.lean`](UnicoProofs/Platonici/Trasferimento.lean)):
regular facets and cyclic vertex fans transport along polytope-preserving
isometries, so each solid needs one facet and one vertex fan built by hand —
symmetry does the rest.

**Update (July 18, 2026, third release): the bridge from flag-transitivity
to the five Schläfli pairs.** On the benchmark's own contract we certify:

```lean
theorem regolare_schlafli (P : ConvexPolytope 3) (hreg : P.IsRegular) :
    ∃ p q : ℕ, P.asFinite.IsCyclicallyRegularOfType p q ∧
      ((p = 3 ∧ q = 3) ∨ (p = 4 ∧ q = 3) ∨ (p = 3 ∧ q = 4) ∨
       (p = 5 ∧ q = 3) ∨ (p = 3 ∧ q = 5))
```

Every regular 3-polytope (flag-transitive in the benchmark's sense) carries
the structure our classification engine consumes: every facet is a regular
p-gon traced by an isometry orbit, every vertex figure is a q-cyclic fan,
and (p, q) is one of the five Platonic pairs
([`Ponte.lean`](UnicoProofs/Platonici/Ponte.lean)). The 31 new modules build
the full ladder from the contract's definitions: existence of flags through
any vertex or facet, uniqueness of the flag transporter (a symmetry fixing a
flag fixes four affinely independent barycenters, hence is the identity),
the diamond property in both directions (every edge lies in exactly two
facets, every polygon vertex lies in exactly two edges), fan connectivity
via a simplex walk, the deterministic fan cycle with simultaneous return of
facet and edge, and transport lemmas that make p, q and the edge length
uniform across the polytope. This closes the bridge phase. What remains for
the benchmark's 3D equality is rigidity: two regular polytopes of the same
type are similar. The first tool of that phase is included
([`SimilarEquiv.lean`](UnicoProofs/Platonici/SimilarEquiv.lean): similarity
is an equivalence). As always, if you know prior art we should cite, please
open an issue.

**Update (July 18, 2026, second release) — the 3D lower bound on the lean-eval
benchmark's own definitions.** The [lean-eval benchmark](https://github.com/leanprover/lean-eval)
states the Platonic classification problem on its own clean definitions
(`ConvexPolytope`, flags, `IsRegular` as flag-transitivity, `platonicCount` as
similarity classes). We reproduce those definitions verbatim
([`Benchmark.lean`](UnicoProofs/Platonici/Benchmark.lean)) and certify, on that
exact contract:

```lean
theorem cinque_le_platonicCount3 : 5 ≤ platonicCount 3
```

via flag-transitivity of all five solids, a similarity invariant (vertex
cardinality, since similarities biject extreme points), and an `encard` class
count. This is the **lower bound only**: it does not solve the benchmark
problem, which asks for equality and for the counts in every dimension. The
upper bound (every regular 3-polytope is similar to one of the five) is the
next phase of this project.

Modules: [`UnicoProofs/Platonici/`](UnicoProofs/Platonici/) — apex theorems in
[`Classificazione.lean`](UnicoProofs/Platonici/Classificazione.lean),
[`Realizzabilita.lean`](UnicoProofs/Platonici/Realizzabilita.lean),
[`RegolariBenchmark.lean`](UnicoProofs/Platonici/RegolariBenchmark.lean), and the
five witness modules (`TetraedroStadio2`, `CuboTestimone`, `OttaedroTestimone`,
`DodecaedroTestimone`, `IcosaedroTestimone`).

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

| File | Statement | Trust | Verify | Proof author |
|------|-----------|:-----:|:------:|--------------|
| [`Platonici/`](UnicoProofs/Platonici/) | **The Platonic solids classification** (Wiedijk #50, local Schläfli types) — 3D convex polytope with orbit-regular p-gonal facets and q-cyclic vertices ⟹ q(p−2) < 2p and (p,q) is one of the five Platonic pairs (`cyclicallyRegular_schlafli`); certified witnesses for **all five solids**, the characterization `realizzabile_iff`, and the lean-eval-contract lower bound `cinque_le_platonicCount3 : 5 ≤ platonicCount 3` (flag-transitivity of all five, similarity invariant, class count); the bridge `regolare_schlafli` (every flag-transitive 3-polytope is cyclically regular of one of the five types); 68 modules | ✅ pure kernel | [comparator](comparator/platonici/) | UNICO / NOUS (Claude, Anthropic) |
| [`SylvesterGallai.lean`](UnicoProofs/SylvesterGallai.lean) | **The Sylvester–Gallai theorem** — a finite non-collinear point set always admits a line through exactly two of its points; Kelly's proof made purely vectorial, no dimension hypothesis (see prior-art note: Sylvester–Chvátal exists in Lean 4, the classical Euclidean statement did not) | ✅ pure kernel | [comparator](comparator/sylvester_gallai/) | UNICO / NOUS (Claude, Anthropic) |
| [`Feuerbach/`](UnicoProofs/Feuerbach/) | **Feuerbach's theorem** (Wiedijk #29) — nine-point circle internally tangent to the incircle (`feuerbach_insphere`) and externally tangent to the three excircles (`feuerbach_exsphere`); independent proof, 11 modules | ✅ pure kernel | [comparator](comparator/feuerbach/) | UNICO / NOUS (Claude, Anthropic) |
| [`Morley.lean`](UnicoProofs/Morley.lean) | **Morley's trisector theorem** (Wiedijk #84) — geometric statement, with `∃!` and non-degeneracy companions; independent formalization (see prior-art note: solved earlier on the [lean-eval benchmark](https://leanprover.github.io/lean-eval-leaderboard/problems/morley_theorem)) | ✅ pure kernel | [comparator](lean-eval/morley_theorem/) | UNICO / NOUS (Claude, Anthropic) |
| [`Erdos1064K2.lean`](UnicoProofs/Erdos1064K2.lean) | **Erdős Problem 1064, variant k2** — infinitely many `n` with `φ(n) < φ(n − φ(n))` (Grytczuk–Luca–Wójtowicz 2001; independent equivalent proof in [lean-genius](https://github.com/rjwalters/lean-genius), July 8, 2026 — see prior-art note in file) | ✅ pure kernel | — | Aristotle (Harmonic AI) |
| [`Erdos1148Counterexample.lean`](UnicoProofs/Erdos1148Counterexample.lean) | **Erdős Problem 1148** — `6563` is not representable as `x² + y² − z²` with `max(x², y², z²) ≤ 6563` (largest such integer known) | ⚙️ compiler | — | UNICO / NOUS (Claude, Anthropic) |

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

## Independent verification with Comparator

Building the whole project trusts our `lake` setup. For a stronger, environment-independent
check, three theorems ship a self-contained [Comparator](https://github.com/leanprover/comparator)
workspace ([`comparator/`](comparator/)): you read a short `Challenge.lean` to see *what* is
claimed, then one command confirms the proof establishes *exactly* that statement, uses only the
standard axioms, and is accepted by the Lean kernel — without reading the full proof.

```bash
cd comparator/sylvester_gallai   # or feuerbach
lake exe cache get
lake env comparator config.json  # prints: Your solution is okay!
```

All three (`sylvester_gallai`, `feuerbach`, `morley_theorem`) pass. Both geometry workspaces were
verified with the real `landrun` Landlock sandbox on Linux (kernel 7.0, Landlock ABI 8), not only
the built-in kernel check — the same guarantee a reviewer gets on their own machine.

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
