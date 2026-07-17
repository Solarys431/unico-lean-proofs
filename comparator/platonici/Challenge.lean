/-
Copyright (c) 2026 Daniele Cappello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Cappello
-/
import Mathlib

/-!
# The Platonic solids classification (Wiedijk #50) — the challenge statement

A 3-dimensional convex polytope whose facets are regular p-gons (regularity
defined BY ORBIT of an affine isometry: no angle or length is postulated) and
whose vertices are all q-cyclic satisfies `q * (p - 2) < 2 * p`, hence (p, q)
is one of the five Platonic pairs. Plus non-vacuity: such a polytope exists
for (3, 3).

Unlike our Feuerbach challenge, the definitions here are NOT mathlib's (mathlib
has no polytope theory): they are stated below in full, and they are the whole
contract. Audit them before judging: the angular inequality appears in no
definition, facet regularity postulates only the existence of a generating
isometry orbit, and the vertex fan is pure incidence structure. The proofs are
deliberately `sorry`; run Comparator to check `Solution.lean` proves these
exact statements from the standard axioms only.
-/


/-!
CAMPAGNA #50 — MODULO DEFINIZIONI (disegno del gate cieco, 17 lug 2026).

Le nozioni su cui vive il teorema `cyclicallyRegular_schlafli`:

* `FiniteConvexPolytope A` — hull convesso di un insieme finito i cui vertici
  dichiarati sono ESATTAMENTE i punti estremi (lo stesso patto del benchmark
  lean-eval, ma su spazio astratto A: si vincola l'oggetto, non l'ambiente).
* `IsFace` / `IsFacet` — facce esposte non vuote; faccette = facce di span 2D.
* `IsRegularFacet` — poligono regolare PER ORBITA di una rotazione: niente
  liste di angoli postulategli dentro (la riparazione anti-trappola del gate).
  La congruenza dei lati consecutivi è GRATIS dall'isometria.
* `CyclicVertexData` / `IsCyclicVertex` — il fan di q faccette attorno a un
  vertice, permutato ciclicamente da un'isometria che fissa il vertice e
  preserva il politopo.
* `IsCyclicallyRegularOfType` — il predicato del teorema di classificazione.

La disuguaglianza angolare NON compare in alcuna definizione: è il TEOREMA
(kill-gate `spike_somma_sotto_due_pi`, già kernel-certificato al giorno zero).
-/

open Set Metric
open scoped RealInnerProductSpace

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- Un politopo convesso su uno spazio con prodotto interno reale: hull convesso
di un insieme finito non vuoto di punti, i cui vertici dichiarati sono
esattamente i punti estremi dell'hull. -/
structure FiniteConvexPolytope (A : Type*) [NormedAddCommGroup A]
    [InnerProductSpace ℝ A] where
  vertices : Finset A
  nonempty : vertices.Nonempty
  vertices_eq_extremePoints :
    (vertices : Set A) = (convexHull ℝ (vertices : Set A)).extremePoints ℝ

namespace FiniteConvexPolytope

variable (P : FiniteConvexPolytope A)

/-- Il corpo convesso del politopo. -/
def toSet : Set A := convexHull ℝ (P.vertices : Set A)

/-- Una faccia: sottoinsieme esposto e non vuoto del corpo. -/
def IsFace (F : Set A) : Prop :=
  IsExposed ℝ P.toSet F ∧ F.Nonempty

/-- Una faccetta: faccia il cui span direzionale è un piano. -/
def IsFacet (F : Set A) : Prop :=
  P.IsFace F ∧ Module.finrank ℝ (vectorSpan ℝ F) = 2

/-- Faccetta p-gonale REGOLARE, definita per orbita: esiste un'isometria affine
ρ che manda la faccetta in sé, il cui ciclo su un vertice di partenza ha
esattamente p punti distinti, chiude dopo p passi, genera la faccetta come hull
convesso, e ha passo di lunghezza ℓ. La congruenza di TUTTI i lati consecutivi
segue gratis dall'isometria; nessun angolo è postulato. -/
def IsRegularFacet (F : Set A) (p : ℕ) (ℓ : ℝ) : Prop :=
  P.IsFacet F ∧ 0 < ℓ ∧ 3 ≤ p ∧
  ∃ (ρ : A ≃ᵃⁱ[ℝ] A) (x₀ : A),
    x₀ ∈ F ∧
    (⇑ρ) '' F = F ∧
    Function.Injective (fun i : Fin p => (⇑ρ)^[(i : ℕ)] x₀) ∧
    (⇑ρ)^[p] x₀ = x₀ ∧
    F = convexHull ℝ (Set.range fun i : Fin p => (⇑ρ)^[(i : ℕ)] x₀) ∧
    dist x₀ (ρ x₀) = ℓ

/-- I dati di un vertice q-ciclico: le faccette incidenti a v enumerate da
`Fin q`, un'isometria σ che fissa v, preserva il politopo e ruota il fan di un
passo, e la completezza locale del fan (faccette consecutive condividono uno
spigolo per v: il loro incontro contiene v e un punto ulteriore). -/
structure CyclicVertexData (v : A) (q : ℕ) where
  /-- l'enumerazione ciclica delle faccette incidenti a v -/
  faccetta : Fin q → Set A
  isFacet : ∀ i, P.IsFacet (faccetta i)
  mem_v : ∀ i, v ∈ faccetta i
  distinte : Function.Injective faccetta
  complete : ∀ F : Set A, P.IsFacet F → v ∈ F → ∃ i, F = faccetta i
  /-- la simmetria ciclica locale -/
  σ : A ≃ᵃⁱ[ℝ] A
  fissa_v : σ v = v
  preserva : (⇑σ) '' P.toSet = P.toSet
  ruota : ∀ i : Fin q, (⇑σ) '' faccetta i = faccetta (finRotate q i)
  /-- faccette consecutive si toccano in uno spigolo per v, non solo in v -/
  spigolo : ∀ i : Fin q,
    ∃ x, x ≠ v ∧ x ∈ faccetta i ∩ faccetta (finRotate q i)
  /-- struttura di fan (pseudovarietà): un punto di spigolo diverso da v
  appartiene SOLO alle due faccette che quello spigolo condividono. Nessun
  angolo, nessun conteggio: è la proprietà «ogni spigolo ha due facce». -/
  spigolo_due : ∀ i j : Fin q, ∀ x,
    x ∈ faccetta i ∩ faccetta (finRotate q i) → x ≠ v →
    x ∈ faccetta j → j = i ∨ j = finRotate q i

/-- Vertice q-ciclico (forma proposizionale). -/
def IsCyclicVertex (v : A) (q : ℕ) : Prop :=
  Nonempty (P.CyclicVertexData v q)

/-- Il predicato del teorema di classificazione: politopo 3-dimensionale con
faccette p-gonali regolari di lato comune ℓ e ogni vertice q-ciclico. -/
def IsCyclicallyRegularOfType (p q : ℕ) : Prop :=
  Module.finrank ℝ (vectorSpan ℝ (P.vertices : Set A)) = 3 ∧
  3 ≤ p ∧ 3 ≤ q ∧
  ∃ ℓ > 0,
    (∀ F, P.IsFacet F → P.IsRegularFacet F p ℓ) ∧
    (∀ v ∈ P.vertices, P.IsCyclicVertex v q)

end FiniteConvexPolytope

open FiniteConvexPolytope

/-- The local Schläfli classification: five Platonic pairs. -/
theorem cyclicallyRegular_schlafli
    {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    (P : FiniteConvexPolytope A) {p q : ℕ}
    (h : P.IsCyclicallyRegularOfType p q) :
    q * (p - 2) < 2 * p ∧
    ((p = 3 ∧ q = 3) ∨ (p = 4 ∧ q = 3) ∨ (p = 3 ∧ q = 4) ∨
     (p = 5 ∧ q = 3) ∨ (p = 3 ∧ q = 5)) := by
  sorry

/-- Non-vacuity: a (3,3) polytope exists (the regular tetrahedron). -/
theorem exists_cyclicallyRegular :
    ∃ P : FiniteConvexPolytope (EuclideanSpace ℝ (Fin 3)),
      P.IsCyclicallyRegularOfType 3 3 := by
  sorry
