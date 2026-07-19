import Mathlib
import Challenge
import Solution.InvarianteSimilarita

/-!
CAMPAGNA #50, DIMENSIONE 2 — LO SCHELETRO DEL CONTEGGIO (19 lug 2026).

`platonicCount 2 = ⊤`: nel piano i politopi regolari sono infiniti (un
poligono regolare per ogni numero di lati). A differenza della dimensione
3, qui NON serve un maggiorante: basta esibire una famiglia infinita di
classi distinte.

Il discriminante è già certificato: `vertices_card_of_similar` dice che
due politopi simili hanno lo stesso numero di vertici, dunque poligoni
con un numero diverso di lati stanno in classi diverse. Qui lo scheletro
che, data una famiglia di poligoni regolari con cardinalità crescente,
conclude `⊤`.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- La classe di similarità di un politopo regolare (dimensione
arbitraria). -/
def classeSim (d : ℕ) (P : regularPolytopes d) : Set (regularPolytopes d) :=
  {Q | regularSimilar d P Q}

theorem classeSim_mem_quoziente (d : ℕ) (P : regularPolytopes d) :
    classeSim d P ∈ {S : Set (regularPolytopes d) |
      ∃ P', S = {Q : regularPolytopes d | regularSimilar d P' Q}} :=
  ⟨P, rfl⟩

/-- Politopi regolari con un numero diverso di vertici stanno in classi
distinte. -/
theorem classeSim_ne_of_card_ne {d : ℕ} {P Q : regularPolytopes d}
    (h : (P : ConvexPolytope d).vertices.card ≠
      (Q : ConvexPolytope d).vertices.card) :
    classeSim d P ≠ classeSim d Q := by
  intro hcon
  apply h
  have hQ : Q ∈ classeSim d Q := similar_refl (Q : ConvexPolytope d)
  rw [← hcon] at hQ
  exact (vertices_card_of_similar hQ).symm

/-- **IL CONTEGGIO INFINITO**: una famiglia di politopi regolari con
cardinalità dei vertici iniettiva dà infinite classi, dunque
`platonicCount d = ⊤`. -/
theorem platonicCount_eq_top (d : ℕ) (F : ℕ → regularPolytopes d)
    (hcard : Function.Injective
      (fun n => (F n : ConvexPolytope d).vertices.card)) :
    platonicCount d = ⊤ := by
  classical
  have hinj : Function.Injective (fun n => classeSim d (F n)) := by
    intro m n hmn
    by_contra hne
    exact classeSim_ne_of_card_ne (fun hc => hne (hcard hc)) hmn
  have hsub : Set.range (fun n => classeSim d (F n)) ⊆
      {S : Set (regularPolytopes d) |
        ∃ P', S = {Q : regularPolytopes d | regularSimilar d P' Q}} := by
    rintro S ⟨n, rfl⟩
    exact classeSim_mem_quoziente d (F n)
  have hinf : (Set.range (fun n => classeSim d (F n))).Infinite :=
    Set.infinite_range_of_injective hinj
  have hinf' : {S : Set (regularPolytopes d) |
      ∃ P', S = {Q : regularPolytopes d | regularSimilar d P' Q}}.Infinite :=
    hinf.mono hsub
  show Set.encard _ = ⊤
  exact hinf'.encard_eq

end LeanEval.Geometry.PlatonicClassification
