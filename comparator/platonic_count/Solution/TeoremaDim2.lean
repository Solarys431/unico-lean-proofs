import Mathlib
import Challenge
import Solution.Dim2Scheletro
import Solution.PoligonoRegolare
import Solution.PoligonoDiedrale

/-!
# NEL PIANO I POLITOPI REGOLARI SONO INFINITI

    platonicCount 2 = ⊤

il primo congiunto dell'enunciato del benchmark. A differenza della
dimensione 3 non serve un maggiorante: basta una famiglia infinita di
classi distinte, e il numero di vertici le separa.

La famiglia è `n ↦ poligono (n+3)`: poligoni regolari con 3, 4, 5, …
vertici, ciascuno regolare per `poligono_isRegular` e con cardinalità
`n+3` per `poligono_card`.
-/

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- La famiglia dei poligoni regolari, indicizzata da `ℕ` a partire dal
triangolo. -/
def famigliaPoligoni (n : ℕ) : regularPolytopes 2 :=
  ⟨poligono (n + 3), poligono_isRegular (n + 3) (by omega)⟩

@[simp] theorem famigliaPoligoni_card (n : ℕ) :
    (famigliaPoligoni n : ConvexPolytope 2).vertices.card = n + 3 :=
  poligono_card (n + 3) (by omega)

/-- **NEL PIANO I POLITOPI REGOLARI SONO INFINITI.** -/
theorem platonicCount_two : platonicCount 2 = ⊤ := by
  refine platonicCount_eq_top 2 famigliaPoligoni ?_
  intro m n hmn
  have h : m + 3 = n + 3 := by
    simpa [famigliaPoligoni_card] using hmn
  omega

end LeanEval.Geometry.PlatonicClassification
