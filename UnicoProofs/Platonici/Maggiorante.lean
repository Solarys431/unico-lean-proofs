import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.InvarianteSimilarita
import UnicoProofs.Platonici.IstanzeBenchmark
import UnicoProofs.Platonici.SimilarEquiv
import UnicoProofs.Platonici.ConteggioBenchmark
import UnicoProofs.Platonici.RegolariBenchmark

/-!
RIGIDITÀ — IL MAGGIORANTE E L'EQUAZIONE FINALE (gate 8, 19 lug 2026).

Il minorante `5 ≤ platonicCount 3` è già scaricato (RegolariBenchmark).
Qui la controparte condizionale: se ogni politopo regolare di ℝ³ è
simile a uno dei cinque testimoni (LA RIGIDITÀ, in scarico), allora le
classi sono al più cinque, e con il minorante `platonicCount 3 = 5`.
L'intera campagna si riduce così a scaricare UNA ipotesi:
`∀ P : regularPolytopes 3, ∃ i, regularSimilar 3 P (testimone i)`.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- I cinque testimoni come politopi regolari. -/
def testimone : Fin 5 → regularPolytopes 3 :=
  ![⟨tetraedroBM, tetraedroBM_isRegular⟩,
    ⟨cuboBM, cuboBM_isRegular⟩,
    ⟨ottaedroBM, ottaedroBM_isRegular⟩,
    ⟨dodecaedroBM, dodecaedroBM_isRegular⟩,
    ⟨icosaedroBM, icosaedroBM_isRegular⟩]

/-- Simili ⟹ stessa classe. -/
theorem classe_eq_of_similar {P Q : regularPolytopes 3}
    (h : regularSimilar 3 P Q) : classe 3 P = classe 3 Q := by
  ext R
  constructor
  · intro hR
    exact similar_trans (similar_symm h) hR
  · intro hR
    exact similar_trans h hR

/-- **IL MAGGIORANTE CONDIZIONALE**: se ogni regolare è simile a un
testimone, le classi sono al più cinque. -/
theorem platonicCount3_le_cinque_di
    (hrig : ∀ P : regularPolytopes 3,
      ∃ i : Fin 5, regularSimilar 3 P (testimone i)) :
    platonicCount 3 ≤ 5 := by
  classical
  have hsub : {S : Set (regularPolytopes 3) |
      ∃ P, S = {Q : regularPolytopes 3 | regularSimilar 3 P Q}} ⊆
      Set.range (fun i : Fin 5 => classe 3 (testimone i)) := by
    rintro S ⟨P, rfl⟩
    obtain ⟨i, hi⟩ := hrig P
    exact ⟨i, (classe_eq_of_similar hi).symm⟩
  calc Set.encard {S : Set (regularPolytopes 3) |
        ∃ P, S = {Q : regularPolytopes 3 | regularSimilar 3 P Q}}
      ≤ Set.encard
        (Set.range (fun i : Fin 5 => classe 3 (testimone i))) :=
        Set.encard_le_encard hsub
    _ = Set.encard ((fun i : Fin 5 => classe 3 (testimone i)) ''
        Set.univ) := by rw [Set.image_univ]
    _ ≤ Set.encard (Set.univ : Set (Fin 5)) := Set.encard_image_le _ _
    _ = 5 := by simp [Set.encard_univ]

/-- **L'EQUAZIONE FINALE CONDIZIONALE**: rigidità ⟹
`platonicCount 3 = 5`. -/
theorem platonicCount3_eq_cinque_di
    (hrig : ∀ P : regularPolytopes 3,
      ∃ i : Fin 5, regularSimilar 3 P (testimone i)) :
    platonicCount 3 = 5 :=
  le_antisymm (platonicCount3_le_cinque_di hrig) cinque_le_platonicCount3

end LeanEval.Geometry.PlatonicClassification
