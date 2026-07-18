import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.InvarianteSimilarita
import UnicoProofs.Platonici.IstanzeBenchmark

/-!
FASE 2, P6 — IL MOTORE DEL CONTEGGIO (18 lug 2026).

Forma condizionale: dati gli `IsRegular` dei cinque solidi (P2-P4, in arrivo),
le loro classi di similitudine sono cinque elementi distinti dell'insieme di
cui `platonicCount 3` è l'encard. Quindi `5 ≤ platonicCount 3`.
La distinzione delle classi viene dalle dieci non-similarità (P5).
-/

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- La classe di similitudine di un politopo regolare. -/
def classe (d : ℕ) (P : regularPolytopes d) : Set (regularPolytopes d) :=
  {Q | regularSimilar d P Q}

theorem classe_mem_quoziente (d : ℕ) (P : regularPolytopes d) :
    classe d P ∈ {S : Set (regularPolytopes d) |
      ∃ P', S = {Q : regularPolytopes d | regularSimilar d P' Q}} :=
  ⟨P, rfl⟩

theorem self_mem_classe (d : ℕ) (P : regularPolytopes d) :
    P ∈ classe d P :=
  similar_refl (P : ConvexPolytope d)

/-- Classi uguali ⟹ i rappresentanti sono simili. -/
theorem similar_of_classe_eq {d : ℕ} {P Q : regularPolytopes d}
    (h : classe d P = classe d Q) :
    ConvexPolytope.Similar (P : ConvexPolytope d) (Q : ConvexPolytope d) := by
  have hQ : Q ∈ classe d Q := self_mem_classe d Q
  rw [← h] at hQ
  exact hQ

/-- IL MOTORE: cinque regolari a coppie non simili ⟹ 5 ≤ platonicCount 3. -/
theorem cinque_le_platonicCount3_di
    (hT : tetraedroBM.IsRegular) (hC : cuboBM.IsRegular)
    (hO : ottaedroBM.IsRegular) (hD : dodecaedroBM.IsRegular)
    (hI : icosaedroBM.IsRegular) : 5 ≤ platonicCount 3 := by
  classical
  set e1 : regularPolytopes 3 := ⟨tetraedroBM, hT⟩ with he1
  set e2 : regularPolytopes 3 := ⟨cuboBM, hC⟩ with he2
  set e3 : regularPolytopes 3 := ⟨ottaedroBM, hO⟩ with he3
  set e4 : regularPolytopes 3 := ⟨dodecaedroBM, hD⟩ with he4
  set e5 : regularPolytopes 3 := ⟨icosaedroBM, hI⟩ with he5
  have h12 : classe 3 e1 ≠ classe 3 e2 :=
    fun h => non_simili_tetraedro_cubo (similar_of_classe_eq h)
  have h13 : classe 3 e1 ≠ classe 3 e3 :=
    fun h => non_simili_tetraedro_ottaedro (similar_of_classe_eq h)
  have h14 : classe 3 e1 ≠ classe 3 e4 :=
    fun h => non_simili_tetraedro_dodecaedro (similar_of_classe_eq h)
  have h15 : classe 3 e1 ≠ classe 3 e5 :=
    fun h => non_simili_tetraedro_icosaedro (similar_of_classe_eq h)
  have h23 : classe 3 e2 ≠ classe 3 e3 :=
    fun h => non_simili_cubo_ottaedro (similar_of_classe_eq h)
  have h24 : classe 3 e2 ≠ classe 3 e4 :=
    fun h => non_simili_cubo_dodecaedro (similar_of_classe_eq h)
  have h25 : classe 3 e2 ≠ classe 3 e5 :=
    fun h => non_simili_cubo_icosaedro (similar_of_classe_eq h)
  have h34 : classe 3 e3 ≠ classe 3 e4 :=
    fun h => non_simili_ottaedro_dodecaedro (similar_of_classe_eq h)
  have h35 : classe 3 e3 ≠ classe 3 e5 :=
    fun h => non_simili_ottaedro_icosaedro (similar_of_classe_eq h)
  have h45 : classe 3 e4 ≠ classe 3 e5 :=
    fun h => non_simili_dodecaedro_icosaedro (similar_of_classe_eq h)
  have hsub : ({classe 3 e1, classe 3 e2, classe 3 e3, classe 3 e4, classe 3 e5} :
      Set (Set (regularPolytopes 3)))
      ⊆ {S | ∃ P', S = {Q : regularPolytopes 3 | regularSimilar 3 P' Q}} := by
    intro S hS
    rcases hS with h | h | h | h | h <;> subst h <;>
      first
        | exact classe_mem_quoziente 3 e1
        | exact classe_mem_quoziente 3 e2
        | exact classe_mem_quoziente 3 e3
        | exact classe_mem_quoziente 3 e4
        | exact classe_mem_quoziente 3 e5
  have hcard : ({classe 3 e1, classe 3 e2, classe 3 e3, classe 3 e4, classe 3 e5} :
      Set (Set (regularPolytopes 3))).encard = 5 := by
    rw [Set.encard_insert_of_notMem (by simp [h12, h13, h14, h15]),
      Set.encard_insert_of_notMem (by simp [h23, h24, h25]),
      Set.encard_insert_of_notMem (by simp [h34, h35]),
      Set.encard_insert_of_notMem (by simp [h45]),
      Set.encard_singleton]
    rfl
  show (5 : ℕ∞) ≤ Set.encard _
  calc (5 : ℕ∞) = _ := hcard.symm
    _ ≤ _ := Set.encard_le_encard hsub

end LeanEval.Geometry.PlatonicClassification
