import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FanVertice

/-!
RIGIDITÀ, GATE 4 (primo ingrediente) — IL PIANO DAI DUE RAGGI (19 lug 2026).

`faccetta_determinata` (gate 2 di sol) chiede tre cose per identificare due
faccette: stesso piano, stesso lato, stesso semipiano. Qui il PRIMO: una
faccia bidimensionale che contiene un punto v e due direzioni indipendenti
uscenti da v ha per giacitura esattamente lo span di quelle due direzioni;
quindi due facce bidimensionali con lo stesso v e gli stessi due raggi
stanno nello STESSO PIANO affine. È il ponte fra l'uguaglianza dei raggi
(che il gate 2 consegna) e l'identificazione delle faccette.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Due punti di un insieme danno una differenza nella giacitura. -/
theorem sub_mem_vectorSpan {A : Set (E 3)} {x v : E 3}
    (hx : x ∈ A) (hv : v ∈ A) : x - v ∈ vectorSpan ℝ A := by
  have h := vsub_mem_vectorSpan ℝ hx hv
  exact h

/-- **LA GIACITURA DAI DUE RAGGI**: una faccia di rank 2 con due
direzioni indipendenti uscenti da un suo punto ha per giacitura il loro
span. -/
theorem vectorSpan_eq_span_due {A : Set (E 3)} {v x y : E 3}
    (hv : v ∈ A) (hx : x ∈ A) (hy : y ∈ A)
    (hind : LinearIndependent ℝ ![x - v, y - v])
    (hrank : Module.finrank ℝ (vectorSpan ℝ A) = 2) :
    vectorSpan ℝ A = Submodule.span ℝ {x - v, y - v} := by
  classical
  have hle : Submodule.span ℝ ({x - v, y - v} : Set (E 3)) ≤
      vectorSpan ℝ A := by
    rw [Submodule.span_le]
    intro z hz
    rcases hz with hz | hz
    · rw [hz]; exact sub_mem_vectorSpan hx hv
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]; exact sub_mem_vectorSpan hy hv
  have hrange : (Set.range ![x - v, y - v]) = {x - v, y - v} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (hz | hz)
      · exact ⟨0, hz.symm⟩
      · rw [Set.mem_singleton_iff] at hz
        exact ⟨1, hz.symm⟩
  have hspan2 : Module.finrank ℝ
      (Submodule.span ℝ ({x - v, y - v} : Set (E 3))) = 2 := by
    rw [← hrange]
    have h := finrank_span_eq_card hind
    rw [h]
    simp
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hspan2, hrank])).symm

/-- **STESSO VERTICE E STESSI DUE RAGGI ⟹ STESSO PIANO**. -/
theorem affineSpan_eq_of_raggi_eq {A B : Set (E 3)} {v x y x' y' : E 3}
    (hvA : v ∈ A) (hxA : x ∈ A) (hyA : y ∈ A)
    (hvB : v ∈ B) (hxB : x' ∈ B) (hyB : y' ∈ B)
    (hindA : LinearIndependent ℝ ![x - v, y - v])
    (hindB : LinearIndependent ℝ ![x' - v, y' - v])
    (hrankA : Module.finrank ℝ (vectorSpan ℝ A) = 2)
    (hrankB : Module.finrank ℝ (vectorSpan ℝ B) = 2)
    (hspan : Submodule.span ℝ ({x - v, y - v} : Set (E 3)) =
      Submodule.span ℝ ({x' - v, y' - v} : Set (E 3))) :
    affineSpan ℝ A = affineSpan ℝ B := by
  classical
  have hdirA : vectorSpan ℝ A = Submodule.span ℝ {x - v, y - v} :=
    vectorSpan_eq_span_due hvA hxA hyA hindA hrankA
  have hdirB : vectorSpan ℝ B = Submodule.span ℝ {x' - v, y' - v} :=
    vectorSpan_eq_span_due hvB hxB hyB hindB hrankB
  have hdir : (affineSpan ℝ A).direction = (affineSpan ℝ B).direction := by
    rw [direction_affineSpan, direction_affineSpan, hdirA, hdirB, hspan]
  have hvA' : v ∈ affineSpan ℝ A := subset_affineSpan ℝ A hvA
  have hvB' : v ∈ affineSpan ℝ B := subset_affineSpan ℝ B hvB
  exact AffineSubspace.ext_of_direction_eq hdir ⟨v, hvA', hvB'⟩

/-- Il raggio unitario e il punto che lo genera hanno lo stesso span. -/
theorem span_pair_smul {v x y : E 3} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Submodule.span ℝ ({a • (x - v), b • (y - v)} : Set (E 3)) =
      Submodule.span ℝ ({x - v, y - v} : Set (E 3)) := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    rcases hz with hz | hz
    · rw [hz]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl rfl))
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span (Or.inr rfl))
  · rw [Submodule.span_le]
    intro z hz
    rcases hz with hz | hz
    · rw [hz]
      have hmem : a • (x - v) ∈ Submodule.span ℝ
          ({a • (x - v), b • (y - v)} : Set (E 3)) :=
        Submodule.subset_span (Or.inl rfl)
      have hsmul : a⁻¹ • (a • (x - v)) ∈ Submodule.span ℝ
          ({a • (x - v), b • (y - v)} : Set (E 3)) :=
        Submodule.smul_mem _ _ hmem
      simpa [smul_smul, inv_mul_cancel₀ ha] using hsmul
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have hmem : b • (y - v) ∈ Submodule.span ℝ
          ({a • (x - v), b • (y - v)} : Set (E 3)) :=
        Submodule.subset_span (Or.inr rfl)
      have hsmul : b⁻¹ • (b • (y - v)) ∈ Submodule.span ℝ
          ({a • (x - v), b • (y - v)} : Set (E 3)) :=
        Submodule.smul_mem _ _ hmem
      simpa [smul_smul, inv_mul_cancel₀ hb] using hsmul

end LeanEval.Geometry.PlatonicClassification
