import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.Indipendenza
import UnicoProofs.Platonici.GramCanonica

/-!
LA POSITIVITÀ EFFETTIVA DELLA GRAM (20 lug 2026).

Correzione terminologica (rilievo del revisore): `gram_definita_positiva`
dimostra `ker G = 0` (NON-degenerazione), non la vera positività definita.
Per una Gram di vettori linearmente indipendenti la positività vera è
naturale: `xᵀ G x = ‖Σ xᵢ αᵢ‖² > 0` per `x ≠ 0`. Questa è la forma che il
ponte di Sylvester consumerà.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **La forma quadratica di una Gram di vettori indipendenti è
DEFINITA POSITIVA**: `x ≠ 0 ⟹ Σᵢⱼ xᵢxⱼ⟪αᵢ,αⱼ⟫ > 0`. -/
theorem gram_forma_positiva {ι : Type*} [Fintype ι] (α : ι → E n)
    (hind : LinearIndependent ℝ α) (g : ι → ℝ) (hg : g ≠ 0) :
    0 < ∑ i, ∑ j, g i * g j * ⟪α i, α j⟫ := by
  -- la forma è ‖Σ gᵢ αᵢ‖²
  have hform : (∑ i, ∑ j, g i * g j * ⟪α i, α j⟫)
      = ⟪∑ i, g i • α i, ∑ j, g j • α j⟫ := by
    rw [sum_inner]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [inner_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hform, real_inner_self_eq_norm_sq]
  have hne : (∑ i, g i • α i) ≠ 0 := by
    intro h
    apply hg
    funext i
    exact (Fintype.linearIndependent_iff.mp hind) g h i
  positivity

/-- **La Gram canonica del politopo è definita positiva** (forma forte). -/
theorem gram_canonica_forma_positiva (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (hn : 3 ≤ n) (g : Fin n → ℝ)
    (hg : g ≠ 0) :
    0 < ∑ i, ∑ j, g i * g j *
      ⟪normaleOrientato P hreg F i, normaleOrientato P hreg F j⟫ :=
  gram_forma_positiva (normaleOrientato P hreg F)
    (normali_orientati_linearIndependent P hreg F (by omega)) g hg

end LeanEval.Geometry.PlatonicClassification
