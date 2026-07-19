import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.Trasportatore
import UnicoProofs.Platonici.RelazioniCoxeter
import UnicoProofs.Platonici.Iperpiano

/-!
MOTORE COXETER, PASSO 18 — I NORMALI DELLE RIFLESSIONI (19 lug 2026).

Dall'iperpiano dei punti fissi si estrae il NORMALE UNITARIO `αᵢ`: il
generatore della retta ortogonale alla giacitura dell'iperpiano. È il
vettore su cui si costruirà la matrice di Gram.

L'iperpiano è descritto in forma implicita: `rᵢ x = x ↔ ⟪αᵢ, x − p⟫ = 0`.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Una retta ortogonale a un iperpiano contiene un vettore unitario. -/
theorem esiste_unitario_ortogonale {W : Submodule ℝ (E n)}
    (hW : Module.finrank ℝ W + 1 = n) :
    ∃ α : E n, ‖α‖ = 1 ∧ α ∈ Wᗮ ∧ Wᗮ = ℝ ∙ α := by
  have hrank : Module.finrank ℝ (Wᗮ : Submodule ℝ (E n)) = 1 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal (K := W) (𝕜 := ℝ)
    have hn : Module.finrank ℝ (E n) = n := by simp
    omega
  obtain ⟨v, hv⟩ := finrank_eq_one_iff'.mp hrank
  obtain ⟨hvne, hspan⟩ := hv
  have hvnorm : ‖(v : E n)‖ ≠ 0 := by
    simpa using fun hc => hvne (Subtype.ext (by simpa using hc))
  refine ⟨‖(v : E n)‖⁻¹ • (v : E n), ?_, ?_, ?_⟩
  · rw [norm_smul]
    simp [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), hvnorm]
  · exact Submodule.smul_mem _ _ v.2
  · apply le_antisymm
    · intro w hw
      obtain ⟨c, hc⟩ := hspan ⟨w, hw⟩
      refine Submodule.mem_span_singleton.mpr ⟨c * ‖(v : E n)‖, ?_⟩
      have hcv : c • (v : E n) = w := congrArg Subtype.val hc
      rw [mul_smul, smul_inv_smul₀ hvnorm]
      exact hcv
    · rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.smul_mem _ _ v.2

/-- **Il normale della riflessione semplice**: l'iperpiano dei punti
fissi di `rᵢ` è descritto da un vettore unitario `α` e un punto `p`. -/
theorem esiste_normale (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) :
    ∃ α p : E n, ‖α‖ = 1 ∧
      (∀ x : E n, simpleReflection P hreg F i x = x ↔
        ⟪α, x - p⟫ = 0) := by
  obtain ⟨H, hdim, hfix⟩ := simpleReflection_fix_eq_hyperplane P hreg F i
  -- un punto fisso esiste: i centroidi
  obtain ⟨q, _, hqfix⟩ := centroidi_fissi_indipendenti P hreg F i
  have hp : q i ∈ H := (hfix (q i)).mp (hqfix i)
  obtain ⟨α, hαnorm, _, hspan⟩ := esiste_unitario_ortogonale hdim
  refine ⟨α, q i, hαnorm, fun x => ?_⟩
  rw [hfix x]
  constructor
  · intro hx
    have hmem : x - q i ∈ H.direction := by
      have := AffineSubspace.vsub_mem_direction hx hp
      simpa [vsub_eq_sub] using this
    have hα : α ∈ H.directionᗮ := by
      rw [hspan]
      exact Submodule.mem_span_singleton_self α
    rw [real_inner_comm]
    exact hα (x - q i) hmem
  · intro hx
    have hmem : x - q i ∈ H.direction := by
      have hbot : (H.directionᗮ)ᗮ = H.direction :=
        Submodule.orthogonal_orthogonal _
      rw [← hbot, hspan]
      intro w hw
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
      rw [← hc, real_inner_smul_left, hx, mul_zero]
    have hx' : x = (x - q i) +ᵥ q i := by
      simp [vadd_eq_add]
    rw [hx']
    exact AffineSubspace.vadd_mem_of_mem_direction hmem hp

end LeanEval.Geometry.PlatonicClassification
