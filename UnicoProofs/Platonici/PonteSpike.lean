import Mathlib

/-!
A5 — IL PONTE DELLO SPIKE (campagna #50, assemblaggio).

Due raccordi che portano l'uscita del killer (`passo_del_fan`: θ = ±2π/q)
nella bocca dello Spike-0 (`spike_somma_sotto_due_pi`):

* `inner_rotation_eq_cos` — il prodotto interno tra un versore e il suo
  ruotato è il coseno del passo;
* `inner_rotation_pm` — per θ = ±2π/q il coseno è `Real.cos (2π/q)`
  (il segno dell'orientazione muore nel coseno);
* `scomposizione_assiale` — un versore con colatitudine c ∈ (0,1) rispetto
  all'asse ŵ si scrive c•ŵ + s•ê con ê versore ortogonale, s = √(1−c²):
  esattamente la forma `cos β•w + sin β•e` chiesta dallo Spike-0, con
  β = arccos c ∈ (0, π/2).
-/

open Real
open scoped RealInnerProductSpace

namespace PlatoniciA5

section Rotazione

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- Il prodotto interno tra un versore e il suo ruotato è il coseno del passo. -/
theorem inner_rotation_eq_cos (o : Orientation ℝ E (Fin 2)) (θ : Real.Angle)
    (x : E) (hx : ‖x‖ = 1) :
    ⟪x, o.rotation θ x⟫ = Real.Angle.cos θ := by
  have hx0 : x ≠ 0 := by
    intro h; rw [h, norm_zero] at hx; norm_num at hx
  rw [o.inner_eq_norm_mul_norm_mul_cos_oangle, LinearIsometryEquiv.norm_map, hx,
    o.oangle_rotation_self_right hx0]
  ring

/-- Per un passo θ = ±2π/q il prodotto interno è cos(2π/q): il segno muore. -/
theorem inner_rotation_pm (o : Orientation ℝ E (Fin 2)) (θ : Real.Angle)
    (q : ℕ)
    (hθ : θ = ((2 * π / q : ℝ) : Real.Angle) ∨ θ = ((-(2 * π / q) : ℝ) : Real.Angle))
    (x : E) (hx : ‖x‖ = 1) :
    ⟪x, o.rotation θ x⟫ = Real.cos (2 * π / q) := by
  rcases hθ with h | h <;>
    rw [inner_rotation_eq_cos o θ x hx, h, Real.Angle.cos_coe]
  rw [Real.cos_neg]

end Rotazione

section Scomposizione

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Scomposizione assiale: un versore u con colatitudine c ∈ (0,1) rispetto
al versore-asse ŵ si scrive u = c•ŵ + √(1−c²)•ê con ê versore ortogonale a ŵ.
È la forma richiesta dallo Spike-0 con β = arccos c. -/
theorem scomposizione_assiale (w u : V) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    {c : ℝ} (hc : ⟪w, u⟫ = c) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ e : V, ‖e‖ = 1 ∧ ⟪w, e⟫ = 0 ∧
      u = c • w + Real.sqrt (1 - c ^ 2) • e := by
  set s : ℝ := Real.sqrt (1 - c ^ 2) with hs
  have hc2 : c ^ 2 < 1 := by nlinarith
  have hspos : 0 < s := Real.sqrt_pos.mpr (by nlinarith)
  have hs2 : s ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (by nlinarith)
  refine ⟨s⁻¹ • (u - c • w), ?_, ?_, ?_⟩
  · have hnorm2 : ‖u - c • w‖ ^ 2 = 1 - c ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, real_inner_smul_right,
        real_inner_comm w u, hc]
      simp only [Real.norm_eq_abs, abs_of_pos hc0]
      rw [hw, hu]
      ring
    have hnorm : ‖u - c • w‖ = s := by
      rw [hs]
      rw [show (1 : ℝ) - c ^ 2 = ‖u - c • w‖ ^ 2 from hnorm2.symm]
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    rw [norm_smul, hnorm, norm_inv, Real.norm_eq_abs, abs_of_pos hspos]
    field_simp
  · rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right, hc,
      real_inner_self_eq_norm_sq, hw]
    ring
  · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hspos), one_smul]
    abel

/-- La colatitudine positiva e sotto 1 dà β = arccos c ∈ (0, π/2) con
cos β = c e sin β = √(1−c²): il dizionario completo verso lo Spike-0. -/
theorem beta_di_colatitudine {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ β : ℝ, 0 < β ∧ β < π / 2 ∧ Real.cos β = c ∧
      Real.sin β = Real.sqrt (1 - c ^ 2) := by
  refine ⟨Real.arccos c, ?_, ?_, ?_, ?_⟩
  · exact Real.arccos_pos.mpr hc1
  · exact Real.arccos_lt_pi_div_two.mpr hc0
  · exact Real.cos_arccos (by linarith) (le_of_lt hc1)
  · rw [Real.sin_arccos]

end Scomposizione

end PlatoniciA5
