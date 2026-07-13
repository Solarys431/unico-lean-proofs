/-
Copyright (c) 2026 Daniele Cappello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Cappello

Part of a Lean formalization of Feuerbach's theorem, produced by the
UNICO/NOUS autonomous certification pipeline (Claude, by Anthropic).
Every step is kernel-checked.
-/

import Mathlib
import UnicoProofs.Feuerbach.Normalization
import UnicoProofs.Feuerbach.TouchpointTangency

/-!
# Affine arithmetic of the normalization map

* `Φ_smul_vadd`: Φ respects points of the form `k•v +ᵥ q` (used for the Euler line)
* `Φ_centroid`: the centroid maps to the average of the three normalized vertices
* `Φinv` / `Φ_Φinv`: the explicit inverse of Φ (for the circumcenter candidate)
* `dist_eq_r_mul`: transporting distances back through Φ
* `conj_eq_inv` / `Φ_vsub_div`: on the unit circle, conjugation is inversion
-/

namespace FeuerbachFinal1

open EuclideanGeometry Affine Module FeuerbachMap FeuerbachWeld

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

/-- Φ on points of the form `k•v +ᵥ q`: becomes a combination in `ℂ`. -/
theorem Φ_smul_vadd (c : P) (r : ℝ) (k : ℝ) (v : V) (q : P) :
    Φ (V := V) c r ((k • v) +ᵥ q)
      = (k : ℂ) * (toComplex (V := V) v) / (r : ℂ) + Φ (V := V) c r q := by
  rw [Φ, Φ, vadd_vsub_assoc, map_add, map_smul, add_div, Complex.real_smul]

/-- The normalized centroid is the average of the normalized vertices. -/
theorem Φ_centroid (c : P) (r : ℝ) (t : Triangle ℝ P) :
    Φ (V := V) c r (Finset.univ.centroid ℝ t.points)
      = (Φ (V := V) c r (t.points 0) + Φ (V := V) c r (t.points 1)
          + Φ (V := V) c r (t.points 2)) / 3 := by
  have hsum : ∑ i, Finset.univ.centroidWeights ℝ (ι := Fin 3) i = 1 :=
    Finset.univ.sum_centroidWeights_eq_one_of_nonempty ℝ Finset.univ_nonempty
  have hcomb := Finset.univ.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    (Finset.univ.centroidWeights ℝ) t.points hsum c
  rw [Finset.centroid_def, hcomb, Φ, vadd_vsub, Finset.weightedVSubOfPoint_apply,
    Fin.sum_univ_three]
  simp only [Finset.centroidWeights_apply, Finset.card_univ, Fintype.card_fin,
    map_add, map_smul, Complex.real_smul]
  rw [Φ, Φ, Φ]
  push_cast
  field_simp

/-- **The explicit inverse of Φ**: `z ↦ toComplex⁻¹(r•z) +ᵥ c`. -/
noncomputable def Φinv (c : P) (r : ℝ) (z : ℂ) : P :=
  ((toComplex (V := V)).symm ((r : ℝ) • z)) +ᵥ c

/-- Φ ∘ Φinv = id (for `r ≠ 0`). -/
theorem Φ_Φinv (c : P) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Φ (V := V) c r (Φinv (V := V) c r z) = z := by
  rw [Φinv, Φ, vadd_vsub, LinearIsometryEquiv.apply_symm_apply, Complex.real_smul]
  have hr' : (r : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact hr.ne'
  field_simp

/-- Transporting distances backward: `dist x y = r · dist (Φx) (Φy)`. -/
theorem dist_eq_r_mul (c : P) {r : ℝ} (hr : 0 < r) (x y : P) :
    dist x y = r * dist (Φ (V := V) c r x) (Φ (V := V) c r y) := by
  rw [dist_Φ (V := V) c hr x y]
  field_simp

/-- On the unit circle, conjugation is inversion: `conj z = z⁻¹` when `‖z‖ = 1`. -/
theorem conj_eq_inv {z : ℂ} (hz : ‖z‖ = 1) : (starRingEnd ℂ) z = z⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
  simp

/-- The difference under Φ: `toComplex (x −ᵥ y) / r = Φx − Φy`. -/
theorem Φ_vsub_div (c : P) (r : ℝ) (x y : P) :
    (toComplex (V := V) (x -ᵥ y)) / (r : ℂ) = Φ (V := V) c r x - Φ (V := V) c r y := by
  rw [Φ, Φ, div_sub_div_same, ← map_sub, vsub_sub_vsub_cancel_right]

end FeuerbachFinal1
