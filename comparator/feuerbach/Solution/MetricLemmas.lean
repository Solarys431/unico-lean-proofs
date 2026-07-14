/-
Copyright (c) 2026 Daniele Cappello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Cappello

Part of a Lean formalization of Feuerbach's theorem, produced by the
UNICO/NOUS autonomous certification pipeline (Claude, by Anthropic).
Every step is kernel-checked.
-/

import Mathlib
import Solution.Core
import Solution.Normalization
import Solution.TouchpointTangency
import Solution.VertexFormula
import Solution.AffineTransport
import Solution.Circumcenter
import Solution.NinePointCenter

/-!
# Center distance and nine-point radius via the model parameter

* `Φ_affineCombination`: Φ sends affine combinations to combinations in ℂ
* `dist_excenter_ninePointCenter`: the distance between the centers is `r·|W+1|`
* `ninePointRadius_eq`: the nine-point radius is `r·|W|`

(Refactor requested by sol: the two derivations are extracted from the body of
the disjunctive theorem and become reusable for the branch-specific theorems.)
-/

namespace FeuerbachWeld2

open EuclideanGeometry Affine Module
open FeuerbachCore FeuerbachMap FeuerbachWeld FeuerbachAssembly
open FeuerbachFinal1 FeuerbachFinal2 FeuerbachFinal3

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

/-- **Φ transports affine combinations** (the general version of `Φ_centroid`). -/
theorem Φ_affineCombination (c : P) (r : ℝ) (p : Fin 3 → P) (lam : Fin 3 → ℝ)
    (hlam : ∑ i, lam i = 1) :
    Φ (V := V) c r (Finset.univ.affineCombination ℝ p lam)
      = ∑ i, (lam i : ℂ) * Φ (V := V) c r (p i) := by
  rw [Finset.univ.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    lam p hlam c]
  rw [Φ, vadd_vsub, Finset.weightedVSubOfPoint_apply]
  rw [map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Complex.real_smul, Φ]
  ring

variable {t : Triangle ℝ P} {signs : Finset (Fin 3)}

/-- The distance between the sphere's center and the nine-point center, as a
function of the model's real parameter `W`. -/
theorem dist_excenter_ninePointCenter (hE : t.ExcenterExists signs)
    (hr : 0 < t.exradius signs) {W : ℝ}
    (hW : w (τ (V := V) t signs 0) (τ (V := V) t signs 1) (τ (V := V) t signs 2)
      = (W : ℂ)) :
    dist (t.exsphere signs).center t.ninePointCircle.center
      = t.exradius signs * |W + 1| := by
  set c := t.excenter signs
  set r := t.exradius signs
  set τ₀ := τ (V := V) t signs 0
  set τ₁ := τ (V := V) t signs 1
  set τ₂ := τ (V := V) t signs 2
  obtain ⟨h01, h12, h20⟩ := τ_add_ne (V := V) hE hr
  have hPτ := P_τ_ne (V := V) hE hr
  have hn0 : ‖τ₀‖ = 1 := norm_Φ_touchpoint_eq_one t signs hE hr 0
  have hn1 : ‖τ₁‖ = 1 := norm_Φ_touchpoint_eq_one t signs hE hr 1
  have hn2 : ‖τ₂‖ = 1 := norm_Φ_touchpoint_eq_one t signs hE hr 2
  have hz0 : τ₀ ≠ 0 := by intro h; rw [h] at hn0; simp at hn0
  have hz1 : τ₁ ≠ 0 := by intro h; rw [h] at hn1; simp at hn1
  have hz2 : τ₂ ≠ 0 := by intro h; rw [h] at hn2; simp at hn2
  have hNc : N τ₀ τ₁ τ₂ * (starRingEnd ℂ) (N τ₀ τ₁ τ₂) = (w τ₀ τ₁ τ₂ + 1) ^ 2 := by
    rw [conj_N hn0 hn1 hn2]
    exact normSq_N hz0 hz1 hz2 hPτ
  have hnormN : ‖N τ₀ τ₁ τ₂‖ = |W + 1| := by
    have h2 : Complex.normSq (N τ₀ τ₁ τ₂) = (W + 1) ^ 2 := by
      have h1 : (Complex.normSq (N τ₀ τ₁ τ₂) : ℂ) = (((W + 1) ^ 2 : ℝ) : ℂ) := by
        rw [← Complex.mul_conj, hNc, hW]; push_cast; ring
      exact_mod_cast h1
    rw [← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq, h2,
      Real.sqrt_sq_eq_abs]
  have hNP : Φ (V := V) c r t.ninePointCircle.center = N τ₀ τ₁ τ₂ :=
    Φ_ninePointCenter (V := V) hE hr
  have h1 : dist c t.ninePointCircle.center = r * |W + 1| := by
    rw [dist_eq_r_mul (V := V) c hr, Φ_center, hNP, dist_zero_left, hnormN]
  simpa [Simplex.exsphere_center] using h1

/-- The nine-point radius, as a function of the model's real parameter `W`. -/
theorem ninePointRadius_eq (hE : t.ExcenterExists signs)
    (hr : 0 < t.exradius signs) {W : ℝ}
    (hW : w (τ (V := V) t signs 0) (τ (V := V) t signs 1) (τ (V := V) t signs 2)
      = (W : ℂ)) :
    t.ninePointCircle.radius = t.exradius signs * |W| := by
  set c := t.excenter signs
  set r := t.exradius signs
  set τ₀ := τ (V := V) t signs 0
  set τ₁ := τ (V := V) t signs 1
  set τ₂ := τ (V := V) t signs 2
  set Om := O τ₀ τ₁ τ₂ with hOm
  obtain ⟨h01, h12, h20⟩ := τ_add_ne (V := V) hE hr
  have hPτ := P_τ_ne (V := V) hE hr
  have hn0 : ‖τ₀‖ = 1 := norm_Φ_touchpoint_eq_one t signs hE hr 0
  have hn1 : ‖τ₁‖ = 1 := norm_Φ_touchpoint_eq_one t signs hE hr 1
  have hn2 : ‖τ₂‖ = 1 := norm_Φ_touchpoint_eq_one t signs hE hr 2
  have hv0 : Φ (V := V) c r (t.points 0) = 2 * τ₁ * τ₂ / (τ₁ + τ₂) :=
    Φ_vertex_eq t signs hE hr (by decide) (by decide) (by decide)
  have hnormV : ‖Φ (V := V) c r (t.points 0) - Om‖ = 2 * |W| := by
    have hd0 : (Φ (V := V) c r (t.points 0) - Om)
        * (starRingEnd ℂ) (Φ (V := V) c r (t.points 0) - Om)
        = 4 * (e₃ τ₀ τ₁ τ₂) ^ 2 / (FeuerbachCore.P τ₀ τ₁ τ₂) ^ 2 := by
      rw [hv0, hOm]
      exact vertex_sub_O_mul_conj hn0 hn1 hn2 hPτ h12
    have hw2 : 4 * (e₃ τ₀ τ₁ τ₂) ^ 2 / (FeuerbachCore.P τ₀ τ₁ τ₂) ^ 2
        = (((4 * W ^ 2 : ℝ)) : ℂ) := by
      have h4 : (4 : ℂ) * (e₃ τ₀ τ₁ τ₂) ^ 2 / (FeuerbachCore.P τ₀ τ₁ τ₂) ^ 2
          = (2 * w τ₀ τ₁ τ₂) ^ 2 := by
        unfold w
        field_simp
        ring
      rw [h4, hW]; push_cast; ring
    have h2 : Complex.normSq (Φ (V := V) c r (t.points 0) - Om) = 4 * W ^ 2 := by
      have h1 : (Complex.normSq (Φ (V := V) c r (t.points 0) - Om) : ℂ)
          = (((4 * W ^ 2 : ℝ)) : ℂ) := by
        rw [← Complex.mul_conj, hd0, hw2]
      exact_mod_cast h1
    rw [← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq, h2]
    rw [show (4 : ℝ) * W ^ 2 = (2 * |W|) ^ 2 by rw [mul_pow]; rw [sq_abs]; norm_num,
      Real.sqrt_sq (by positivity)]
  have hCR : t.circumradius = r * ‖Φ (V := V) c r (t.points 0) - Om‖ :=
    circumradius_eq (V := V) hE hr
  rw [Simplex.ninePointCircle_radius, hCR, hnormV]
  push_cast
  ring

end FeuerbachWeld2
