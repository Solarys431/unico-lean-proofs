/-
Copyright (c) 2026 Daniele Cappello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Cappello

Part of a Lean formalization of Feuerbach's theorem, produced by the
UNICO/NOUS autonomous certification pipeline (Claude, by Anthropic).
Every step is kernel-checked.
-/

import Mathlib
import UnicoProofs.Feuerbach.Core
import UnicoProofs.Feuerbach.Normalization
import UnicoProofs.Feuerbach.TouchpointTangency
import UnicoProofs.Feuerbach.VertexFormula
import UnicoProofs.Feuerbach.AffineTransport
import UnicoProofs.Feuerbach.Circumcenter

/-!
# The nine-point center in the model, and the disjunctive tangency theorem

* `conj_N`: the conjugate of the model's nine-point center
* `Φ_ninePointCenter`: mathlib's nine-point center maps to `N = e₂²/P`
* `circumradius_eq`: the circumradius transports through Φ
* `feuerbach`: the nine-point circle and the incircle/excircle are TANGENT
  (internally in one direction or the other, or externally)
-/

namespace FeuerbachFinal3

open EuclideanGeometry Affine Module
open FeuerbachCore FeuerbachMap FeuerbachWeld FeuerbachAssembly
open FeuerbachFinal1 FeuerbachFinal2

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

/-- The conjugate of `N` in the model: `conj (N a b c) = N a⁻¹ b⁻¹ c⁻¹`. -/
theorem conj_N {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    (starRingEnd ℂ) (N a b c) = N a⁻¹ b⁻¹ c⁻¹ := by
  unfold N e₂ FeuerbachCore.P
  simp only [map_div₀, map_pow, map_mul, map_add, conj_eq_inv ha, conj_eq_inv hb,
    conj_eq_inv hc]

variable {t : Triangle ℝ P} {signs : Finset (Fin 3)}

set_option maxHeartbeats 1600000 in
-- the final `field_simp`/`ring` closes a rational identity with three symbolic
-- denominators; it needs more heartbeats than the default limit
/-- **Mathlib's nine-point center maps to `N` in the model.** -/
theorem Φ_ninePointCenter (hE : t.ExcenterExists signs) (hr : 0 < t.exradius signs) :
    Φ (V := V) (t.excenter signs) (t.exradius signs) t.ninePointCircle.center
      = N (τ (V := V) t signs 0) (τ (V := V) t signs 1) (τ (V := V) t signs 2) := by
  set c := t.excenter signs
  set r := t.exradius signs
  set τ₀ := τ (V := V) t signs 0
  set τ₁ := τ (V := V) t signs 1
  set τ₂ := τ (V := V) t signs 2
  obtain ⟨h01, h12, h20⟩ := τ_add_ne (V := V) hE hr
  have hPτ := P_τ_ne (V := V) hE hr
  have hv0 : Φ (V := V) c r (t.points 0) = 2 * τ₁ * τ₂ / (τ₁ + τ₂) :=
    Φ_vertex_eq t signs hE hr (by decide) (by decide) (by decide)
  have hv1 : Φ (V := V) c r (t.points 1) = 2 * τ₂ * τ₀ / (τ₂ + τ₀) :=
    Φ_vertex_eq t signs hE hr (by decide) (by decide) (by decide)
  have hv2 : Φ (V := V) c r (t.points 2) = 2 * τ₀ * τ₁ / (τ₀ + τ₁) :=
    Φ_vertex_eq t signs hE hr (by decide) (by decide) (by decide)
  -- fold the hypotheses into the abbreviations, so `field_simp`/`ring` can see them
  have h01' : τ₀ + τ₁ ≠ 0 := h01
  have h12' : τ₁ + τ₂ ≠ 0 := h12
  have h20' : τ₂ + τ₀ ≠ 0 := h20
  have hPτ' : FeuerbachCore.P τ₀ τ₁ τ₂ ≠ 0 := hPτ
  have hOc : Φ (V := V) c r t.circumcenter = O τ₀ τ₁ τ₂ :=
    Φ_circumcenter (V := V) hE hr
  -- mathlib's formula for the nine-point center (definitional)
  have hcen : t.ninePointCircle.center
      = ((3 : ℝ) / 2) • (Finset.univ.centroid ℝ t.points -ᵥ t.circumcenter)
          +ᵥ t.circumcenter := by
    rw [Simplex.ninePointCircle_center]
    norm_num
  rw [hcen, Φ_smul_vadd, mul_div_assoc, Φ_vsub_div (V := V) c r, Φ_centroid, hOc,
    hv0, hv1, hv2]
  rw [← N_eq_sum h01' (by rwa [add_comm] at h20') h12' hPτ']
  push_cast
  field_simp
  ring

/-- **The circumradius transports through Φ**: it equals `r · ‖Φ(p₀) − O_modello‖`. -/
theorem circumradius_eq (hE : t.ExcenterExists signs) (hr : 0 < t.exradius signs) :
    t.circumradius = t.exradius signs
      * ‖Φ (V := V) (t.excenter signs) (t.exradius signs) (t.points 0)
          - O (τ (V := V) t signs 0) (τ (V := V) t signs 1) (τ (V := V) t signs 2)‖ := by
  rw [← t.dist_circumcenter_eq_circumradius 0,
    dist_eq_r_mul (t.excenter signs) hr, dist_eq_norm, Φ_circumcenter (V := V) hE hr]

/-- **FEUERBACH'S THEOREM** (unified form over the four circles).

For every triangle in a real Euclidean plane and every choice of `signs` for
which the incircle/excircle exists with positive radius, the nine-point circle
and that circle are **tangent**: internally (in one direction or the other) or
externally. With `signs = ∅` this is tangency to the incircle; with
`signs = {i}` to the excircles: by `excenter_eq_incenter_or_excenter_singleton`,
these instances exhaust Feuerbach's theorem. -/
theorem feuerbach (hE : t.ExcenterExists signs) (hr : 0 < t.exradius signs) :
    (t.exsphere signs).IsIntTangent t.ninePointCircle
      ∨ t.ninePointCircle.IsIntTangent (t.exsphere signs)
      ∨ (t.exsphere signs).IsExtTangent t.ninePointCircle := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos
    (R := ℝ) (by rw [Fact.out (p := finrank ℝ V = 2)]; norm_num)
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
  have hz0 : τ₀ ≠ 0 := by intro h; rw [h] at hn0; simp at hn0
  have hz1 : τ₁ ≠ 0 := by intro h; rw [h] at hn1; simp at hn1
  have hz2 : τ₂ ≠ 0 := by intro h; rw [h] at hn2; simp at hn2
  -- `w` is a real number `W`
  obtain ⟨W, hW⟩ := Complex.conj_eq_iff_real.mp (conj_w hn0 hn1 hn2 hPτ)
  -- the distance between the centers, in the model: ‖N‖ = |W + 1|
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
  -- the model's circumradius: ‖Φp₀ − O‖ = 2|W|
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
      have : (4 : ℂ) * (e₃ τ₀ τ₁ τ₂) ^ 2 / (FeuerbachCore.P τ₀ τ₁ τ₂) ^ 2
          = (2 * w τ₀ τ₁ τ₂) ^ 2 := by
        unfold w
        field_simp
        ring
      rw [this, hW]; push_cast; ring
    have h2 : Complex.normSq (Φ (V := V) c r (t.points 0) - Om) = 4 * W ^ 2 := by
      have h1 : (Complex.normSq (Φ (V := V) c r (t.points 0) - Om) : ℂ)
          = (((4 * W ^ 2 : ℝ)) : ℂ) := by
        rw [← Complex.mul_conj, hd0, hw2]
      exact_mod_cast h1
    rw [← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq, h2]
    rw [show (4 : ℝ) * W ^ 2 = (2 * |W|) ^ 2 by rw [mul_pow]; rw [sq_abs]; norm_num,
      Real.sqrt_sq (by positivity)]
  -- distance between the centers and the nine-point radius, transported
  -- (the explicit types force the definitional folding of the abbreviations)
  have hNP : Φ (V := V) c r t.ninePointCircle.center = N τ₀ τ₁ τ₂ :=
    Φ_ninePointCenter (V := V) hE hr
  have hCR : t.circumradius = r * ‖Φ (V := V) c r (t.points 0) - Om‖ :=
    circumradius_eq (V := V) hE hr
  have hdist : dist (t.exsphere signs).center t.ninePointCircle.center
      = r * |W + 1| := by
    have h1 : dist c t.ninePointCircle.center = r * |W + 1| := by
      rw [dist_eq_r_mul (V := V) c hr, Φ_center, hNP, dist_zero_left, hnormN]
    simpa [Simplex.exsphere_center] using h1
  have hrad : t.ninePointCircle.radius = r * |W| := by
    rw [Simplex.ninePointCircle_radius, hCR, hnormV]
    push_cast
    ring
  have hex_r : (t.exsphere signs).radius = r := Simplex.exsphere_radius t signs
  have h9r : 0 ≤ t.ninePointCircle.radius := by rw [hrad]; positivity
  -- the trichotomy on the sign of W
  by_cases hW1 : W + 1 ≤ 0
  · -- W ≤ −1: internal tangency, nine-point circle outside
    left
    rw [Sphere.isIntTangent_iff_dist_center]
    refine ⟨?_, by rw [hex_r]; exact hr.le, h9r⟩
    rw [hdist, hrad, hex_r, abs_of_nonpos hW1, abs_of_nonpos (by linarith)]
    ring
  · push_neg at hW1
    by_cases hW0 : W < 0
    · -- −1 < W < 0: internal tangency, nine-point circle inside
      right; left
      rw [Sphere.isIntTangent_iff_dist_center]
      refine ⟨?_, h9r, by rw [hex_r]; exact hr.le⟩
      rw [dist_comm, hdist, hrad, hex_r, abs_of_pos (by linarith), abs_of_neg hW0]
      ring
    · -- W ≥ 0: external tangency
      push_neg at hW0
      right; right
      rw [Sphere.isExtTangent_iff_dist_center]
      refine ⟨?_, by rw [hex_r]; exact hr.le, h9r⟩
      rw [hdist, hrad, hex_r, abs_of_nonneg (by linarith), abs_of_nonneg hW0]
      ring

/-- **Feuerbach, unconditional.** For EVERY triangle in the Euclidean plane and
EVERY choice of `signs`, the incircle/excircle and the nine-point circle are
tangent. The existence conditions are derived internally: mathlib guarantees
that for a triangle every excenter exists (`excenterExists`) with positive
radius (`exradius_pos`). -/
theorem feuerbach_of_triangle (t : Triangle ℝ P) (signs : Finset (Fin 3)) :
    (t.exsphere signs).IsIntTangent t.ninePointCircle
      ∨ t.ninePointCircle.IsIntTangent (t.exsphere signs)
      ∨ (t.exsphere signs).IsExtTangent t.ninePointCircle :=
  feuerbach (t.excenterExists signs) (t.excenterExists signs).exradius_pos

end FeuerbachFinal3
