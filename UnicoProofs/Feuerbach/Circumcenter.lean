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

/-!
# Identifying mathlib's circumcenter in the model

* `conj_vertex` / `conj_O` / `conj_w`: conjugates of the model's closed forms
* `norm_eq_of_mul_conj_eq`: equal norms from equal products with the conjugate
* `vertex_sub_O_mul_conj`: the conjugate-squared vertex-to-circumcenter distance
  in the model
* `τ`, `τ_add_ne`, `P_τ_ne`: the normalized touchpoints and their basic
  non-vanishing facts
* `Φ_circumcenter`: **mathlib's circumcenter maps to the model's circumcenter**
-/

namespace FeuerbachFinal2

open EuclideanGeometry Affine Module
open FeuerbachCore FeuerbachMap FeuerbachWeld FeuerbachAssembly FeuerbachFinal1

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

/-- The conjugate of the model's vertex: `conj (2ab/(a+b)) = 2/(a+b)`. -/
theorem conj_vertex {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a + b ≠ 0) :
    (starRingEnd ℂ) (2 * a * b / (a + b)) = 2 / (a + b) := by
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := by intro h; rw [h] at hb; simp at hb
  have hinv : a⁻¹ + b⁻¹ = (a + b) / (a * b) := by field_simp; ring
  rw [map_div₀, map_mul, map_mul, map_add, conj_eq_inv ha, conj_eq_inv hb,
    map_ofNat, hinv]
  field_simp

/-- The conjugate of `O` in the model: `conj (O a b c) = O a⁻¹ b⁻¹ c⁻¹`. -/
theorem conj_O {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    (starRingEnd ℂ) (O a b c) = O a⁻¹ b⁻¹ c⁻¹ := by
  unfold O e₃ e₁ FeuerbachCore.P
  simp only [map_div₀, map_mul, map_add, map_ofNat, conj_eq_inv ha, conj_eq_inv hb,
    conj_eq_inv hc]

/-- The conjugate of `w` in the concrete model (`τ` of norm 1): `conj w = w`. -/
theorem conj_w {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hP : FeuerbachCore.P a b c ≠ 0) :
    (starRingEnd ℂ) (w a b c) = w a b c := by
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := by intro h; rw [h] at hb; simp at hb
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
  have h1 : (starRingEnd ℂ) (w a b c) = w a⁻¹ b⁻¹ c⁻¹ := by
    unfold w e₃ FeuerbachCore.P
    simp only [map_div₀, map_mul, map_add, conj_eq_inv ha, conj_eq_inv hb, conj_eq_inv hc]
  rw [h1]
  exact w_inv ha0 hb0 hc0 hP

section TheEnd

variable (t : Triangle ℝ P) (signs : Finset (Fin 3))

/-- Equality of norms from equality of the products with the conjugate. -/
theorem norm_eq_of_mul_conj_eq {z z' : ℂ}
    (h : z * (starRingEnd ℂ) z = z' * (starRingEnd ℂ) z') : ‖z‖ = ‖z'‖ := by
  have h2 : Complex.normSq z = Complex.normSq z' := by
    have h1 : (Complex.normSq z : ℂ) = (Complex.normSq z' : ℂ) := by
      rw [← Complex.mul_conj, ← Complex.mul_conj]; exact h
    exact_mod_cast h1
  rw [← Real.sqrt_sq (norm_nonneg z), ← Real.sqrt_sq (norm_nonneg z'),
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, h2]

/-- **The conjugate-square of the vertex-to-circumcenter distance in the model**,
as a function of the three normalized touchpoints (case of the first vertex;
the others follow by rotating the arguments). -/
theorem vertex_sub_O_mul_conj {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hP : FeuerbachCore.P a b c ≠ 0) (hbc : b + c ≠ 0) :
    (2 * b * c / (b + c) - O a b c)
        * (starRingEnd ℂ) (2 * b * c / (b + c) - O a b c)
      = 4 * (e₃ a b c) ^ 2 / (FeuerbachCore.P a b c) ^ 2 := by
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := by intro h; rw [h] at hb; simp at hb
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
  rw [map_sub, conj_vertex hb hc hbc, conj_O ha hb hc]
  exact normSq_vertex_sub_O ha0 hb0 hc0 hP hbc

/-- The normalized touchpoints, as a function of the index. -/
noncomputable def τ (i : Fin 3) : ℂ :=
  Φ (V := V) (t.excenter signs) (t.exradius signs) (t.touchpoint signs i)

variable {t signs}

/-- The pairwise sums of the normalized touchpoints are nonzero. -/
theorem τ_add_ne (hE : t.ExcenterExists signs) (hr : 0 < t.exradius signs) :
    (τ (V := V) t signs 0 + τ (V := V) t signs 1 ≠ 0)
      ∧ (τ (V := V) t signs 1 + τ (V := V) t signs 2 ≠ 0)
      ∧ (τ (V := V) t signs 2 + τ (V := V) t signs 0 ≠ 0) :=
  ⟨Φ_touchpoint_add_ne_zero t signs hE hr (i := 2) (by decide) (by decide),
   Φ_touchpoint_add_ne_zero t signs hE hr (i := 0) (by decide) (by decide),
   Φ_touchpoint_add_ne_zero t signs hE hr (i := 1) (by decide) (by decide)⟩

/-- The model's denominator is nonzero on the normalized touchpoints. -/
theorem P_τ_ne (hE : t.ExcenterExists signs) (hr : 0 < t.exradius signs) :
    FeuerbachCore.P (τ (V := V) t signs 0) (τ (V := V) t signs 1)
      (τ (V := V) t signs 2) ≠ 0 := by
  obtain ⟨h01, h12, h20⟩ := τ_add_ne (V := V) hE hr
  unfold FeuerbachCore.P
  exact mul_ne_zero (mul_ne_zero h01 (by rwa [add_comm] at h20)) h12

/-- **Mathlib's circumcenter maps to the model's circumcenter.** -/
theorem Φ_circumcenter (hE : t.ExcenterExists signs) (hr : 0 < t.exradius signs) :
    Φ (V := V) (t.excenter signs) (t.exradius signs) t.circumcenter
      = O (τ (V := V) t signs 0) (τ (V := V) t signs 1) (τ (V := V) t signs 2) := by
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
  -- the three normalized vertices, by uniqueness of the intersection of tangents
  have hv0 : Φ (V := V) c r (t.points 0) = 2 * τ₁ * τ₂ / (τ₁ + τ₂) :=
    Φ_vertex_eq t signs hE hr (i := 0) (j := 1) (k := 2)
      (by decide) (by decide) (by decide)
  have hv1 : Φ (V := V) c r (t.points 1) = 2 * τ₂ * τ₀ / (τ₂ + τ₀) :=
    Φ_vertex_eq t signs hE hr (i := 1) (j := 2) (k := 0)
      (by decide) (by decide) (by decide)
  have hv2 : Φ (V := V) c r (t.points 2) = 2 * τ₀ * τ₁ / (τ₀ + τ₁) :=
    Φ_vertex_eq t signs hE hr (i := 2) (j := 0) (k := 1)
      (by decide) (by decide) (by decide)
  -- the candidate: the preimage of the model's circumcenter
  set Q : P := Φinv (V := V) c r Om with hQ
  have hΦQ : Φ (V := V) c r Q = Om := Φ_Φinv c hr Om
  -- the three distances from the vertices coincide
  have key : ∀ i : Fin 3, ‖Φ (V := V) c r (t.points i) - Om‖
      = ‖Φ (V := V) c r (t.points 0) - Om‖ := by
    intro i
    fin_cases i
    · rfl
    · -- vertex 1: rotated model (τ₁, τ₂, τ₀)
      show ‖Φ (V := V) c r (t.points 1) - Om‖ = ‖Φ (V := V) c r (t.points 0) - Om‖
      refine norm_eq_of_mul_conj_eq ?_
      rw [hv1, hv0]
      have e1 := vertex_sub_O_mul_conj hn1 hn2 hn0
        (by rw [P_rotate]; exact hPτ) h20
      have e0 := vertex_sub_O_mul_conj hn0 hn1 hn2 hPτ h12
      rw [O_rotate, ← hOm] at e1
      rw [← hOm] at e0
      rw [e1, e0, e₃_rotate, P_rotate]
    · -- vertex 2: model rotated twice (τ₂, τ₀, τ₁)
      show ‖Φ (V := V) c r (t.points 2) - Om‖ = ‖Φ (V := V) c r (t.points 0) - Om‖
      refine norm_eq_of_mul_conj_eq ?_
      rw [hv2, hv0]
      have e2 := vertex_sub_O_mul_conj hn2 hn0 hn1
        (by rw [P_rotate, P_rotate]; exact hPτ) h01
      have e0 := vertex_sub_O_mul_conj hn0 hn1 hn2 hPτ h12
      rw [O_rotate, O_rotate, ← hOm] at e2
      rw [← hOm] at e0
      rw [e2, e0, e₃_rotate, e₃_rotate, P_rotate, P_rotate]
  -- hence Q is equidistant from the three vertices
  have hdist : ∀ i : Fin 3, dist (t.points i) Q
      = r * ‖Φ (V := V) c r (t.points 0) - Om‖ := by
    intro i
    rw [dist_eq_r_mul c hr, hΦQ, dist_eq_norm, key i]
  -- and it lies in the plane (the span of the triangle is everything)
  have hspan : Q ∈ affineSpan ℝ (Set.range t.points) := by
    have htop : affineSpan ℝ (Set.range t.points) = ⊤ :=
      t.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.2
        (by simp [Fact.out (p := finrank ℝ V = 2)])
    rw [htop]; trivial
  -- uniqueness of the circumcenter
  have hQc : Q = t.circumcenter := t.eq_circumcenter_of_dist_eq hspan hdist
  rw [← hQc, hΦQ]

end TheEnd

end FeuerbachFinal2
