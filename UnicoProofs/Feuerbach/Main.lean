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
import UnicoProofs.Feuerbach.NinePointCenter
import UnicoProofs.Feuerbach.Barycentric
import UnicoProofs.Feuerbach.MetricLemmas

/-!
# Feuerbach's theorem: the two classical statements

* `feuerbach_insphere`: the nine-point circle is tangent INTERNALLY to the
  incircle;
* `feuerbach_exsphere`: and EXTERNALLY to each of the three excircles.

The chain of reasoning: the barycentric weights of the incenter/excenter
(mathlib) transport under Φ to the equation of the normalized vertices; the
barycentric certificates give the sign of the parameter `W`; the extracted
metric lemmas convert that sign into tangency.
-/

namespace FeuerbachMain

open EuclideanGeometry Affine Module
open FeuerbachCore FeuerbachMap FeuerbachWeld FeuerbachAssembly
open FeuerbachFinal1 FeuerbachFinal2 FeuerbachFinal3
open FeuerbachBarycentric FeuerbachWeld2

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

variable {t : Triangle ℝ P} {signs : Finset (Fin 3)}

/-- **The sign of the parameter, from the sign of the weights**: the core shared
by both theorems. Given the mathlib hypotheses (existence, positive radius) and
the real parameter `W`, it produces the two barycentric certificate identities. -/
theorem barycentric_certificates (hE : t.ExcenterExists signs)
    (hr : 0 < t.exradius signs) {W : ℝ}
    (hW : w (τ (V := V) t signs 0) (τ (V := V) t signs 1) (τ (V := V) t signs 2)
      = (W : ℂ)) :
    W * (t.excenterWeights signs 0 * t.excenterWeights signs 1
        * t.excenterWeights signs 2)
      * (Complex.normSq (τ (V := V) t signs 0 - τ (V := V) t signs 1)
        * Complex.normSq (τ (V := V) t signs 0 - τ (V := V) t signs 2)
        * Complex.normSq (τ (V := V) t signs 1 - τ (V := V) t signs 2)) = -1
    ∧ W * (Complex.normSq (τ (V := V) t signs 0 + τ (V := V) t signs 1
        + τ (V := V) t signs 2) - 1) = 1 := by
  classical
  set c := t.excenter signs
  set r := t.exradius signs
  set τ₀ := τ (V := V) t signs 0
  set τ₁ := τ (V := V) t signs 1
  set τ₂ := τ (V := V) t signs 2
  obtain ⟨h01, h12, h20⟩ := τ_add_ne (V := V) hE hr
  have h01' : τ₀ + τ₁ ≠ 0 := h01
  have h12' : τ₁ + τ₂ ≠ 0 := h12
  have h20' : τ₂ + τ₀ ≠ 0 := h20
  have hPτ := P_τ_ne (V := V) hE hr
  have hPτ' : FeuerbachCore.P τ₀ τ₁ τ₂ ≠ 0 := hPτ
  have hn0 : ‖τ₀‖ = 1 := norm_Φ_touchpoint_eq_one t signs hE hr 0
  have hn1 : ‖τ₁‖ = 1 := norm_Φ_touchpoint_eq_one t signs hE hr 1
  have hn2 : ‖τ₂‖ = 1 := norm_Φ_touchpoint_eq_one t signs hE hr 2
  have hv0 : Φ (V := V) c r (t.points 0) = 2 * τ₁ * τ₂ / (τ₁ + τ₂) :=
    Φ_vertex_eq t signs hE hr (by decide) (by decide) (by decide)
  have hv1 : Φ (V := V) c r (t.points 1) = 2 * τ₂ * τ₀ / (τ₂ + τ₀) :=
    Φ_vertex_eq t signs hE hr (by decide) (by decide) (by decide)
  have hv2 : Φ (V := V) c r (t.points 2) = 2 * τ₀ * τ₁ / (τ₀ + τ₁) :=
    Φ_vertex_eq t signs hE hr (by decide) (by decide) (by decide)
  -- mathlib's weights
  set l0 := t.excenterWeights signs 0
  set l1 := t.excenterWeights signs 1
  set l2 := t.excenterWeights signs 2
  have hlam : ∑ i, t.excenterWeights signs i = 1 := by
    rw [Simplex.sum_excenterWeights_eq_one_iff]
    exact hE
  have hsum : (l0 : ℂ) + l1 + l2 = 1 := by
    have := hlam
    rw [Fin.sum_univ_three] at this
    exact_mod_cast congrArg (Complex.ofReal) this
  -- the vertex equation: 0 = Σ λᵢ · Vᵢ
  have hzero : (l0 : ℂ) * Φ (V := V) c r (t.points 0)
      + (l1 : ℂ) * Φ (V := V) c r (t.points 1)
      + (l2 : ℂ) * Φ (V := V) c r (t.points 2) = 0 := by
    have h := Φ_affineCombination (V := V) c r t.points (t.excenterWeights signs) hlam
    rw [← Simplex.excenter_eq_affineCombination] at h
    rw [Fin.sum_univ_three] at h
    have hc : Φ (V := V) c r (t.excenter signs) = 0 := Φ_center c r
    rw [hc] at h
    linear_combination -h
  rw [hv0, hv1, hv2] at hzero
  -- the polynomial forms (denominators cleared) with (a,b,c) := (τ₀,τ₁,τ₂)
  have hE2 : (l0 : ℂ) * (2 * τ₁ * τ₂) * ((τ₂ + τ₀) * (τ₀ + τ₁))
      + (l1 : ℂ) * (2 * τ₂ * τ₀) * ((τ₁ + τ₂) * (τ₀ + τ₁))
      + (l2 : ℂ) * (2 * τ₀ * τ₁) * ((τ₁ + τ₂) * (τ₂ + τ₀)) = 0 := by
    field_simp at hzero
    linear_combination hzero
  -- the conjugate: the λ are real, the vertices conjugate via `conj_vertex`
  have hzero_c : (l0 : ℂ) * (2 / (τ₁ + τ₂))
      + (l1 : ℂ) * (2 / (τ₂ + τ₀))
      + (l2 : ℂ) * (2 / (τ₀ + τ₁)) = 0 := by
    have h := congrArg (starRingEnd ℂ) hzero
    rw [map_add, map_add, map_mul, map_mul, map_mul, map_zero,
      Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_ofReal,
      conj_vertex hn1 hn2 h12', conj_vertex hn2 hn0 h20',
      conj_vertex hn0 hn1 h01'] at h
    exact h
  have hE3 : (l0 : ℂ) * 2 * ((τ₂ + τ₀) * (τ₀ + τ₁))
      + (l1 : ℂ) * 2 * ((τ₁ + τ₂) * (τ₀ + τ₁))
      + (l2 : ℂ) * 2 * ((τ₁ + τ₂) * (τ₂ + τ₀)) = 0 := by
    field_simp at hzero_c
    linear_combination hzero_c
  -- the certificates
  have hprod := lambda_prod (a := τ₀) (b := τ₁) (c := τ₂) hsum hE2 hE3 h01'
    (by rwa [add_comm] at h20') h12'
  exact ⟨W_mul_prod hn0 hn1 hn2 hPτ' hW hprod,
    W_mul_normSq_sub_one hn0 hn1 hn2 hPτ' hW⟩

/-- **FEUERBACH'S THEOREM, internal part.** The nine-point circle of every
triangle in the Euclidean plane is tangent internally to the incircle. -/
theorem feuerbach_insphere (t : Triangle ℝ P) :
    t.insphere.IsIntTangent t.ninePointCircle := by
  classical
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos
    (R := ℝ) (by rw [Fact.out (p := finrank ℝ V = 2)]; norm_num)
  have hE : t.ExcenterExists (∅ : Finset (Fin 3)) := t.excenterExists ∅
  have hr : 0 < t.exradius ∅ := hE.exradius_pos
  set c := t.excenter (∅ : Finset (Fin 3))
  set r := t.exradius (∅ : Finset (Fin 3))
  set τ₀ := τ (V := V) t ∅ 0
  set τ₁ := τ (V := V) t ∅ 1
  set τ₂ := τ (V := V) t ∅ 2
  have hPτ := P_τ_ne (V := V) hE hr
  have hn0 : ‖τ₀‖ = 1 := norm_Φ_touchpoint_eq_one t ∅ hE hr 0
  have hn1 : ‖τ₁‖ = 1 := norm_Φ_touchpoint_eq_one t ∅ hE hr 1
  have hn2 : ‖τ₂‖ = 1 := norm_Φ_touchpoint_eq_one t ∅ hE hr 2
  obtain ⟨W, hW⟩ := Complex.conj_eq_iff_real.mp (conj_w hn0 hn1 hn2 hPτ)
  obtain ⟨hA, hB⟩ := barycentric_certificates (V := V) hE hr hW
  -- the incenter's weights are all positive
  have h0 : 0 < t.excenterWeights ∅ 0 := t.excenterWeights_empty_pos 0
  have h1 : 0 < t.excenterWeights ∅ 1 := t.excenterWeights_empty_pos 1
  have h2 : 0 < t.excenterWeights ∅ 2 := t.excenterWeights_empty_pos 2
  -- the normalized touchpoints are distinct
  have hne : ∀ {i j : Fin 3}, i ≠ j → τ (V := V) t ∅ i ≠ τ (V := V) t ∅ j := by
    intro i j hij
    exact (Φ_injective (V := V) c hr).ne (touchpoint_ne t ∅ hE hr hij)
  have hn01 : 0 < Complex.normSq (τ₀ - τ₁) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr (hne (by decide)))
  have hn02 : 0 < Complex.normSq (τ₀ - τ₂) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr (hne (by decide)))
  have hn12 : 0 < Complex.normSq (τ₁ - τ₂) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr (hne (by decide)))
  -- THE SIGN: W ≤ −1
  have hWle : W ≤ -1 := W_le_neg_one_of_pos_weights hA hB h0 h1 h2 hn01 hn02 hn12
  -- the internal tangency
  have hdist := dist_excenter_ninePointCenter (V := V) hE hr hW
  have hrad := ninePointRadius_eq (V := V) hE hr hW
  have hins : t.insphere = t.exsphere (∅ : Finset (Fin 3)) := rfl
  rw [hins, Sphere.isIntTangent_iff_dist_center]
  refine ⟨?_, ?_, ?_⟩
  · rw [hdist, hrad, Simplex.exsphere_radius]
    rw [abs_of_nonpos (by linarith : W + 1 ≤ 0), abs_of_nonpos (by linarith : W ≤ 0)]
    ring
  · rw [Simplex.exsphere_radius]; exact hr.le
  · rw [hrad]; positivity

/-- **FEUERBACH'S THEOREM, external part.** The nine-point circle of every
triangle in the Euclidean plane is tangent externally to each of the three
excircles. -/
theorem feuerbach_exsphere (t : Triangle ℝ P) (i : Fin 3) :
    (t.exsphere {i}).IsExtTangent t.ninePointCircle := by
  classical
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos
    (R := ℝ) (by rw [Fact.out (p := finrank ℝ V = 2)]; norm_num)
  have hE : t.ExcenterExists ({i} : Finset (Fin 3)) := t.excenterExists {i}
  have hr : 0 < t.exradius {i} := hE.exradius_pos
  set c := t.excenter ({i} : Finset (Fin 3))
  set r := t.exradius ({i} : Finset (Fin 3))
  set τ₀ := τ (V := V) t {i} 0
  set τ₁ := τ (V := V) t {i} 1
  set τ₂ := τ (V := V) t {i} 2
  have hPτ := P_τ_ne (V := V) hE hr
  have hn0 : ‖τ₀‖ = 1 := norm_Φ_touchpoint_eq_one t {i} hE hr 0
  have hn1 : ‖τ₁‖ = 1 := norm_Φ_touchpoint_eq_one t {i} hE hr 1
  have hn2 : ‖τ₂‖ = 1 := norm_Φ_touchpoint_eq_one t {i} hE hr 2
  obtain ⟨W, hW⟩ := Complex.conj_eq_iff_real.mp (conj_w hn0 hn1 hn2 hPτ)
  obtain ⟨hA, hB⟩ := barycentric_certificates (V := V) hE hr hW
  have hC := nine_sub_normSq hn0 hn1 hn2
  -- the excenter's weights: the one at index `i` is negative, the others positive
  have hwneg : t.excenterWeights {i} i < 0 := by
    have hs := t.sign_excenterWeights_singleton_neg i
    have := sign_eq_neg_one_iff.mp hs
    exact this
  have hwpos : ∀ {j : Fin 3}, i ≠ j → 0 < t.excenterWeights {i} j := by
    intro j hij
    have hs := t.sign_excenterWeights_singleton_pos hij
    exact sign_eq_one_iff.mp hs
  have hneg : t.excenterWeights {i} 0 * t.excenterWeights {i} 1
      * t.excenterWeights {i} 2 < 0 := by
    fin_cases i
    · exact mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos hwneg (hwpos (by decide)))
        (hwpos (by decide))
    · exact mul_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (hwpos (by decide)) hwneg)
        (hwpos (by decide))
    · exact mul_neg_of_pos_of_neg
        (mul_pos (hwpos (by decide)) (hwpos (by decide))) hwneg
  -- the normalized touchpoints are distinct
  have hne : ∀ {j k : Fin 3}, j ≠ k → τ (V := V) t {i} j ≠ τ (V := V) t {i} k := by
    intro j k hjk
    exact (Φ_injective (V := V) c hr).ne (touchpoint_ne t {i} hE hr hjk)
  have hn01 : 0 < Complex.normSq (τ₀ - τ₁) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr (hne (by decide)))
  have hn02 : 0 < Complex.normSq (τ₀ - τ₂) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr (hne (by decide)))
  have hn12 : 0 < Complex.normSq (τ₁ - τ₂) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr (hne (by decide)))
  -- THE SIGN: W > 1/8 > 0
  have hWgt : 1 / 8 < W := W_gt_eighth_of_neg_weights hA hB hC hneg hn01 hn02 hn12
  -- the external tangency
  have hdist := dist_excenter_ninePointCenter (V := V) hE hr hW
  have hrad := ninePointRadius_eq (V := V) hE hr hW
  rw [Sphere.isExtTangent_iff_dist_center]
  refine ⟨?_, ?_, ?_⟩
  · rw [hdist, hrad, Simplex.exsphere_radius]
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ W + 1), abs_of_nonneg (by linarith : (0:ℝ) ≤ W)]
    ring
  · rw [Simplex.exsphere_radius]; exact hr.le
  · rw [hrad]; positivity

end FeuerbachMain
