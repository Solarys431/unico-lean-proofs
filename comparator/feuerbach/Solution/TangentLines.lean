/-
Copyright (c) 2026 Daniele Cappello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Cappello

Part of a Lean formalization of Feuerbach's theorem, produced by the
UNICO/NOUS autonomous certification pipeline (Claude, by Anthropic).
Every step is kernel-checked.
-/

import Mathlib

/-! # Tangent lines to the unit circle in complex form

The foundational building block: if `t` lies on the unit circle, the tangent line
at `t` is the set of points `z` with `z + t²·conj z = 2t`. Two tangent lines (at
`t₂` and `t₃`, non-antipodal) meet at the unique point `2·t₂·t₃/(t₂+t₃)`.

This is the formula that the algebraic core assumes; here we prove it.
-/

namespace FeuerbachBridge

open Complex

/-- **The tangent line to the unit circle at `t`**, in complex form: for
`‖t‖ = 1` the condition `z + t²·conj z = 2t` characterizes the tangent line at `t`
(equivalent to `Re(conj t · (z − t)) = 0`, orthogonality to the radius). This
development uses and proves the direction "orthogonality ⟹ onTangent"
(`onTangent_of_inner_eq_zero`); the other direction is not needed by the chain. -/
def onTangent (t z : ℂ) : Prop := z + t ^ 2 * (starRingEnd ℂ) z = 2 * t

/-- **The link with mathlib.** Tangency in mathlib is "the radius is orthogonal to
the line": a vanishing inner product. This lemma translates that condition into
our scalar equation `onTangent`.

This is the bridge between the library's abstract language (inner product spaces,
affine subspaces) and concrete computation on the complex plane. -/
theorem onTangent_of_inner_eq_zero {t z : ℂ} (ht : ‖t‖ = 1)
    (hinner : inner ℝ (z - t) t = (0 : ℝ)) :
    onTangent t z := by
  -- `|t| = 1` means `t · conj t = 1`
  have htt : t * (starRingEnd ℂ) t = 1 := by
    rw [Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, ht]
    norm_num
  -- mathlib's convention: ⟪w, z⟫_ℝ = (z · conj w).re
  have hre : (t * (starRingEnd ℂ) (z - t)).re = 0 := by
    rw [Complex.inner] at hinner
    exact hinner
  -- setting u = t·conj(z−t), the hypothesis says Re u = 0, i.e. u + conj u = 0
  set u : ℂ := t * (starRingEnd ℂ) (z - t) with hu_def
  -- `z + conj z = 2·Re z`, and here the real part vanishes
  have hu : u + (starRingEnd ℂ) u = 0 := by
    rw [Complex.add_conj, hre]
    simp
  -- and the tangent equation is exactly t·(u + conj u + 2) = 2t
  have halg : z + t ^ 2 * (starRingEnd ℂ) z = t * (u + (starRingEnd ℂ) u + 2) := by
    rw [hu_def]
    simp only [map_mul, map_sub, Complex.conj_conj]
    linear_combination (2 * t - z) * htt
  unfold onTangent
  rw [halg, hu]
  ring

/-- The touchpoint lies on its own tangent line. -/
theorem onTangent_self {t : ℂ} (ht : ‖t‖ = 1) : onTangent t t := by
  have h : (starRingEnd ℂ) t = t⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, ht]
    simp
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0] at ht; simp at ht
  unfold onTangent
  rw [h]
  field_simp
  ring

/-- **The vertex as the intersection of two tangent lines.** If `t₂, t₃` lie on
the unit circle and are not antipodal (`t₂ + t₃ ≠ 0`), then `A = 2·t₂·t₃/(t₂+t₃)`
lies on both tangent lines. This is the formula used by the algebraic core. -/
theorem vertex_onTangent {t₂ t₃ : ℂ} (h₂ : ‖t₂‖ = 1) (h₃ : ‖t₃‖ = 1)
    (hsum : t₂ + t₃ ≠ 0) :
    onTangent t₂ (2 * t₂ * t₃ / (t₂ + t₃)) ∧ onTangent t₃ (2 * t₂ * t₃ / (t₂ + t₃)) := by
  have ht₂0 : t₂ ≠ 0 := by intro h0; rw [h0] at h₂; simp at h₂
  have ht₃0 : t₃ ≠ 0 := by intro h0; rw [h0] at h₃; simp at h₃
  have c₂ : (starRingEnd ℂ) t₂ = t₂⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h₂]; simp
  have c₃ : (starRingEnd ℂ) t₃ = t₃⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h₃]; simp
  -- the sum of the inverses, as a single fraction
  have hinv : t₂⁻¹ + t₃⁻¹ = (t₂ + t₃) / (t₂ * t₃) := by field_simp; ring
  have hinv0 : t₂⁻¹ + t₃⁻¹ ≠ 0 := by
    rw [hinv]; exact div_ne_zero hsum (mul_ne_zero ht₂0 ht₃0)
  -- the conjugate of the vertex: conj A = 2/(t₂+t₃)
  have hconj : (starRingEnd ℂ) (2 * t₂ * t₃ / (t₂ + t₃)) = 2 / (t₂ + t₃) := by
    rw [map_div₀, map_mul, map_mul, map_add, c₂, c₃, map_ofNat, hinv]
    field_simp
  constructor <;> · unfold onTangent; rw [hconj]; field_simp; try ring

/-- **Uniqueness of the intersection**: two non-parallel tangent lines meet at a
single point. This is used to identify the vertex unambiguously. -/
theorem tangent_inter_unique {t₂ t₃ z : ℂ} (h₂ : ‖t₂‖ = 1) (h₃ : ‖t₃‖ = 1)
    (hne : t₂ ≠ t₃) (hsum : t₂ + t₃ ≠ 0)
    (hz₂ : onTangent t₂ z) (hz₃ : onTangent t₃ z) :
    z = 2 * t₂ * t₃ / (t₂ + t₃) := by
  unfold onTangent at hz₂ hz₃
  -- subtracting: (t₂² − t₃²)·conj z = 2(t₂ − t₃), and t₂² − t₃² = (t₂−t₃)(t₂+t₃) ≠ 0
  have hsub : (t₂ ^ 2 - t₃ ^ 2) * (starRingEnd ℂ) z = 2 * (t₂ - t₃) := by
    linear_combination hz₂ - hz₃
  have hfac : t₂ ^ 2 - t₃ ^ 2 = (t₂ - t₃) * (t₂ + t₃) := by ring
  have hd : t₂ - t₃ ≠ 0 := sub_ne_zero.mpr hne
  have hconj : (starRingEnd ℂ) z = 2 / (t₂ + t₃) := by
    rw [hfac] at hsub
    field_simp at hsub ⊢
    linear_combination hsub
  -- substituting conj z into the first equation
  rw [hconj] at hz₂
  field_simp at hz₂ ⊢
  linear_combination hz₂


/-- **Antipodality is excluded for free.** If a point lies on two tangent lines at
antipodal points (`t` and `−t`), the two equations sum to `t = 0`: absurd on the
unit circle. Hence two tangent lines sharing a common point are never antipodal. -/
theorem ne_neg_of_onTangent_both {t s z : ℂ} (ht : ‖t‖ = 1)
    (hzt : onTangent t z) (hzs : onTangent s z) (hts : s = -t) : False := by
  rw [hts] at hzs
  unfold onTangent at hzt hzs
  have h : (4 : ℂ) * t = 0 := by
    linear_combination hzs - hzt
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0] at ht; simp at ht
  simp [ht0] at h

end FeuerbachBridge

