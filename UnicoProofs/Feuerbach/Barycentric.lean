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

/-!
# Barycentric sign certificates

(sol's route, distilled version.)

If `0 = λ₀V₀ + λ₁V₁ + λ₂V₂` with `Σλ = 1` (the center as an affine combination
of the normalized vertices), then two PURE rational identities hold:

  (A)  W · λ₀λ₁λ₂ · ‖a−b‖²‖a−c‖²‖b−c‖² = −1
  (B)  W · (‖a+b+c‖² − 1) = 1

plus the nine identity: 9 − ‖a+b+c‖² = ‖a−b‖² + ‖a−c‖² + ‖b−c‖².

Immediate consequences: all weights positive (incenter) ⟹ W ≤ −1 (internal
tangency); one negative weight (excenter) ⟹ W > 1/8 (external tangency). No
arcs, no cosines: only certificates.
-/

namespace FeuerbachBarycentric

open FeuerbachCore

/-- On the unit circle, `‖a−b‖² = −(a−b)²/(ab)` (as an identity in `ℂ`). -/
theorem normSq_sub_unit {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ((Complex.normSq (a - b) : ℝ) : ℂ) = -(a - b) ^ 2 / (a * b) := by
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := by intro h; rw [h] at hb; simp at hb
  have hca : (starRingEnd ℂ) a = a⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, ha]; simp
  have hcb : (starRingEnd ℂ) b = b⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hb]; simp
  rw [← Complex.mul_conj, map_sub, hca, hcb]
  field_simp
  ring

/-- On the unit circle, `‖a+b+c‖² = (a+b+c)(ab+ac+bc)/(abc)` (in `ℂ`). -/
theorem normSq_add_three_unit {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    ((Complex.normSq (a + b + c) : ℝ) : ℂ)
      = (a + b + c) * (a * b + a * c + b * c) / (a * b * c) := by
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := by intro h; rw [h] at hb; simp at hb
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
  have hca : (starRingEnd ℂ) a = a⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, ha]; simp
  have hcb : (starRingEnd ℂ) b = b⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hb]; simp
  have hcc : (starRingEnd ℂ) c = c⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hc]; simp
  rw [← Complex.mul_conj, map_add, map_add, hca, hcb, hcc]
  field_simp
  ring

section Lambdas

variable {a b c : ℂ} {l0 l1 l2 : ℝ}

-- The barycentric hypotheses in polynomial form (denominators already cleared):
-- `hE2` is the combination of the vertices, `hE3` its conjugate.
variable (hsum : (l0 : ℂ) + l1 + l2 = 1)
  (hE2 : (l0 : ℂ) * (2 * b * c) * ((c + a) * (a + b))
      + (l1 : ℂ) * (2 * c * a) * ((b + c) * (a + b))
      + (l2 : ℂ) * (2 * a * b) * ((b + c) * (c + a)) = 0)
  (hE3 : (l0 : ℂ) * 2 * ((c + a) * (a + b))
      + (l1 : ℂ) * 2 * ((b + c) * (a + b))
      + (l2 : ℂ) * 2 * ((b + c) * (c + a)) = 0)

include hsum hE2 hE3

/-- The closed form of the first weight: `λ₀(a−b)(a−c) = −a(b+c)`. -/
theorem lambda0_mul (hab : a + b ≠ 0) (hac : a + c ≠ 0) :
    (l0 : ℂ) * ((a - b) * (a - c)) = -(a * (b + c)) := by
  have key : (2 * (a + b) * (a + c))
      * ((l0 : ℂ) * ((a - b) * (a - c)) + a * (b + c)) = 0 := by
    linear_combination (-(2 * a * (b + c) * (a + b) * (a + c))) * hsum + hE2 + a ^ 2 * hE3
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (mul_ne_zero (mul_ne_zero two_ne_zero hab) hac)
  · linear_combination h

/-- The closed form of the second weight: `λ₁(a−b)(b−c) = b(a+c)`. -/
theorem lambda1_mul (hab : a + b ≠ 0) (hbc : b + c ≠ 0) :
    (l1 : ℂ) * ((a - b) * (b - c)) = b * (a + c) := by
  have key : (2 * (a + b) * (b + c))
      * ((l1 : ℂ) * ((a - b) * (b - c)) - b * (a + c)) = 0 := by
    linear_combination (2 * b * (a + c) * (a + b) * (b + c)) * hsum - hE2 - b ^ 2 * hE3
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (mul_ne_zero (mul_ne_zero two_ne_zero hab) hbc)
  · linear_combination h

/-- The closed form of the third weight: `λ₂(a−c)(b−c) = −c(a+b)`. -/
theorem lambda2_mul (hac : a + c ≠ 0) (hbc : b + c ≠ 0) :
    (l2 : ℂ) * ((a - c) * (b - c)) = -(c * (a + b)) := by
  have key : (2 * (a + c) * (b + c))
      * ((l2 : ℂ) * ((a - c) * (b - c)) + c * (a + b)) = 0 := by
    linear_combination (-(2 * c * (a + b) * (a + c) * (b + c))) * hsum + hE2 + c ^ 2 * hE3
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (mul_ne_zero (mul_ne_zero two_ne_zero hac) hbc)
  · linear_combination h

/-- **The product of the weights**: `λ₀λ₁λ₂ · ∏(differences)² = e₃·P` (in `ℂ`).
Telescoping product of the three closed forms. -/
theorem lambda_prod (hab : a + b ≠ 0) (hac : a + c ≠ 0) (hbc : b + c ≠ 0) :
    ((l0 : ℂ) * l1 * l2) * ((a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2)
      = e₃ a b c * P a b c := by
  have h0 := lambda0_mul hsum hE2 hE3 hab hac
  have h1 := lambda1_mul hsum hE2 hE3 hab hbc
  have h2 := lambda2_mul hsum hE2 hE3 hac hbc
  unfold e₃ FeuerbachCore.P
  linear_combination
    (((l1 : ℂ) * ((a - b) * (b - c))) * ((l2 : ℂ) * ((a - c) * (b - c)))) * h0
    + ((-(a * (b + c))) * ((l2 : ℂ) * ((a - c) * (b - c)))) * h1
    + ((-(a * (b + c))) * (b * (a + c))) * h2

end Lambdas

section Signs

variable {a b c : ℂ} {l0 l1 l2 W : ℝ}

-- The multiplied variants of the norm lemmas (no divisions, for the certificates).
theorem normSq_sub_unit' (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ((Complex.normSq (a - b) : ℝ) : ℂ) * (a * b) = -(a - b) ^ 2 := by
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := by intro h; rw [h] at hb; simp at hb
  rw [normSq_sub_unit ha hb]
  field_simp

theorem normSq_add_three_unit' (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    ((Complex.normSq (a + b + c) : ℝ) : ℂ) * (a * b * c)
      = (a + b + c) * (a * b + a * c + b * c) := by
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := by intro h; rw [h] at hb; simp at hb
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
  rw [normSq_add_three_unit ha hb hc]
  field_simp

/-- **Identity (A)**: `W · λ₀λ₁λ₂ · ‖a−b‖²‖a−c‖²‖b−c‖² = −1`. -/
theorem W_mul_prod (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hP : P a b c ≠ 0) (hW : w a b c = (W : ℂ))
    (hprod : ((l0 : ℂ) * l1 * l2) * ((a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2)
      = e₃ a b c * P a b c) :
    W * (l0 * l1 * l2)
      * (Complex.normSq (a - b) * Complex.normSq (a - c) * Complex.normSq (b - c))
      = -1 := by
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := by intro h; rw [h] at hb; simp at hb
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
  have he₃ : e₃ a b c ≠ 0 := by
    unfold e₃; exact mul_ne_zero (mul_ne_zero ha0 hb0) hc0
  have hW' : (W : ℂ) * P a b c = e₃ a b c := by
    rw [← hW]; unfold w; field_simp
  have hn1 := normSq_sub_unit' ha hb
  have hn2 := normSq_sub_unit' ha hc
  have hn3 := normSq_sub_unit' hb hc
  have key : ((W : ℂ) * ((l0 : ℂ) * l1 * l2)
      * (((Complex.normSq (a - b) : ℝ) : ℂ) * ((Complex.normSq (a - c) : ℝ) : ℂ)
        * ((Complex.normSq (b - c) : ℝ) : ℂ)) + 1)
      * (P a b c * (a * b * (a * c) * (b * c))) = 0 := by
    have expand : ((W : ℂ) * ((l0 : ℂ) * l1 * l2)
        * (((Complex.normSq (a - b) : ℝ) : ℂ) * ((Complex.normSq (a - c) : ℝ) : ℂ)
          * ((Complex.normSq (b - c) : ℝ) : ℂ)))
        * (P a b c * (a * b * (a * c) * (b * c)))
        = ((W : ℂ) * P a b c) * (((l0 : ℂ) * l1 * l2)
          * ((((Complex.normSq (a - b) : ℝ) : ℂ) * (a * b))
            * ((((Complex.normSq (a - c) : ℝ) : ℂ)) * (a * c))
            * ((((Complex.normSq (b - c) : ℝ) : ℂ)) * (b * c)))) := by ring
    calc ((W : ℂ) * ((l0 : ℂ) * l1 * l2)
        * (((Complex.normSq (a - b) : ℝ) : ℂ) * ((Complex.normSq (a - c) : ℝ) : ℂ)
          * ((Complex.normSq (b - c) : ℝ) : ℂ)) + 1)
        * (P a b c * (a * b * (a * c) * (b * c)))
        = ((W : ℂ) * P a b c) * (((l0 : ℂ) * l1 * l2)
          * ((((Complex.normSq (a - b) : ℝ) : ℂ) * (a * b))
            * ((((Complex.normSq (a - c) : ℝ) : ℂ)) * (a * c))
            * ((((Complex.normSq (b - c) : ℝ) : ℂ)) * (b * c))))
          + P a b c * (a * b * (a * c) * (b * c)) := by ring
      _ = e₃ a b c * (((l0 : ℂ) * l1 * l2)
          * ((-(a - b) ^ 2) * (-(a - c) ^ 2) * (-(b - c) ^ 2)))
          + P a b c * (a * b * (a * c) * (b * c)) := by rw [hW', hn1, hn2, hn3]
      _ = -(e₃ a b c * (((l0 : ℂ) * l1 * l2)
          * ((a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2)))
          + P a b c * (a * b * (a * c) * (b * c)) := by ring
      _ = -(e₃ a b c * (e₃ a b c * P a b c))
          + P a b c * (a * b * (a * c) * (b * c)) := by rw [hprod]
      _ = 0 := by unfold e₃; ring
  rcases mul_eq_zero.mp key with h | h
  · have : ((W * (l0 * l1 * l2) * (Complex.normSq (a - b) * Complex.normSq (a - c)
        * Complex.normSq (b - c)) : ℝ) : ℂ) = ((-1 : ℝ) : ℂ) := by
      push_cast
      linear_combination h
    exact_mod_cast this
  · exact absurd h (mul_ne_zero hP (by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) (mul_ne_zero ha0 hc0)) ?_
      exact mul_ne_zero hb0 hc0))

/-- **Identity (B)**: `W · (‖a+b+c‖² − 1) = 1`. -/
theorem W_mul_normSq_sub_one (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hP : P a b c ≠ 0) (hW : w a b c = (W : ℂ)) :
    W * (Complex.normSq (a + b + c) - 1) = 1 := by
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := by intro h; rw [h] at hb; simp at hb
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
  have he₃ : e₃ a b c ≠ 0 := by
    unfold e₃; exact mul_ne_zero (mul_ne_zero ha0 hb0) hc0
  have hW' : (W : ℂ) * P a b c = e₃ a b c := by
    rw [← hW]; unfold w; field_simp
  have hns := normSq_add_three_unit' ha hb hc
  have key : (((W : ℂ) * (((Complex.normSq (a + b + c) : ℝ) : ℂ) - 1)) - 1)
      * (a * b * c) = 0 := by
    calc (((W : ℂ) * (((Complex.normSq (a + b + c) : ℝ) : ℂ) - 1)) - 1) * (a * b * c)
        = (W : ℂ) * (((Complex.normSq (a + b + c) : ℝ) : ℂ) * (a * b * c))
          - (W : ℂ) * (a * b * c) - a * b * c := by ring
      _ = (W : ℂ) * ((a + b + c) * (a * b + a * c + b * c))
          - (W : ℂ) * (a * b * c) - a * b * c := by rw [hns]
      _ = (W : ℂ) * P a b c - a * b * c := by
          rw [P_eq]; unfold e₁ e₂ e₃; ring
      _ = 0 := by rw [hW']; unfold e₃; ring
  rcases mul_eq_zero.mp key with h | h
  · have : ((W * (Complex.normSq (a + b + c) - 1) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      push_cast
      linear_combination h
    exact_mod_cast this
  · exact absurd h (mul_ne_zero (mul_ne_zero ha0 hb0) hc0)

/-- **The nine identity**: `9 − ‖a+b+c‖² = ‖a−b‖² + ‖a−c‖² + ‖b−c‖²`. -/
theorem nine_sub_normSq (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    9 - Complex.normSq (a + b + c)
      = Complex.normSq (a - b) + Complex.normSq (a - c) + Complex.normSq (b - c) := by
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := by intro h; rw [h] at hb; simp at hb
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
  have hns := normSq_add_three_unit' ha hb hc
  have hn1 := normSq_sub_unit' ha hb
  have hn2 := normSq_sub_unit' ha hc
  have hn3 := normSq_sub_unit' hb hc
  have key : (((9 - Complex.normSq (a + b + c)
      - (Complex.normSq (a - b) + Complex.normSq (a - c) + Complex.normSq (b - c)) : ℝ)) : ℂ)
      * (a * b * c) = 0 := by
    push_cast
    calc ((9 : ℂ) - ((Complex.normSq (a + b + c) : ℝ) : ℂ)
        - (((Complex.normSq (a - b) : ℝ) : ℂ) + ((Complex.normSq (a - c) : ℝ) : ℂ)
          + ((Complex.normSq (b - c) : ℝ) : ℂ))) * (a * b * c)
        = 9 * (a * b * c) - ((Complex.normSq (a + b + c) : ℝ) : ℂ) * (a * b * c)
          - ((((Complex.normSq (a - b) : ℝ) : ℂ) * (a * b)) * c
            + ((((Complex.normSq (a - c) : ℝ) : ℂ)) * (a * c)) * b
            + ((((Complex.normSq (b - c) : ℝ) : ℂ)) * (b * c)) * a) := by ring
      _ = 9 * (a * b * c) - (a + b + c) * (a * b + a * c + b * c)
          - ((-(a - b) ^ 2) * c + (-(a - c) ^ 2) * b + (-(b - c) ^ 2) * a) := by
          rw [hns, hn1, hn2, hn3]
      _ = 0 := by ring
  rcases mul_eq_zero.mp key with h | h
  · have h' : ((9 - Complex.normSq (a + b + c)
        - (Complex.normSq (a - b) + Complex.normSq (a - c) + Complex.normSq (b - c)) : ℝ) : ℂ)
        = 0 := h
    have : (9 - Complex.normSq (a + b + c)
        - (Complex.normSq (a - b) + Complex.normSq (a - c) + Complex.normSq (b - c)) : ℝ)
        = 0 := by exact_mod_cast h'
    linarith
  · exact absurd h (mul_ne_zero (mul_ne_zero ha0 hb0) hc0)

/-- **The sign for the INCENTER**: all weights positive ⟹ `W ≤ −1`. -/
theorem W_le_neg_one_of_pos_weights
    (hA : W * (l0 * l1 * l2)
      * (Complex.normSq (a - b) * Complex.normSq (a - c) * Complex.normSq (b - c)) = -1)
    (hB : W * (Complex.normSq (a + b + c) - 1) = 1)
    (h0 : 0 < l0) (h1 : 0 < l1) (h2 : 0 < l2)
    (hn1 : 0 < Complex.normSq (a - b)) (hn2 : 0 < Complex.normSq (a - c))
    (hn3 : 0 < Complex.normSq (b - c)) :
    W ≤ -1 := by
  have hX : 0 < (l0 * l1 * l2)
      * (Complex.normSq (a - b) * Complex.normSq (a - c) * Complex.normSq (b - c)) :=
    mul_pos (mul_pos (mul_pos h0 h1) h2) (mul_pos (mul_pos hn1 hn2) hn3)
  have hW0 : W < 0 := by nlinarith
  have hns : 0 ≤ Complex.normSq (a + b + c) := Complex.normSq_nonneg _
  nlinarith [mul_nonneg (neg_nonneg.mpr hW0.le) hns]

/-- **The sign for the EXCENTERS**: negative product of the weights ⟹ `1/8 < W`. -/
theorem W_gt_eighth_of_neg_weights
    (hA : W * (l0 * l1 * l2)
      * (Complex.normSq (a - b) * Complex.normSq (a - c) * Complex.normSq (b - c)) = -1)
    (hB : W * (Complex.normSq (a + b + c) - 1) = 1)
    (hC : 9 - Complex.normSq (a + b + c)
      = Complex.normSq (a - b) + Complex.normSq (a - c) + Complex.normSq (b - c))
    (hneg : l0 * l1 * l2 < 0)
    (hn1 : 0 < Complex.normSq (a - b)) (hn2 : 0 < Complex.normSq (a - c))
    (hn3 : 0 < Complex.normSq (b - c)) :
    1 / 8 < W := by
  have hX : (l0 * l1 * l2)
      * (Complex.normSq (a - b) * Complex.normSq (a - c) * Complex.normSq (b - c)) < 0 :=
    mul_neg_of_neg_of_pos hneg (mul_pos (mul_pos hn1 hn2) hn3)
  have hW0 : 0 < W := by nlinarith
  have hlt9 : Complex.normSq (a + b + c) < 9 := by nlinarith
  nlinarith [mul_lt_mul_of_pos_left hlt9 hW0]

end Signs

end FeuerbachBarycentric
