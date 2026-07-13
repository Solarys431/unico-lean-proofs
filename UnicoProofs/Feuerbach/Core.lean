/-
Copyright (c) 2026 Daniele Cappello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Cappello

Part of a Lean formalization of Feuerbach's theorem, produced by the
UNICO/NOUS autonomous certification pipeline (Claude, by Anthropic).
Every step is kernel-checked.
-/

import Mathlib

/-! # The algebraic core on the unit-circle tangential model

Hypotheses fixed after the adversarial gate: the touchpoints are nonzero (they lie
on the unit circle) and pairwise non-antipodal (otherwise `P = 0` and two sides of
the triangle would be parallel).

The heart of the matter: conjugation on the unit circle is the inversion `t ↦ 1/t`,
and under it `e₂ ↦ e₁/e₃` and `P ↦ P/e₃²`. It follows that `conj N = e₁²/P`, and the
squared distance between the nine-point center and the origin becomes `e₁²e₂²/P²`,
which by the symmetric identity `P = e₁e₂ − e₃` is exactly `(w+1)²`.
-/

namespace FeuerbachCore

open Complex

variable {t₁ t₂ t₃ : ℂ}

/-- Elementary symmetric polynomials. -/
noncomputable def e₁ (t₁ t₂ t₃ : ℂ) : ℂ := t₁ + t₂ + t₃
noncomputable def e₂ (t₁ t₂ t₃ : ℂ) : ℂ := t₁ * t₂ + t₁ * t₃ + t₂ * t₃
noncomputable def e₃ (t₁ t₂ t₃ : ℂ) : ℂ := t₁ * t₂ * t₃

/-- The product of the denominators: it vanishes exactly when `tᵢ = −tⱼ` for some
pair (which on the unit circle means: two antipodal touchpoints). -/
noncomputable def P (t₁ t₂ t₃ : ℂ) : ℂ := (t₁ + t₂) * (t₁ + t₃) * (t₂ + t₃)

/-- The key parameter `w = e₃/P`. On the unit circle it is a real number
(`w_inv` + conjugation); its sign will separate the incircle from the excircles
once the link with the arcs is established (the range-weld's job, not this file's). -/
noncomputable def w (t₁ t₂ t₃ : ℂ) : ℂ := e₃ t₁ t₂ t₃ / P t₁ t₂ t₃

/-- The nine-point center of the tangential triangle. -/
noncomputable def N (t₁ t₂ t₃ : ℂ) : ℂ := (e₂ t₁ t₂ t₃) ^ 2 / P t₁ t₂ t₃

/-- **(I1)** The symmetric identity `P = e₁e₂ − e₃`: purely polynomial. -/
theorem P_eq (t₁ t₂ t₃ : ℂ) :
    P t₁ t₂ t₃ = e₁ t₁ t₂ t₃ * e₂ t₁ t₂ t₃ - e₃ t₁ t₂ t₃ := by
  unfold P e₁ e₂ e₃; ring

/-- Corollary of (I1): `e₃ + P = e₁e₂`. This is the pivot of everything. -/
theorem e₃_add_P (t₁ t₂ t₃ : ℂ) :
    e₃ t₁ t₂ t₃ + P t₁ t₂ t₃ = e₁ t₁ t₂ t₃ * e₂ t₁ t₂ t₃ := by
  rw [P_eq]; ring

/-- **The heart, in the abstract.** If `c + p = a·b` with `p ≠ 0`, then
`(b²/p)·(a²/p) = (c/p + 1)²`. All of Feuerbach's theorem lives in this one line:
the left side is the squared distance between the centers, the right side is the
square of `w+1`. -/
theorem heart_alg (a b c p : ℂ) (hp : p ≠ 0) (h : c + p = a * b) :
    b ^ 2 / p * (a ^ 2 / p) = (c / p + 1) ^ 2 := by
  field_simp
  linear_combination (-(c + p + a * b)) * h

section Conjugation

variable (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) (h₃ : t₃ ≠ 0)
include h₁ h₂ h₃

/-- Under inversion, `e₁` becomes `e₂/e₃`. -/
theorem e₁_inv : e₁ t₁⁻¹ t₂⁻¹ t₃⁻¹ = e₂ t₁ t₂ t₃ / e₃ t₁ t₂ t₃ := by
  unfold e₁ e₂ e₃; field_simp; ring

/-- Under inversion, `e₂` becomes `e₁/e₃`. -/
theorem e₂_inv : e₂ t₁⁻¹ t₂⁻¹ t₃⁻¹ = e₁ t₁ t₂ t₃ / e₃ t₁ t₂ t₃ := by
  unfold e₂ e₁ e₃; field_simp; ring

/-- Under inversion, `e₃` becomes `1/e₃`. -/
theorem e₃_inv : e₃ t₁⁻¹ t₂⁻¹ t₃⁻¹ = (e₃ t₁ t₂ t₃)⁻¹ := by
  unfold e₃; field_simp

/-- Under inversion, `P` becomes `P/e₃²`. -/
theorem P_inv : P t₁⁻¹ t₂⁻¹ t₃⁻¹ = P t₁ t₂ t₃ / (e₃ t₁ t₂ t₃) ^ 2 := by
  unfold P e₃; field_simp; ring

/-- `N` evaluated at the inverse arguments equals `e₁²/P`. On the unit circle
(where `conj t = t⁻¹`) this is the conjugate of `N`. -/
theorem N_inv (hP : P t₁ t₂ t₃ ≠ 0) :
    N t₁⁻¹ t₂⁻¹ t₃⁻¹ = (e₁ t₁ t₂ t₃) ^ 2 / P t₁ t₂ t₃ := by
  have he₃ : e₃ t₁ t₂ t₃ ≠ 0 := by
    unfold e₃; exact mul_ne_zero (mul_ne_zero h₁ h₂) h₃
  unfold N
  rw [e₂_inv h₁ h₂ h₃, P_inv h₁ h₂ h₃]
  field_simp

/-- **(I3)** `w` is invariant under inversion of its arguments. On the unit circle
(where inversion is conjugation) this says that `w` is real. -/
theorem w_inv (hP : P t₁ t₂ t₃ ≠ 0) : w t₁⁻¹ t₂⁻¹ t₃⁻¹ = w t₁ t₂ t₃ := by
  have he₃ : e₃ t₁ t₂ t₃ ≠ 0 := by
    unfold e₃; exact mul_ne_zero (mul_ne_zero h₁ h₂) h₃
  unfold w
  rw [e₃_inv h₁ h₂ h₃, P_inv h₁ h₂ h₃]
  field_simp

/-- **(I2) — THE HEART OF FEUERBACH'S THEOREM.** The cross-product identity:
`N · N(inverse arguments) = (w+1)²`. On the unit circle the second factor is
`conj N`, so the product is `‖N‖²`: the squared distance between the nine-point
center and the origin. -/
theorem normSq_N (hP : P t₁ t₂ t₃ ≠ 0) :
    N t₁ t₂ t₃ * N t₁⁻¹ t₂⁻¹ t₃⁻¹ = (w t₁ t₂ t₃ + 1) ^ 2 := by
  rw [N_inv h₁ h₂ h₃ hP]
  unfold N w
  exact heart_alg (e₁ t₁ t₂ t₃) (e₂ t₁ t₂ t₃) (e₃ t₁ t₂ t₃) (P t₁ t₂ t₃) hP
    (e₃_add_P t₁ t₂ t₃)

end Conjugation


section Circumcenter

/-- The circumcenter of the tangential triangle, in the model. -/
noncomputable def O (t₁ t₂ t₃ : ℂ) : ℂ :=
  2 * e₃ t₁ t₂ t₃ * e₁ t₁ t₂ t₃ / P t₁ t₂ t₃

/-- The conjugate of the circumcenter: `conj O = 2e₂/P`. -/
theorem O_inv (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) (h₃ : t₃ ≠ 0) (hP : P t₁ t₂ t₃ ≠ 0) :
    O t₁⁻¹ t₂⁻¹ t₃⁻¹ = 2 * e₂ t₁ t₂ t₃ / P t₁ t₂ t₃ := by
  have he₃ : e₃ t₁ t₂ t₃ ≠ 0 := by
    unfold e₃; exact mul_ne_zero (mul_ne_zero h₁ h₂) h₃
  unfold O
  rw [e₃_inv h₁ h₂ h₃, e₁_inv h₁ h₂ h₃, P_inv h₁ h₂ h₃]
  unfold e₁ e₂ e₃ at *
  field_simp

/-- **Equidistance from the circumcenter** (first vertex), in cross-product form:
`(V₁ − O) · (V₁ − O)(inverse arguments) = 4e₃²/P²`. On the unit circle the product
is `‖V₁ − O‖² = R²`. The other two follow by rotation. -/
theorem normSq_vertex_sub_O (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) (h₃ : t₃ ≠ 0)
    (hP : P t₁ t₂ t₃ ≠ 0) (h₂₃ : t₂ + t₃ ≠ 0) :
    (2 * t₂ * t₃ / (t₂ + t₃) - O t₁ t₂ t₃)
        * (2 / (t₂ + t₃) - O t₁⁻¹ t₂⁻¹ t₃⁻¹)
      = 4 * (e₃ t₁ t₂ t₃) ^ 2 / (P t₁ t₂ t₃) ^ 2 := by
  have h₁₂ : t₁ + t₂ ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hP)
  have h₁₃ : t₁ + t₃ ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hP)
  rw [O_inv h₁ h₂ h₃ hP]
  unfold O e₁ e₂ e₃ P at *
  field_simp
  ring

end Circumcenter


section Symmetry

/-- `P` is invariant under cyclic rotation of its arguments. -/
theorem P_rotate (t₁ t₂ t₃ : ℂ) : P t₂ t₃ t₁ = P t₁ t₂ t₃ := by unfold P; ring

/-- `O` is invariant under cyclic rotation of its arguments. -/
theorem O_rotate (t₁ t₂ t₃ : ℂ) : O t₂ t₃ t₁ = O t₁ t₂ t₃ := by
  unfold O e₁ e₃ P; ring

/-- `e₃` is invariant under cyclic rotation. -/
theorem e₃_rotate (t₁ t₂ t₃ : ℂ) : e₃ t₂ t₃ t₁ = e₃ t₁ t₂ t₃ := by unfold e₃; ring

/-- **The nine-point center as the sum of the vertices**: `N = (V₁+V₂+V₃−O)/2`,
where `Vᵢ` are the vertices of the tangential triangle. This is the identity that
links mathlib's definition (via the Euler line) to the closed form `e₂²/P`. -/
theorem N_eq_sum (h₁₂ : t₁ + t₂ ≠ 0) (h₁₃ : t₁ + t₃ ≠ 0) (h₂₃ : t₂ + t₃ ≠ 0)
    (hP : P t₁ t₂ t₃ ≠ 0) :
    (2 * t₂ * t₃ / (t₂ + t₃) + 2 * t₃ * t₁ / (t₃ + t₁) + 2 * t₁ * t₂ / (t₁ + t₂)
        - O t₁ t₂ t₃) / 2 = N t₁ t₂ t₃ := by
  have h₃₁ : t₃ + t₁ ≠ 0 := by rwa [add_comm]
  unfold O N e₁ e₂ e₃ P at *
  field_simp
  ring

end Symmetry

end FeuerbachCore

