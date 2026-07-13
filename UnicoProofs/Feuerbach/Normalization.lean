/-
Copyright (c) 2026 Daniele Cappello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Cappello

Part of a Lean formalization of Feuerbach's theorem, produced by the
UNICO/NOUS autonomous certification pipeline (Claude, by Anthropic).
Every step is kernel-checked.
-/

import Mathlib

/-! # The normalizing similarity Φ

Φ sends the abstract Euclidean plane to the complex plane, with the circle's
center placed at the origin and the radius rescaled to 1:

    Φ(p) := toComplex (p -ᵥ center) / radius

Under Φ:
  · the center maps to 0
  · the touchpoints land on the UNIT CIRCLE (norm 1)
  · the sides (tangent to the sphere) become tangent lines to the unit circle
  · the vertices become the intersections of the tangent lines — the core's formula

This is the link between mathlib's abstractions and the concrete model.
-/

namespace FeuerbachMap

open EuclideanGeometry Affine Module

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

/-- The canonical isometry from the vector plane to `ℂ` (the same one built for
Morley). -/
noncomputable def toComplex : V ≃ₗᵢ[ℝ] ℂ :=
  ((stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)).repr.trans
    Complex.orthonormalBasisOneI.repr.symm

/-- **The normalizing map**: center at the origin, radius rescaled to 1. -/
noncomputable def Φ (c : P) (r : ℝ) (p : P) : ℂ :=
  (toComplex (V := V) (p -ᵥ c)) / (r : ℂ)

/-- The center maps to the origin. -/
@[simp] theorem Φ_center (c : P) (r : ℝ) : Φ (V := V) c r c = 0 := by
  simp [Φ]

/-- **Distances scale**: `‖Φ p‖ = dist p c / r`. This is the lemma that carries the
touchpoints onto the unit circle. -/
theorem norm_Φ (c : P) {r : ℝ} (hr : 0 < r) (p : P) :
    ‖Φ (V := V) c r p‖ = dist p c / r := by
  rw [Φ, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le,
    LinearIsometryEquiv.norm_map, dist_eq_norm_vsub V]

/-- **The touchpoints land on the unit circle.** If `p` is at distance `r` from
the center (as every touchpoint is at distance `exradius` from the excenter), then
`‖Φ p‖ = 1`. -/
theorem norm_Φ_eq_one (c : P) {r : ℝ} (hr : 0 < r) {p : P} (hp : dist p c = r) :
    ‖Φ (V := V) c r p‖ = 1 := by
  rw [norm_Φ c hr p, hp, div_self hr.ne']

/-- **The inner product transports.** Orthogonality in `P` becomes orthogonality
in `ℂ`, up to the positive scale factor. This is the link that allows
`onTangent_of_inner_eq_zero` to be applied. -/
theorem inner_Φ_sub (c : P) {r : ℝ} (hr : 0 < r) (p q : P) :
    inner ℝ (Φ (V := V) c r p - Φ (V := V) c r q) (Φ (V := V) c r q)
      = inner ℝ (p -ᵥ q : V) (q -ᵥ c : V) / r ^ 2 := by
  have hr0 : r ≠ 0 := hr.ne'
  -- division by a real number is a scalar multiplication
  have hdiv : ∀ z : ℂ, z / (r : ℂ) = (r⁻¹ : ℝ) • z := by
    intro z
    rw [Complex.real_smul]
    push_cast
    field_simp
  have hsub : Φ (V := V) c r p - Φ (V := V) c r q
      = (r⁻¹ : ℝ) • (toComplex (V := V) (p -ᵥ q)) := by
    rw [Φ, Φ, div_sub_div_same, ← map_sub, vsub_sub_vsub_cancel_right, hdiv]
  have hq : Φ (V := V) c r q = (r⁻¹ : ℝ) • (toComplex (V := V) (q -ᵥ c)) := by
    rw [Φ, hdiv]
  rw [hsub, hq, real_inner_smul_left, real_inner_smul_right,
    LinearIsometryEquiv.inner_map_map]
  field_simp


/-- **Distances scale between any two points**: `dist (Φ x) (Φ y) = dist x y / r`. -/
theorem dist_Φ (c : P) {r : ℝ} (hr : 0 < r) (x y : P) :
    dist (Φ (V := V) c r x) (Φ (V := V) c r y) = dist x y / r := by
  have hsub : Φ (V := V) c r x - Φ (V := V) c r y
      = (toComplex (V := V) (x -ᵥ y)) / (r : ℂ) := by
    rw [Φ, Φ, div_sub_div_same, ← map_sub, vsub_sub_vsub_cancel_right]
  rw [dist_eq_norm, hsub, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le,
    LinearIsometryEquiv.norm_map, ← dist_eq_norm_vsub]

/-- **Φ is injective**: it is a similarity, and similarities do not glue points
together. -/
theorem Φ_injective (c : P) {r : ℝ} (hr : 0 < r) :
    Function.Injective (Φ (V := V) c r) := by
  intro x y hxy
  have h := dist_Φ (V := V) c hr x y
  rw [hxy, dist_self] at h
  have : dist x y = 0 := by
    field_simp [hr.ne'] at h
    simpa using h.symm
  exact dist_eq_zero.mp this

end FeuerbachMap

