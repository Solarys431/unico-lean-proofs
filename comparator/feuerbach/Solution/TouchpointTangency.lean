/-
Copyright (c) 2026 Daniele Cappello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Cappello

Part of a Lean formalization of Feuerbach's theorem, produced by the
UNICO/NOUS autonomous certification pipeline (Claude, by Anthropic).
Every step is kernel-checked.
-/

import Mathlib
import Solution.TangentLines
import Solution.Normalization

/-! # Welding mathlib's touchpoint tangency to the scalar tangent equation

Here the two worlds actually meet: we take mathlib's abstract triangle (a
`Simplex ℝ P 2` in a two-dimensional Euclidean space) and prove that, under the
normalizing map Φ:

  · every touchpoint lands on the UNIT CIRCLE;
  · every VERTEX satisfies the tangent equation at the two touchpoints of the
    sides that contain it.

From there, `tangent_inter_unique` identifies the vertex with the core's formula,
and the chain is closed.
-/

namespace FeuerbachWeld

open EuclideanGeometry Affine Module FeuerbachMap FeuerbachBridge

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

variable (t : Triangle ℝ P) (signs : Finset (Fin 3))

/-- **The touchpoints land on the unit circle.**

Every touchpoint is at distance `exradius` from the excenter (mathlib:
`ExcenterExists.dist_excenter`), and Φ divides by exactly that. -/
theorem norm_Φ_touchpoint_eq_one (hE : t.ExcenterExists signs)
    (hr : 0 < t.exradius signs) (i : Fin 3) :
    ‖Φ (V := V) (t.excenter signs) (t.exradius signs) (t.touchpoint signs i)‖ = 1 := by
  refine norm_Φ_eq_one _ hr ?_
  rw [dist_comm]
  exact hE.dist_excenter i

/-- **The vertex lies on the side opposite every other vertex.**

For a triangle, the face opposite vertex `j` is the side through the other two,
so it contains vertex `i` whenever `i ≠ j`. -/
theorem vertex_mem_side {i j : Fin 3} (hij : i ≠ j) :
    t.points i ∈ affineSpan ℝ (Set.range (t.faceOpposite j).points) :=
  (Affine.Simplex.points_mem_affineSpan_faceOpposite (s := t)).2 hij

/-- **THE WELDING.** Under Φ, vertex `i` satisfies the tangent equation at
touchpoint `j`, for every `j ≠ i`.

Chain: the side opposite `j` is tangent to the sphere at touchpoint `j` (mathlib);
vertex `i` lies on that side (above); hence the radius to the touchpoint is
orthogonal to the vector from the touchpoint to the vertex; orthogonality
transports under Φ (`inner_Φ_sub`); and orthogonality in ℂ IS the tangent equation
(`onTangent_of_inner_eq_zero`). -/
theorem Φ_vertex_onTangent (hE : t.ExcenterExists signs) (hr : 0 < t.exradius signs)
    {i j : Fin 3} (hij : i ≠ j) :
    onTangent (Φ (V := V) (t.excenter signs) (t.exradius signs) (t.touchpoint signs j))
      (Φ (V := V) (t.excenter signs) (t.exradius signs) (t.points i)) := by
  set c := t.excenter signs
  set r := t.exradius signs
  set q := t.touchpoint signs j
  -- the touchpoint is on the unit circle
  have hnorm : ‖Φ (V := V) c r q‖ = 1 := norm_Φ_touchpoint_eq_one t signs hE hr j
  -- mathlib: the side is tangent to the sphere at the touchpoint, and the vertex lies on the side
  have hinner : inner ℝ (t.points i -ᵥ q : V) (q -ᵥ c : V) = (0 : ℝ) :=
    (hE.isTangentAt_touchpoint j).inner_left_eq_zero_of_mem (vertex_mem_side t hij)
  -- orthogonality transports under Φ
  have hinnerC : inner ℝ (Φ (V := V) c r (t.points i) - Φ (V := V) c r q)
      (Φ (V := V) c r q) = (0 : ℝ) := by
    rw [inner_Φ_sub c hr, hinner, zero_div]
  exact onTangent_of_inner_eq_zero hnorm hinnerC

end FeuerbachWeld
