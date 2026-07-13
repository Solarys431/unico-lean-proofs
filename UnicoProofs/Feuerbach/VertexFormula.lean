/-
Copyright (c) 2026 Daniele Cappello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Cappello

Part of a Lean formalization of Feuerbach's theorem, produced by the
UNICO/NOUS autonomous certification pipeline (Claude, by Anthropic).
Every step is kernel-checked.
-/

import Mathlib
import UnicoProofs.Feuerbach.TangentLines
import UnicoProofs.Feuerbach.Normalization
import UnicoProofs.Feuerbach.TouchpointTangency

/-! # The vertices as unique intersections of tangent lines

The touchpoints are distinct, non-antipodal, and the normalized vertex IS the
core's formula.

  · `touchpoint_ne`: if two touchpoints coincided, the two sides would lie on the
    same tangent line and the three vertices would be collinear, against affine
    independence. (Dimension argument: 2 ≤ 1, absurd.)
  · `Φ_vertex_eq`: combining the welding, the exclusion of antipodality, and the
    uniqueness of the intersection, the normalized vertex is `2·tⱼtₖ/(tⱼ+tₖ)`.
-/

namespace FeuerbachAssembly

open EuclideanGeometry Affine Module FeuerbachMap FeuerbachBridge FeuerbachWeld

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

variable (t : Triangle ℝ P) (signs : Finset (Fin 3))

/-- **The touchpoints are distinct.** If they coincided at `p`, both sides would
lie on the tangent line at `p` (the orthogonal to the radius), and with them all
three vertices: but three affinely independent points cannot lie on a line. -/
theorem touchpoint_ne (hE : t.ExcenterExists signs) (hr : 0 < t.exradius signs)
    {j k : Fin 3} (hjk : j ≠ k) :
    t.touchpoint signs j ≠ t.touchpoint signs k := by
  intro heq
  set p := t.touchpoint signs j with hp
  -- p ≠ center, since it is at distance r > 0 from the center
  have hpc : (p -ᵥ (t.exsphere signs).center : V) ≠ 0 := by
    rw [vsub_ne_zero]
    intro h0
    have hd := hE.dist_excenter j
    rw [← hp] at hd
    rw [Simplex.exsphere_center] at h0
    rw [h0] at hd
    simp only [dist_self] at hd
    exact hr.ne hd
  -- both sides lie in the orthogonal to the radius at p
  have hj := (hE.isTangentAt_touchpoint j).le_orthRadius
  have hk := (hE.isTangentAt_touchpoint k).le_orthRadius
  rw [← heq] at hk
  -- hence all three vertices lie in it
  have hall : ∀ i, t.points i ∈ (t.exsphere signs).orthRadius p := by
    intro i
    rcases eq_or_ne i j with rfl | hij
    · exact hk (vertex_mem_side t hjk)
    · exact hj (vertex_mem_side t hij)
  -- the vectorSpan of the vertices lies within the direction of the orthogonal, which has rank 1
  have hspan : vectorSpan ℝ (Set.range t.points)
      ≤ ((t.exsphere signs).orthRadius p).direction := by
    rw [vectorSpan_def]
    refine Submodule.span_le.2 ?_
    rintro v ⟨x, ⟨i, rfl⟩, y, ⟨i', rfl⟩, rfl⟩
    exact AffineSubspace.vsub_mem_direction (hall i) (hall i')
  have hrank2 : finrank ℝ (vectorSpan ℝ (Set.range t.points)) = 2 :=
    t.independent.finrank_vectorSpan (by simp)
  have hdir : ((t.exsphere signs).orthRadius p).direction
      = (ℝ ∙ (p -ᵥ (t.exsphere signs).center))ᗮ := by
    rw [Sphere.orthRadius, AffineSubspace.direction_mk']
  have hrank1 : finrank ℝ ((ℝ ∙ (p -ᵥ (t.exsphere signs).center))ᗮ) = 1 := by
    have hline : finrank ℝ (ℝ ∙ (p -ᵥ (t.exsphere signs).center) : Submodule ℝ V) = 1 :=
      finrank_span_singleton hpc
    have htot := Submodule.finrank_add_finrank_orthogonal
      (ℝ ∙ (p -ᵥ (t.exsphere signs).center))
    rw [hline, Fact.out (p := finrank ℝ V = 2)] at htot
    omega
  have hle := Submodule.finrank_mono hspan
  rw [hrank2, hdir, hrank1] at hle
  omega

/-- **The normalized touchpoints are not antipodal**: their sum is nonzero, since
the vertex lies on both tangent lines and antipodal tangent lines are parallel. -/
theorem Φ_touchpoint_add_ne_zero (hE : t.ExcenterExists signs)
    (hr : 0 < t.exradius signs) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) :
    Φ (V := V) (t.excenter signs) (t.exradius signs) (t.touchpoint signs j)
      + Φ (V := V) (t.excenter signs) (t.exradius signs) (t.touchpoint signs k) ≠ 0 := by
  intro hsum
  exact ne_neg_of_onTangent_both
    (norm_Φ_touchpoint_eq_one t signs hE hr j)
    (Φ_vertex_onTangent t signs hE hr hij)
    (Φ_vertex_onTangent t signs hE hr hik)
    (by linear_combination hsum)

/-- **The normalized vertex is the core's formula**: `2·tⱼtₖ/(tⱼ+tₖ)`. -/
theorem Φ_vertex_eq (hE : t.ExcenterExists signs) (hr : 0 < t.exradius signs)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Φ (V := V) (t.excenter signs) (t.exradius signs) (t.points i)
      = 2 * (Φ (V := V) (t.excenter signs) (t.exradius signs) (t.touchpoint signs j))
          * (Φ (V := V) (t.excenter signs) (t.exradius signs) (t.touchpoint signs k))
          / ((Φ (V := V) (t.excenter signs) (t.exradius signs) (t.touchpoint signs j))
            + (Φ (V := V) (t.excenter signs) (t.exradius signs) (t.touchpoint signs k))) :=
  tangent_inter_unique
    (norm_Φ_touchpoint_eq_one t signs hE hr j)
    (norm_Φ_touchpoint_eq_one t signs hE hr k)
    ((Φ_injective (V := V) (t.excenter signs) hr).ne (touchpoint_ne t signs hE hr hjk))
    (Φ_touchpoint_add_ne_zero t signs hE hr hij hik)
    (Φ_vertex_onTangent t signs hE hr hij)
    (Φ_vertex_onTangent t signs hE hr hik)

end FeuerbachAssembly
