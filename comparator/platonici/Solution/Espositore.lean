import Mathlib
import Solution.Fondamenta


open Set Metric

/-!
SONDA R1a (campagna #50): ogni vertice di un `FiniteConvexPolytope` ammette un
funzionale ESPOSITORE stretto (il vertice è il minimo stretto di f sul corpo).
È la sorgente della puntatezza del cono al vertice: da qui ⟪spigolo, w⟫ > 0.

Catena: vertici = punti estremi → v ∉ hull(vertici∖{v}) (mem_sdiff_convexHull) →
hull finito compatto → chiuso → separazione di Hahn-Banach geometrica →
decomposizione hull(insert) per stringere su TUTTO il corpo.
-/

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

namespace FiniteConvexPolytope


theorem vertice_espositore (P : FiniteConvexPolytope A) (v : A)
    (hv : v ∈ P.vertices) :
    ∃ f : A →L[ℝ] ℝ, ∀ x ∈ P.toSet, x ≠ v → f v < f x := by
  have hvS : v ∈ (P.vertices : Set A) := by exact_mod_cast hv
  have hconv : Convex ℝ P.toSet := convex_convexHull ℝ _
  have hvex : v ∈ (P.toSet).extremePoints ℝ := by
    have := P.vertices_eq_extremePoints ▸ hvS
    exact this
  -- v non sta nell'hull degli altri vertici
  have hnot : v ∉ convexHull ℝ ((P.vertices : Set A) \ {v}) := by
    have h1 := (hconv.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff).mp hvex
    intro hmem
    exact h1.2 (convexHull_mono
      (Set.diff_subset_diff_left (subset_convexHull ℝ _)) hmem)
  by_cases hrest : ((P.vertices : Set A) \ {v}).Nonempty
  · -- separazione stretta dal compatto hull(altri)
    have hfin : ((P.vertices : Set A) \ {v}).Finite :=
      P.vertices.finite_toSet.subset Set.diff_subset
    have hclosed : IsClosed (convexHull ℝ ((P.vertices : Set A) \ {v})) :=
      (hfin.isCompact_convexHull ℝ).isClosed
    obtain ⟨f, u, hfu, hub⟩ :
        ∃ (f : A →L[ℝ] ℝ) (u : ℝ), f v < u ∧
          ∀ b ∈ convexHull ℝ ((P.vertices : Set A) \ {v}), u < f b :=
      geometric_hahn_banach_point_closed (convex_convexHull ℝ _) hclosed hnot
    refine ⟨f, ?_⟩
    intro x hx hxv
    -- decomposizione: toSet = ⋃_{z ∈ hull(altri)} segment v z
    have hins : (P.vertices : Set A) = insert v ((P.vertices : Set A) \ {v}) := by
      rw [Set.insert_diff_singleton, Set.insert_eq_self.mpr hvS]
    have hxJ : x ∈ convexJoin ℝ {v} (convexHull ℝ ((P.vertices : Set A) \ {v})) := by
      rw [← convexHull_insert hrest, ← hins]
      exact hx
    rw [mem_convexJoin] at hxJ
    obtain ⟨w', hw', z, hz, hseg⟩ := hxJ
    rw [Set.mem_singleton_iff] at hw'
    rw [hw'] at hseg
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
    have hfz : f v < f z := hfu.trans (hub z hz)
    have hbpos : 0 < b := by
      rcases lt_or_eq_of_le hb with h | h
      · exact h
      · exfalso
        apply hxv
        have : a = 1 := by linarith
        simp [← h, this]
    have hcalc : f (a • v + b • z) = a * f v + b * f z := by
      simp [map_add, map_smul]
    rw [hcalc]
    have ha1 : a = 1 - b := by linarith
    rw [ha1]
    nlinarith [mul_pos hbpos (sub_pos.mpr hfz)]
  · -- il politopo è il solo punto v: la tesi è vacua
    refine ⟨0, ?_⟩
    intro x hx hxv
    exfalso
    apply hxv
    have hsingle : (P.vertices : Set A) = {v} := by
      apply Set.eq_singleton_iff_unique_mem.mpr
      refine ⟨hvS, fun y hy => ?_⟩
      by_contra hyv
      exact hrest ⟨y, hy, hyv⟩
    have : P.toSet = {v} := by
      rw [toSet, hsingle, convexHull_singleton]
    rw [this] at hx
    exact hx

end FiniteConvexPolytope
