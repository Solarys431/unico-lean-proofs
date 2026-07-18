import Mathlib
import UnicoProofs.Platonici.Benchmark

/-!
FASE 2, P5 — L'INVARIANTE DI SIMILARITÀ (18 lug 2026).

La similitudine del benchmark (scala positiva ∘ isometria) è un'equivalenza
affine; le equivalenze affini biiettano i punti estremi; i vertici di un
`ConvexPolytope` SONO i punti estremi del corpo. Quindi |vertices| è
invariante per similitudine. I cinque solidi hanno 4, 8, 6, 20, 12 vertici:
a coppie non simili.
-/

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- I punti estremi si trasportano lungo un'equivalenza affine. -/
theorem extremePoints_image_affineEquiv (T : E n ≃ᵃ[ℝ] E n) (s : Set (E n)) :
    Set.extremePoints ℝ ((⇑T) '' s) = (⇑T) '' Set.extremePoints ℝ s := by
  have hseg : ∀ u v : E n,
      (⇑T) '' openSegment ℝ u v = openSegment ℝ (T u) (T v) := fun u v =>
    image_openSegment _ T.toAffineMap u v
  ext y
  constructor
  · rintro ⟨hy, hstr⟩
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro u hu v hv hxseg
    have himg : T x ∈ openSegment ℝ (T u) (T v) := by
      rw [← hseg]
      exact ⟨x, hxseg, rfl⟩
    have hmu : T u ∈ (⇑T) '' s := ⟨u, hu, rfl⟩
    have hmv : T v ∈ (⇑T) '' s := ⟨v, hv, rfl⟩
    exact T.injective (hstr hmu hmv himg)
  · rintro ⟨x, hxm, rfl⟩
    obtain ⟨hx, hstr⟩ := hxm
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    intro u hu v hv hy
    obtain ⟨u', hu', hue⟩ := hu
    obtain ⟨v', hv', hve⟩ := hv
    have hpre : x ∈ openSegment ℝ u' v' := by
      rw [← hue, ← hve, ← hseg] at hy
      obtain ⟨w, hw, hwx⟩ := hy
      rwa [← T.injective hwx]
    have h1 : u' = x := hstr hu' hv' hpre
    rw [← hue, h1]

/-- La mappa della similitudine come equivalenza affine. -/
noncomputable def similMap (a : ℝ) (ha : 0 < a) (φ : Isom n) : E n ≃ᵃ[ℝ] E n :=
  φ.toAffineEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ (E n) a (ne_of_gt ha)).toAffineEquiv

theorem similMap_apply (a : ℝ) (ha : 0 < a) (φ : Isom n) (x : E n) :
    similMap a ha φ x = a • (φ x) := rfl

/-- |vertices| è invariante per similitudine. -/
theorem vertices_card_of_similar {P Q : ConvexPolytope n}
    (h : Similar P Q) : Q.vertices.card = P.vertices.card := by
  classical
  obtain ⟨a, ha, φ, hQ⟩ := h
  have hT : Q.toSet = (⇑(similMap a ha φ)) '' P.toSet := by
    rw [hQ, ← Set.image_comp]
    rfl
  have hQv : (Q.vertices : Set (E n))
      = (⇑(similMap a ha φ)) '' (P.vertices : Set (E n)) := by
    have h1 : (Q.vertices : Set (E n)) = Set.extremePoints ℝ Q.toSet :=
      Q.vertices_eq_extremePoints
    have h2 : (P.vertices : Set (E n)) = Set.extremePoints ℝ P.toSet :=
      P.vertices_eq_extremePoints
    rw [h1, h2, hT, extremePoints_image_affineEquiv]
  have hfin : Q.vertices = P.vertices.image (⇑(similMap a ha φ)) := by
    apply Finset.coe_injective
    rw [Finset.coe_image, hQv]
  rw [hfin]
  exact Finset.card_image_of_injective _ (similMap a ha φ).injective

/-- La similitudine è riflessiva. -/
theorem similar_refl (P : ConvexPolytope n) : Similar P P := by
  refine ⟨1, one_pos, AffineIsometryEquiv.refl ℝ (E n), ?_⟩
  simp

end LeanEval.Geometry.PlatonicClassification
