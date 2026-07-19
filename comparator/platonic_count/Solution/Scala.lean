import Mathlib
import Challenge
import Solution.InvarianteSimilarita
import Solution.SimilarEquiv

/-!
RIGIDITÀ, R′0 — IL POLITOPO SCALATO (18-19 lug 2026).

La parte-scaling della falla 9 del vaglio: l'omotetia positiva x ↦ a•x è
un'equivalenza affine (lineare invertibile), quindi trasporta punti estremi
in punti estremi e hull in hull; il politopo scalato è un politopo, il suo
toSet è l'immagine, e P è Similar al proprio scalato (testimoni a e
l'identità). Con questo, nella rigidità si normalizza il lato una volta per
tutte e si lavora a congruenza.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- L'omotetia positiva come equivalenza affine. -/
noncomputable def omotetia (a : ℝ) (ha : a ≠ 0) : E n ≃ᵃ[ℝ] E n :=
  (LinearEquiv.smulOfNeZero ℝ (E n) a ha).toAffineEquiv

@[simp] theorem omotetia_apply (a : ℝ) (ha : a ≠ 0) (x : E n) :
    omotetia a ha x = a • x := rfl

/-- Il politopo scalato. -/
noncomputable def scala (a : ℝ) (ha : a ≠ 0) (P : ConvexPolytope n) :
    ConvexPolytope n where
  vertices := P.vertices.image (a • ·)
  vertices_nonempty := by
    obtain ⟨v, hv⟩ := P.vertices_nonempty
    exact ⟨a • v, Finset.mem_image_of_mem _ hv⟩
  vertices_eq_extremePoints := by
    classical
    have hset : ((P.vertices.image (a • ·) : Finset (E n)) : Set (E n)) =
        (⇑(omotetia a ha)) '' ((P.vertices : Set (E n))) := by
      ext x
      simp [omotetia_apply]
    rw [hset]
    have hhull : convexHull ℝ ((⇑(omotetia a ha)) ''
        ((P.vertices : Set (E n)))) =
        (⇑(omotetia a ha)) '' (convexHull ℝ ((P.vertices : Set (E n)))) := by
      have h1 := (omotetia a ha).toAffineMap.image_convexHull
        ((P.vertices : Set (E n)))
      have hco : (⇑(omotetia a ha).toAffineMap : E n → E n) =
          ⇑(omotetia a ha) := rfl
      rw [hco] at h1
      exact h1.symm
    rw [hhull]
    rw [extremePoints_image_affineEquiv]
    congr 1
    exact P.vertices_eq_extremePoints

theorem scala_toSet (a : ℝ) (ha : a ≠ 0) (P : ConvexPolytope n) :
    (scala a ha P).toSet = (fun x : E n => a • x) '' P.toSet := by
  classical
  show convexHull ℝ (((P.vertices.image (a • ·) : Finset (E n))) :
    Set (E n)) = _
  have hset : ((P.vertices.image (a • ·) : Finset (E n)) : Set (E n)) =
      (⇑(omotetia a ha)) '' ((P.vertices : Set (E n))) := by
    ext x
    simp [omotetia_apply]
  rw [hset]
  have h1 := (omotetia a ha).toAffineMap.image_convexHull
    ((P.vertices : Set (E n)))
  have hco : (⇑(omotetia a ha).toAffineMap : E n → E n) =
      ⇑(omotetia a ha) := rfl
  rw [hco] at h1
  rw [← h1]
  rfl

/-- **Ogni politopo è simile al proprio scalato.** -/
theorem similar_scala (a : ℝ) (ha : 0 < a) (P : ConvexPolytope n) :
    Similar P (scala a (ne_of_gt ha) P) := by
  refine ⟨a, ha, AffineIsometryEquiv.refl ℝ (E n), ?_⟩
  rw [scala_toSet]
  congr 1
  simp

end LeanEval.Geometry.PlatonicClassification
