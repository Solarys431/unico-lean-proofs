import Mathlib
import Challenge
import Solution.InvarianteSimilarita

/-!
FASE 3BCD, R-EQ — LA SIMILARITÀ È UN'EQUIVALENZA (18 lug 2026).

`Similar P Q = ∃ a > 0, ∃ φ isometria, Q.toSet = (a•·) '' (φ '' P.toSet)`.
Il nucleo di symm e trans è il CONIUGIO: per a > 0 e ρ isometria affine,
x ↦ a • ρ(a⁻¹ • x) è ancora un'isometria affine, e assorbe lo scaling:
(coniugio ρ)(a • x) = a • ρ(x). Con questo l'inversa e la composizione di
similitudini tornano nella forma normale scaling∘isometria del benchmark:
per symm si usa il coniugio di φ.symm, per trans quello con a⁻¹.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Il coniugio di un'isometria con uno scaling positivo. La parte lineare
resta quella di ρ: lo scaling commuta con le mappe lineari. -/
noncomputable def coniugioScala (a : ℝ) (ha : a ≠ 0) (ρ : Isom n) : Isom n :=
  AffineIsometryEquiv.mk'
    (fun x => a • ρ (a⁻¹ • x))
    ρ.linearIsometryEquiv
    (0 : E n)
    (by
      intro p
      show a • ρ (a⁻¹ • p) = ρ.linearIsometryEquiv (p - 0) + a • ρ (a⁻¹ • 0)
      have h2 : ρ.linearIsometryEquiv (a⁻¹ • p - a⁻¹ • 0) =
          ρ (a⁻¹ • p) - ρ (a⁻¹ • 0) := ρ.map_vsub _ _
      have h3 : ρ.linearIsometryEquiv (p - 0) =
          a • ρ.linearIsometryEquiv (a⁻¹ • (p - 0)) := by
        rw [map_smul, smul_smul, mul_inv_cancel₀ ha, one_smul]
      rw [h3]
      have h4 : a⁻¹ • (p - 0) = a⁻¹ • p - a⁻¹ • 0 := by
        simp [smul_sub]
      rw [h4, h2, smul_sub]
      abel)

@[simp] theorem coniugioScala_apply (a : ℝ) (ha : a ≠ 0) (ρ : Isom n)
    (x : E n) : coniugioScala a ha ρ x = a • ρ (a⁻¹ • x) := rfl

theorem coniugioScala_smul (a : ℝ) (ha : a ≠ 0) (ρ : Isom n) (x : E n) :
    coniugioScala a ha ρ (a • x) = a • ρ x := by
  rw [coniugioScala_apply]
  congr 1
  rw [smul_smul, inv_mul_cancel₀ ha, one_smul]

/-- La similarità è simmetrica. -/
theorem similar_symm {P Q : ConvexPolytope n} (h : Similar P Q) :
    Similar Q P := by
  obtain ⟨a, ha, φ, hQ⟩ := h
  have hane : a ≠ 0 := ne_of_gt ha
  refine ⟨a⁻¹, inv_pos.mpr ha, coniugioScala a hane φ.symm, ?_⟩
  rw [hQ]
  rw [Set.image_image, Set.image_image, Set.image_image]
  have hid : ∀ x : E n,
      a⁻¹ • (coniugioScala a hane φ.symm) (a • φ x) = x := by
    intro x
    rw [coniugioScala_smul]
    rw [φ.symm_apply_apply]
    rw [smul_smul, inv_mul_cancel₀ hane, one_smul]
  ext x
  constructor
  · intro hx
    exact ⟨x, hx, hid x⟩
  · rintro ⟨y, hy, hxy⟩
    rw [← hxy]
    show a⁻¹ • (coniugioScala a hane φ.symm) (a • φ y) ∈ P.toSet
    rw [hid y]
    exact hy

/-- La similarità è transitiva. -/
theorem similar_trans {P Q R : ConvexPolytope n}
    (h1 : Similar P Q) (h2 : Similar Q R) : Similar P R := by
  obtain ⟨a, ha, φ, hQ⟩ := h1
  obtain ⟨b, hb, ψ, hR⟩ := h2
  have hane : a ≠ 0 := ne_of_gt ha
  have haine : a⁻¹ ≠ 0 := inv_ne_zero hane
  -- ψ̂ assorbe lo scaling a: ψ(a • z) = a • ψ̂ z
  set ψhat : Isom n := coniugioScala a⁻¹ haine ψ with hψhat
  have hassorbe : ∀ z : E n, ψ (a • z) = a • ψhat z := by
    intro z
    rw [hψhat, coniugioScala_apply]
    rw [inv_inv]
    rw [smul_smul, mul_inv_cancel₀ hane, one_smul]
  refine ⟨b * a, mul_pos hb ha, φ.trans ψhat, ?_⟩
  rw [hR, hQ]
  rw [Set.image_image, Set.image_image, Set.image_image, Set.image_image]
  have hid : ∀ x : E n,
      b • ψ (a • φ x) = (b * a) • (φ.trans ψhat) x := by
    intro x
    rw [hassorbe (φ x)]
    rw [smul_smul]
    rfl
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    show (b * a) • (φ.trans ψhat) y = x
    rw [← hxy]
    exact (hid y).symm
  · rintro ⟨y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    show b • ψ (a • φ y) = x
    rw [← hxy]
    exact hid y

end LeanEval.Geometry.PlatonicClassification
