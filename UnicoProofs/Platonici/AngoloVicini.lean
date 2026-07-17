import Mathlib

/-!
L4 — L'ANGOLO DEI VICINI IN COORDINATE (campagna #50, G1-mio).

Tre punti su un cerchio: v e i suoi due vicini a distanza angolare ±α.
L'angolo in v tra le due corde è π − α, per puro prodotto interno:
⟪rot(α)d − d, rot(−α)d − d⟫ = ‖d‖²·2cosα(cosα−1),
‖rot(±α)d − d‖² = ‖d‖²·2(1−cosα), quindi cos∠ = −cosα e ∠ = π − α.
Niente teorema dell'angolo inscritto: solo `cos_two_mul` e `arccos`.
-/

open Real
open scoped RealInnerProductSpace

namespace PlatoniciL4

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- Il prodotto interno con il proprio ruotato, in forma generale. -/
theorem inner_rotazione_generale (o : Orientation ℝ E (Fin 2))
    (θ : Real.Angle) (x : E) :
    ⟪x, o.rotation θ x⟫ = ‖x‖ ^ 2 * Real.Angle.cos θ := by
  by_cases hx : x = 0
  · rw [hx]
    simp
  · rw [o.inner_eq_norm_mul_norm_mul_cos_oangle, LinearIsometryEquiv.norm_map,
      o.oangle_rotation_self_right hx]
    ring

/-- L'ANGOLO DEI VICINI: su un cerchio, l'angolo in v tra le corde verso i
due vicini a distanza angolare ±α vale π − α. -/
theorem angolo_vicini (o : Orientation ℝ E (Fin 2)) (d : E) (hd : d ≠ 0)
    (α : ℝ) (hα0 : 0 < α) (hαπ : α < π) :
    InnerProductGeometry.angle
      (o.rotation ((α : ℝ) : Real.Angle) d - d)
      (o.rotation ((-α : ℝ) : Real.Angle) d - d) = π - α := by
  have hdn : (0 : ℝ) < ‖d‖ := norm_pos_iff.mpr hd
  have hcα1 : Real.cos α < 1 := by
    calc Real.cos α < Real.cos 0 :=
          Real.strictAntiOn_cos ⟨le_refl 0, Real.pi_pos.le⟩
            ⟨hα0.le, hαπ.le⟩ hα0
      _ = 1 := Real.cos_zero
  -- ══ i tre prodotti interni fondamentali ══
  have hRR : ⟪o.rotation ((α : ℝ) : Real.Angle) d,
      o.rotation ((-α : ℝ) : Real.Angle) d⟫
      = ‖d‖ ^ 2 * Real.cos (2 * α) := by
    have hcomp : o.rotation ((-α : ℝ) : Real.Angle) d
        = o.rotation ((α : ℝ) : Real.Angle)
            (o.rotation ((-(2 * α) : ℝ) : Real.Angle) d) := by
      rw [o.rotation_rotation]
      congr 1
      rw [← Real.Angle.coe_add]
      congr 1
      ring
    rw [hcomp, LinearIsometryEquiv.inner_map_map,
      inner_rotazione_generale, Real.Angle.cos_coe, Real.cos_neg]
  have hRd : ⟪o.rotation ((α : ℝ) : Real.Angle) d, d⟫
      = ‖d‖ ^ 2 * Real.cos α := by
    rw [real_inner_comm, inner_rotazione_generale, Real.Angle.cos_coe]
  have hdR : ⟪d, o.rotation ((-α : ℝ) : Real.Angle) d⟫
      = ‖d‖ ^ 2 * Real.cos α := by
    rw [inner_rotazione_generale, Real.Angle.cos_coe, Real.cos_neg]
  -- ══ numeratore ══
  have hnum : ⟪o.rotation ((α : ℝ) : Real.Angle) d - d,
      o.rotation ((-α : ℝ) : Real.Angle) d - d⟫
      = ‖d‖ ^ 2 * (2 * Real.cos α * (Real.cos α - 1)) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      hRR, hRd, hdR, real_inner_self_eq_norm_sq, Real.cos_two_mul]
    ring
  -- ══ denominatore: le due norme al quadrato ══
  have hn1 : ‖o.rotation ((α : ℝ) : Real.Angle) d - d‖ ^ 2
      = ‖d‖ ^ 2 * (2 * (1 - Real.cos α)) := by
    rw [norm_sub_sq_real, LinearIsometryEquiv.norm_map, hRd]
    ring
  have hn2 : ‖o.rotation ((-α : ℝ) : Real.Angle) d - d‖ ^ 2
      = ‖d‖ ^ 2 * (2 * (1 - Real.cos α)) := by
    rw [norm_sub_sq_real, LinearIsometryEquiv.norm_map,
      real_inner_comm d (o.rotation ((-α : ℝ) : Real.Angle) d), hdR]
    ring
  set Aq : ℝ := ‖d‖ ^ 2 * (2 * (1 - Real.cos α)) with hAqdef
  have hAqpos : (0 : ℝ) < Aq := by
    rw [hAqdef]
    have h1 : (0 : ℝ) < 1 - Real.cos α := by linarith
    positivity
  have hnorm1 : ‖o.rotation ((α : ℝ) : Real.Angle) d - d‖ = Real.sqrt Aq := by
    rw [← hn1]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hnorm2 : ‖o.rotation ((-α : ℝ) : Real.Angle) d - d‖ = Real.sqrt Aq := by
    rw [← hn2]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  -- ══ il quoziente e l'arccos ══
  unfold InnerProductGeometry.angle
  rw [hnum, hnorm1, hnorm2, Real.mul_self_sqrt hAqpos.le]
  have hquot : ‖d‖ ^ 2 * (2 * Real.cos α * (Real.cos α - 1)) / Aq
      = -Real.cos α := by
    rw [div_eq_iff (ne_of_gt hAqpos), hAqdef]
    ring
  rw [hquot, Real.arccos_neg, Real.arccos_cos hα0.le hαπ.le]

end PlatoniciL4
