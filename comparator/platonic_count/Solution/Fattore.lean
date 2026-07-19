import Mathlib
import Challenge
import Solution.ScalaBandiere
import Solution.DiamPositivo
import Solution.BandieraSpigolo

/-!
RIGIDITÀ — IL FATTORE DI NORMALIZZAZIONE (19 lug 2026).

La parte dell'assemblaggio che non dipende dai lemmi di trasporto: ogni
politopo full-dimensional ha uno spigolo (la bandiera ne fornisce uno), il
suo diametro è positivo e, in un politopo regolare, non dipende da quale
spigolo si prenda. Il fattore `a = diam(δ_P)/diam(δ_Q)` è dunque ben
definito e positivo.

Il lato del politopo, così misurato, è un invariante intrinseco: nessun
riferimento a `ell` orbitale (regola dell'audit del 19 lug).
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Ogni politopo full-dimensional di ℝ³ ha uno spigolo. -/
theorem esiste_spigolo (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    ∃ δ : Set (E 3), P.IsFace δ ∧ faceDim δ = 1 := by
  obtain ⟨F⟩ := flag_exists P hfull
  exact ⟨F.face 1, F.isFace 1, F.dim_eq 1⟩

/-- **IL LATO DI UN POLITOPO REGOLARE**: il diametro comune dei suoi
spigoli, con la prova che è ben definito e positivo. -/
theorem esiste_lato (P : ConvexPolytope 3) (hreg : P.IsRegular) :
    ∃ l : ℝ, 0 < l ∧
      ∀ δ : Set (E 3), P.IsFace δ → faceDim δ = 1 → Metric.diam δ = l := by
  obtain ⟨δ₀, hδ₀, hdδ₀⟩ := esiste_spigolo P hreg.1
  refine ⟨Metric.diam δ₀, diam_spigolo_pos P hδ₀ hdδ₀, ?_⟩
  intro δ hδ hdδ
  exact spigoli_congrui P hreg hδ hdδ hδ₀ hdδ₀

/-- **IL FATTORE DI NORMALIZZAZIONE**, ben definito e positivo: porta il
lato di `Q` su quello di `P`. -/
theorem esiste_fattore (P Q : ConvexPolytope 3)
    (hregP : P.IsRegular) (hregQ : Q.IsRegular) :
    ∃ a : ℝ, 0 < a ∧
      ∀ (δ ε : Set (E 3)), P.IsFace δ → faceDim δ = 1 →
        Q.IsFace ε → faceDim ε = 1 →
        Metric.diam δ = a * Metric.diam ε := by
  obtain ⟨lP, hlP, hPeq⟩ := esiste_lato P hregP
  obtain ⟨lQ, hlQ, hQeq⟩ := esiste_lato Q hregQ
  refine ⟨lP / lQ, div_pos hlP hlQ, ?_⟩
  intro δ ε hδ hdδ hε hdε
  rw [hPeq δ hδ hdδ, hQeq ε hε hdε]
  field_simp

end LeanEval.Geometry.PlatonicClassification
