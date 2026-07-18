import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.Fondamenta
import UnicoProofs.Platonici.VerticiEsposti
import UnicoProofs.Platonici.SottoPolitopo
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.Interpolazione
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.BandieraCompagna
import UnicoProofs.Platonici.Immagini
import UnicoProofs.Platonici.BandieraVertice
import UnicoProofs.Platonici.FanVertice
import UnicoProofs.Platonici.VerticeCiclico
import UnicoProofs.Platonici.TrasportoData
import UnicoProofs.Platonici.TrasportoFaccetta
import UnicoProofs.Platonici.FaccettaRegolare
import UnicoProofs.Platonici.Classificazione

/-!
FASE 3A, B3 — IL PONTE (18 lug 2026).

**IsRegular ⟹ IsCyclicallyRegularOfType p q.** L'assemblaggio: una faccetta
di riferimento dà (p, ℓ) via `faccetta_regolare` (fascicolo 18 di sol); un
vertice di riferimento dà q via `verticeCiclico_del_regolare`; ogni altra
faccetta/vertice riceve la struttura PER TRASPORTO lungo il trasportatore
delle bandiere (nessun teorema di unicità richiesto). Il rango 3 dei vertici
viene dal full-dim via l'invarianza dello span affine sotto hull.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **IL PONTE**: ogni politopo regolare di ℝ³ è ciclicamente regolare di
tipo (p, q) per qualche p, q ≥ 3. -/
theorem ponte_regolare (P : ConvexPolytope 3) (hreg : P.IsRegular) :
    ∃ p q : ℕ, P.asFinite.IsCyclicallyRegularOfType p q := by
  classical
  have hfull : P.IsFullDim := hreg.1
  -- il rango 3 dei vertici
  have hfin3 : Module.finrank ℝ
      (vectorSpan ℝ (P.vertices : Set (E 3))) = 3 := by
    have h1 : affineSpan ℝ P.toSet =
        affineSpan ℝ ((P.vertices : Set (E 3))) := by
      show affineSpan ℝ (convexHull ℝ ((P.vertices : Set (E 3)))) = _
      exact affineSpan_convexHull _
    have h2 : vectorSpan ℝ ((P.vertices : Set (E 3))) =
        vectorSpan ℝ P.toSet := by
      rw [← direction_affineSpan, ← direction_affineSpan, h1]
    rw [h2]
    exact hfull
  -- la faccetta di riferimento
  have hd1 : 1 ≤ Module.finrank ℝ (vectorSpan ℝ P.toSet) := by
    have h1 : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
    omega
  obtain ⟨A₀, hA₀, hdA₀'⟩ := facet_exists P hd1
  have hdA₀ : faceDim A₀ = 2 := by
    rw [hdA₀']
    have h1 : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
    omega
  obtain ⟨p, ℓ, hRF₀⟩ := faccetta_regolare P hreg hA₀ hdA₀
  have hℓ : 0 < ℓ := hRF₀.2.1
  have hp3 : 3 ≤ p := hRF₀.2.2.1
  -- il vertice di riferimento
  obtain ⟨v₀, hv₀⟩ := P.vertices_nonempty
  obtain ⟨q, hq3, hData₀⟩ := verticeCiclico_del_regolare P hreg hv₀
  refine ⟨p, q, hfin3, hp3, hq3, ℓ, hℓ, ?_, ?_⟩
  · -- ogni faccetta è p-gonale regolare di lato ℓ, per trasporto
    intro B hB
    have hB' := hB
    rw [P.asFinite_isFacet_iff] at hB'
    obtain ⟨hBf, hdB⟩ := hB'
    obtain ⟨F₀, hF₀2⟩ := bandiera_con_faccetta P hA₀ hdA₀
    obtain ⟨FB, hFB2⟩ := bandiera_con_faccetta P hBf hdB
    obtain ⟨τ, hτP, hτflag⟩ := hreg.2 F₀ FB
    have hτA : (⇑τ) '' A₀ = B := by
      have h1 := hτflag 2
      rw [hF₀2, hFB2] at h1
      exact h1
    have h2 := isRegularFacet_trasporto P hτP hRF₀
    rwa [hτA] at h2
  · -- ogni vertice è q-ciclico, per trasporto
    intro v hvV
    show P.asFinite.IsCyclicVertex v q
    obtain ⟨F₀, hF₀0⟩ := bandiera_al_vertice P hfull hv₀
    obtain ⟨Fv, hFv0⟩ := bandiera_al_vertice P hfull hvV
    obtain ⟨τ, hτP, hτflag⟩ := hreg.2 F₀ Fv
    have hτv : τ v₀ = v := by
      have h1 : τ v₀ ∈ (⇑τ) '' F₀.face 0 := ⟨v₀, by rw [hF₀0]; rfl, rfl⟩
      rw [hτflag 0, hFv0] at h1
      exact h1
    obtain ⟨data⟩ := hData₀
    exact cyclicVertexData_trasporto P hτP hτv data

/-- **LA CLASSIFICAZIONE DEL REGOLARE**: ogni politopo regolare di ℝ³ è
ciclicamente regolare di tipo (p, q) con (p, q) fra le CINQUE coppie
platoniche. Il ponte salda IsRegular al motore certificato del 17 luglio. -/
theorem regolare_schlafli (P : ConvexPolytope 3) (hreg : P.IsRegular) :
    ∃ p q : ℕ, P.asFinite.IsCyclicallyRegularOfType p q ∧
      ((p = 3 ∧ q = 3) ∨ (p = 4 ∧ q = 3) ∨ (p = 3 ∧ q = 4) ∨
       (p = 5 ∧ q = 3) ∨ (p = 3 ∧ q = 5)) := by
  obtain ⟨p, q, h⟩ := ponte_regolare P hreg
  exact ⟨p, q, h, (cyclicallyRegular_schlafli P.asFinite h).2⟩

end LeanEval.Geometry.PlatonicClassification
