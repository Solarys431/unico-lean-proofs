import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.Fondamenta
import UnicoProofs.Platonici.VerticiEsposti
import UnicoProofs.Platonici.SottoPolitopo
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.Immagini
import UnicoProofs.Platonici.FanVertice

/-!
FASE 3A, F7 — IL TRASPORTO DEL VERTICE CICLICO (18 lug 2026).

Una simmetria τ del politopo che manda v in v' trasporta i dati del vertice
q-ciclico: le faccette del fan passano per immagine, la simmetria locale per
coniugio τ∘σ∘τ⁻¹, e ogni campo si verifica spingendo avanti e indietro le
immagini. Con questo il q del vertice è UNIFORME su tutti i vertici di un
politopo regolare (le bandiere ai due vertici si trasportano).
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Il trasporto dei dati di vertice ciclico lungo una simmetria. -/
theorem cyclicVertexData_trasporto (P : ConvexPolytope 3)
    {τ : Isom 3} (hτ : P.isSymmetry τ) {v v' : E 3} (hτv : τ v = v')
    {q : ℕ} (h : P.asFinite.CyclicVertexData v q) :
    Nonempty (P.asFinite.CyclicVertexData v' q) := by
  classical
  -- il coniugio
  set σ' : Isom 3 := (τ.symm.trans h.σ).trans τ with hσ'
  have hσ'app : ∀ z : E 3, σ' z = τ (h.σ (τ.symm z)) := by
    intro z
    rfl
  have hτback : τ.symm v' = v := by
    rw [← hτv]
    exact τ.symm_apply_apply v
  refine ⟨{
    faccetta := fun i => (⇑τ) '' h.faccetta i
    isFacet := ?_
    mem_v := ?_
    distinte := ?_
    complete := ?_
    σ := σ'
    fissa_v := ?_
    preserva := ?_
    ruota := ?_
    spigolo := ?_
    spigolo_due := ?_ }⟩
  · -- immagini di faccette sono faccette
    intro i
    have h1 := h.isFacet i
    rw [P.asFinite_isFacet_iff] at h1 ⊢
    exact ⟨isFace_image_isom τ hτ h1.1, by
      rw [faceDim_image_isom]
      exact h1.2⟩
  · intro i
    exact ⟨v, h.mem_v i, hτv⟩
  · intro i j hij
    apply h.distinte
    exact Set.image_injective.mpr τ.injective hij
  · intro A hA hvA
    -- il pull-back di A è una faccetta per v
    have hA' : P.asFinite.IsFacet ((⇑τ.symm) '' A) := by
      rw [P.asFinite_isFacet_iff] at hA ⊢
      exact ⟨isFace_image_isom τ.symm (symmetry_symm hτ) hA.1, by
        rw [faceDim_image_isom]
        exact hA.2⟩
    have hvA' : v ∈ (⇑τ.symm) '' A := by
      refine ⟨v', hvA, hτback⟩
    obtain ⟨i, hi⟩ := h.complete _ hA' hvA'
    refine ⟨i, ?_⟩
    rw [← hi]
    -- τ '' (τ⁻¹ '' A) = A
    rw [← Set.image_comp]
    have h2 : (⇑τ) ∘ (⇑τ.symm) = id := by
      funext z
      simp
    rw [h2, Set.image_id]
  · -- σ' fissa v'
    rw [hσ'app, hτback, h.fissa_v, hτv]
  · -- σ' preserva il politopo
    show (⇑σ') '' P.toSet = P.toSet
    have h1 : (⇑σ' : E 3 → E 3) = (⇑τ) ∘ (⇑h.σ) ∘ (⇑τ.symm) := by
      funext z
      exact hσ'app z
    rw [h1]
    rw [Set.image_comp, Set.image_comp]
    have hτsym : (⇑τ.symm) '' P.toSet = P.toSet := symmetry_symm hτ
    have hpres : (⇑h.σ) '' P.toSet = P.toSet := by
      have h0 := h.preserva
      rwa [P.asFinite_toSet] at h0
    rw [hτsym, hpres, hτ]
  · -- la rotazione per coniugio
    intro i
    have h1 : (⇑σ' : E 3 → E 3) = (⇑τ) ∘ (⇑h.σ) ∘ (⇑τ.symm) := by
      funext z
      exact hσ'app z
    rw [h1, Set.image_comp, Set.image_comp]
    have h2 : (⇑τ.symm) '' ((⇑τ) '' h.faccetta i) = h.faccetta i := by
      rw [← Set.image_comp]
      have h3 : (⇑τ.symm) ∘ (⇑τ) = id := by
        funext z
        simp
      rw [h3, Set.image_id]
    rw [h2, h.ruota i]
  · -- lo spigolo condiviso
    intro i
    obtain ⟨x, hxv, hx⟩ := h.spigolo i
    refine ⟨τ x, ?_, ⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
    intro hcon
    apply hxv
    apply τ.injective
    rw [hcon, hτv]
  · -- spigolo_due per pull-back
    intro i j x hx hxv hxj
    obtain ⟨y, hy, hyx⟩ := hx.1
    have hyi : y ∈ h.faccetta i := hy
    obtain ⟨z, hz, hzx⟩ := hx.2
    have hyz : y = z := by
      apply τ.injective
      rw [hyx, hzx]
    obtain ⟨u, hu, hux⟩ := hxj
    have hyu : y = u := by
      apply τ.injective
      rw [hyx, hux]
    apply h.spigolo_due i j y ⟨hyi, by rw [hyz]; exact hz⟩
    · intro hcon
      apply hxv
      rw [← hyx, hcon, hτv]
    · rw [hyu]
      exact hu

end LeanEval.Geometry.PlatonicClassification
