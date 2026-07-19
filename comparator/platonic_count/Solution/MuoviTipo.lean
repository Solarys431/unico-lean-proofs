import Mathlib
import Challenge
import Solution.FanVertice
import Solution.Muovi
import Solution.Immagini

/-!
RIGIDITÀ — IL TIPO CICLICO SOTTO ISOMETRIA (19 lug 2026).

Ultimo pezzo infrastrutturale dell'assemblaggio: il gemello isometrico di
`ScalaTipo`. La registrazione produce un'isometria `g`; per confrontare i
ventagli occorre sapere che `muovi g Q` è ancora dello stesso tipo e che
il suo ventaglio è l'immagine di quello di `Q`. Le facce e le faccette si
trasportano con i lemmi di `Immagini`, adattati al fatto che qui `g` NON
è una simmetria del politopo ma lo manda in un altro.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- Il corpo del politopo mosso, al livello finito. -/
theorem toSet_muovi_finite (g : Isom 3) (P : ConvexPolytope 3) :
    (muovi g P).asFinite.toSet = (⇑g) '' P.asFinite.toSet :=
  muovi_toSet g P

/-- Le facce si trasportano sul politopo mosso. -/
theorem isFace_muovi {P : ConvexPolytope 3} (g : Isom 3)
    {F : Set (E 3)} (hF : P.asFinite.IsFace F) :
    (muovi g P).asFinite.IsFace ((⇑g) '' F) := by
  refine ⟨?_, hF.2.image _⟩
  rw [toSet_muovi_finite g P]
  exact isExposed_image_isom g hF.1

/-- Le faccette si trasportano sul politopo mosso. -/
theorem isFacet_muovi {P : ConvexPolytope 3} (g : Isom 3)
    {F : Set (E 3)} (hF : P.asFinite.IsFacet F) :
    (muovi g P).asFinite.IsFacet ((⇑g) '' F) := by
  refine ⟨isFace_muovi g hF.1, ?_⟩
  have h2 : Module.finrank ℝ (vectorSpan ℝ F) = 2 := hF.2
  show Module.finrank ℝ (vectorSpan ℝ ((⇑g) '' F)) = 2
  have hd := faceDim_image_isom g F
  show faceDim ((⇑g) '' F) = 2
  rw [hd]
  exact h2

/-- Andata e ritorno dell'isometria sulle immagini. -/
theorem image_isom_roundtrip (g : Isom 3) (G : Set (E 3)) :
    (⇑g) '' ((⇑g.symm) '' G) = G := by
  rw [← Set.image_comp]
  have h : (⇑g) ∘ (⇑g.symm) = id := by
    funext z
    simp
  rw [h, Set.image_id]

/-- Le faccette del politopo mosso vengono da faccette di P. -/
theorem isFacet_of_muovi {P : ConvexPolytope 3} (g : Isom 3)
    {G : Set (E 3)} (hG : (muovi g P).asFinite.IsFacet G) :
    P.asFinite.IsFacet ((⇑g.symm) '' G) ∧ G = (⇑g) '' ((⇑g.symm) '' G) := by
  refine ⟨⟨⟨?_, hG.1.2.image _⟩, ?_⟩, (image_isom_roundtrip g G).symm⟩
  · have hP : P.asFinite.toSet = (⇑g.symm) '' ((muovi g P).asFinite.toSet) := by
      rw [toSet_muovi_finite g P, ← Set.image_comp]
      have h : (⇑g.symm) ∘ (⇑g) = id := by
        funext z
        simp
      rw [h, Set.image_id]
    rw [hP]
    exact isExposed_image_isom g.symm hG.1.1
  · have h2 : Module.finrank ℝ (vectorSpan ℝ G) = 2 := hG.2
    show faceDim ((⇑g.symm) '' G) = 2
    rw [faceDim_image_isom]
    exact h2

/-- I vertici del politopo mosso sono le immagini dei vertici. -/
theorem vertices_muovi_iff {P : ConvexPolytope 3} (g : Isom 3) {w : E 3} :
    w ∈ (muovi g P).vertices ↔ ∃ v ∈ P.vertices, g v = w := by
  classical
  constructor
  · intro hw
    have h : w ∈ P.vertices.image (⇑g) := hw
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp h
    exact ⟨v, hv, hvw⟩
  · rintro ⟨v, hv, rfl⟩
    exact mem_vertices_muovi g P hv

end LeanEval.Geometry.PlatonicClassification
