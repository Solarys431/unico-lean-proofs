import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.BandieraVertice
import UnicoProofs.Platonici.Interpolazione
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.SpigoliCongrui
import UnicoProofs.Platonici.FacceConnesse

/-!
RIGIDITÀ — OGNI SPIGOLO STA IN UNA BANDIERA (19 lug 2026).

Scarico dell'ipotesi di `spigoli_congrui_di_bandiere`: dato uno spigolo
(faccia di rango 1), si costruisce la bandiera che lo contiene — un suo
vertice sotto, una faccetta sopra (per interpolazione) — e se ne conclude
che TUTTI gli spigoli di un politopo regolare hanno lo stesso diametro,
senza ipotesi residue. È la lunghezza del lato come invariante
intrinseco: nessun riferimento a `ell` e quindi nessuna esposizione alla
falla dei testimoni «a stella».
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- La faccetta che sovrasta uno spigolo, per interpolazione. -/
theorem faccetta_sopra_spigolo (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {δ : Set (E 3)} (hδ : P.IsFace δ) (hdδ : faceDim δ = 1) :
    ∃ A : Set (E 3), P.IsFace A ∧ faceDim A = 2 ∧ δ ⊂ A := by
  classical
  have hPdim : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
  have hgap : faceDim δ + 2 ≤ Module.finrank ℝ (vectorSpan ℝ P.toSet) := by
    rw [hdδ, hPdim]
  obtain ⟨A, hA, hss, hAne⟩ := interpolazione P hδ hgap
  refine ⟨A, hA, ?_, hss⟩
  show Module.finrank ℝ (vectorSpan ℝ A) = 2
  have hlo0 := faceDim_lt_of_ssubset P hδ hA hss
  have hlo : Module.finrank ℝ (vectorSpan ℝ δ) <
      Module.finrank ℝ (vectorSpan ℝ A) := hlo0
  have hdim1 : Module.finrank ℝ (vectorSpan ℝ δ) = 1 := hdδ
  have hAss : A ⊂ P.toSet :=
    ⟨face_subset_toSet P hA, fun hsub =>
      hAne (Set.Subset.antisymm (face_subset_toSet P hA) hsub)⟩
  have hhi0 := faceDim_lt_of_ssubset P hA (toSet_isFace P) hAss
  have hhi : Module.finrank ℝ (vectorSpan ℝ A) <
      Module.finrank ℝ (vectorSpan ℝ P.toSet) := hhi0
  omega

/-- Il vertice sotto uno spigolo, come faccia di rango 0. -/
theorem vertice_sotto_spigolo (P : ConvexPolytope 3)
    {δ : Set (E 3)} (hδ : P.IsFace δ) (hdδ : faceDim δ = 1) :
    ∃ v : E 3, v ∈ P.vertices ∧ P.IsFace ({v} : Set (E 3)) ∧
      ({v} : Set (E 3)) ⊂ δ := by
  classical
  obtain ⟨v, hvP, hvδ⟩ := faccetta_ha_vertice P hδ
  have hsing : P.IsFace ({v} : Set (E 3)) := vertex_isFace P hvP
  refine ⟨v, hvP, hsing, ?_, ?_⟩
  · exact Set.singleton_subset_iff.mpr hvδ
  · intro hsub
    have hd : faceDim ({v} : Set (E 3)) = faceDim δ := by
      congr 1
      exact Set.Subset.antisymm (Set.singleton_subset_iff.mpr hvδ) hsub
    rw [faceDim_singleton, hdδ] at hd
    exact absurd hd (by norm_num)

/-- **OGNI SPIGOLO STA IN UNA BANDIERA**. -/
theorem bandiera_con_spigolo (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {δ : Set (E 3)} (hδ : P.IsFace δ) (hdδ : faceDim δ = 1) :
    ∃ F : P.Flag, F.face 1 = δ := by
  classical
  obtain ⟨A, hA, hdA, hδA⟩ := faccetta_sopra_spigolo P hfull hδ hdδ
  obtain ⟨v, _hvP, hsing, hvδ⟩ := vertice_sotto_spigolo P hδ hdδ
  refine ⟨⟨![({v} : Set (E 3)), δ, A], ?_, ?_, ?_⟩, rfl⟩
  · intro k
    fin_cases k
    · exact hsing
    · exact hδ
    · exact hA
  · intro k
    fin_cases k
    · exact faceDim_singleton v
    · exact hdδ
    · exact hdA
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;>
      first
        | exact hvδ
        | exact hδA
        | exact hvδ.trans hδA

/-- **TUTTI GLI SPIGOLI DI UN POLITOPO REGOLARE SONO CONGRUENTI**, senza
ipotesi residue: la lunghezza del lato è un invariante intrinseco. -/
theorem spigoli_congrui (P : ConvexPolytope 3) (hreg : P.IsRegular)
    {δ δ' : Set (E 3)} (hδ : P.IsFace δ) (hdδ : faceDim δ = 1)
    (hδ' : P.IsFace δ') (hdδ' : faceDim δ' = 1) :
    Metric.diam δ = Metric.diam δ' :=
  spigoli_congrui_di_bandiere P hreg
    (bandiera_con_spigolo P hreg.1 hδ hdδ)
    (bandiera_con_spigolo P hreg.1 hδ' hdδ')

end LeanEval.Geometry.PlatonicClassification
