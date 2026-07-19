import Mathlib
import Challenge
import Solution.Scala
import Solution.ScalaFacce
import Solution.ScalaTipo
import Solution.Muovi
import Solution.MuoviTipo
import Solution.TrasportoFinale
import Solution.VentagliEspliciti
import Solution.Registro
import Solution.Montaggio
import Solution.Saldatura
import Solution.Propagazione
import Solution.LatiUguali
import Solution.RegolareTrasporto
import Solution.Fattore
import Solution.DiamPositivo

/-!
RIGIDITÀ — LO SPIGOLO TRASPORTATO E IL PAREGGIO DEI LATI (19 lug 2026).

Il penultimo gradino: l'immagine di uno spigolo lungo le due
trasformazioni è ancora uno spigolo, e il suo diametro è il fattore per
quello di partenza. Con `esiste_fattore` i lati dei due politopi si
pareggiano, che è l'ipotesi di `hdiam_da_lati`.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- L'immagine di una faccia sotto omotetia è una faccia (forma sul
politopo del contratto). -/
theorem isFace_scala_conv {P : ConvexPolytope 3} {a : ℝ} (ha : a ≠ 0)
    {F : Set (E 3)} (hF : P.IsFace F) :
    (scala a ha P).IsFace ((fun x : E 3 => a • x) '' F) :=
  isFace_scala ha hF

/-- Il rango di una faccia si conserva sotto omotetia. -/
theorem faceDim_scala {a : ℝ} (ha : a ≠ 0) {F : Set (E 3)}
    (hdF : faceDim F = 1) :
    faceDim ((fun x : E 3 => a • x) '' F) = 1 := by
  show Module.finrank ℝ (vectorSpan ℝ ((fun x : E 3 => a • x) '' F)) = 1
  rw [finrank_vectorSpan_smul a ha]
  exact hdF

/-- Il rango di una faccia si conserva sotto isometria. -/
theorem faceDim_muovi (g : Isom 3) {F : Set (E 3)} (hdF : faceDim F = 1) :
    faceDim ((⇑g) '' F) = 1 := by
  rw [faceDim_image_isom]
  exact hdF

/-- **LO SPIGOLO TRASPORTATO**: l'immagine di uno spigolo lungo omotetia e
isometria è uno spigolo del politopo trasformato, di diametro `a` volte
quello di partenza. -/
theorem spigolo_trasportato (Q : ConvexPolytope 3) {a : ℝ} (ha : 0 < a)
    (g : Isom 3) {ε : Set (E 3)}
    (hε : Q.IsFace ε) (hdε : faceDim ε = 1) :
    (muovi g (scala a (ne_of_gt ha) Q)).IsFace
        ((⇑g) '' ((fun x : E 3 => a • x) '' ε)) ∧
      faceDim ((⇑g) '' ((fun x : E 3 => a • x) '' ε)) = 1 ∧
      Metric.diam ((⇑g) '' ((fun x : E 3 => a • x) '' ε)) =
        a * Metric.diam ε := by
  refine ⟨?_, ?_, diam_spigolo_trasportato ha g ε⟩
  · exact isFace_muovi g (isFace_scala_conv (ne_of_gt ha) hε)
  · exact faceDim_muovi g (faceDim_scala (ne_of_gt ha) hdε)

/-- **I LATI SI PAREGGIANO**: con il fattore di `esiste_fattore`, uno
spigolo di `P` e uno del politopo normalizzato hanno lo stesso
diametro. -/
theorem lati_pareggiati (P Q : ConvexPolytope 3)
    (hregP : P.IsRegular) (hregQ : Q.IsRegular)
    {a : ℝ} (ha : 0 < a)
    (hfatt : ∀ (δ ε : Set (E 3)), P.IsFace δ → faceDim δ = 1 →
      Q.IsFace ε → faceDim ε = 1 →
      Metric.diam δ = a * Metric.diam ε)
    (g : Isom 3) :
    ∃ (δ₀ ε₀ : Set (E 3)),
      P.IsFace δ₀ ∧ faceDim δ₀ = 1 ∧
      (muovi g (scala a (ne_of_gt ha) Q)).IsFace ε₀ ∧ faceDim ε₀ = 1 ∧
      Metric.diam δ₀ = Metric.diam ε₀ := by
  obtain ⟨δ, hδ, hdδ⟩ := esiste_spigolo P hregP.1
  obtain ⟨ε, hε, hdε⟩ := esiste_spigolo Q hregQ.1
  obtain ⟨hfaceε', hdimε', hdiamε'⟩ := spigolo_trasportato Q ha g hε hdε
  refine ⟨δ, (⇑g) '' ((fun x : E 3 => a • x) '' ε), hδ, hdδ,
    hfaceε', hdimε', ?_⟩
  rw [hdiamε']
  exact hfatt δ ε hδ hdδ hε hdε

end LeanEval.Geometry.PlatonicClassification
