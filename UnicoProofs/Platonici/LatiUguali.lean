import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.Scala
import UnicoProofs.Platonici.ScalaFacce
import UnicoProofs.Platonici.Muovi
import UnicoProofs.Platonici.MuoviTipo
import UnicoProofs.Platonici.TrasportoFinale
import UnicoProofs.Platonici.SpigoliCongrui
import UnicoProofs.Platonici.BandieraSpigolo
import UnicoProofs.Platonici.DiamPositivo
import UnicoProofs.Platonici.Fattore
import UnicoProofs.Platonici.RegolareTrasporto
import UnicoProofs.Platonici.LatoSemipiano

/-!
RIGIDITÀ — I LATI SI PAREGGIANO (19 lug 2026).

L'ultima ipotesi del montaggio: dopo la normalizzazione, gli spigoli dei
due politopi hanno lo stesso diametro. Segue da tre fatti già certificati:
il diametro degli spigoli è costante in un politopo regolare
(`spigoli_congrui`), la regolarità sopravvive alle due trasformazioni
(`isRegular_scala`, `isRegular_muovi`), e il diametro scala del fattore
ed è invariante per isometrie (`diam_smul_image`, `diam_image_isom`).
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- Uno spigolo del ventaglio è una faccia di rango 1. -/
theorem spigolo_fan_faccia (P : ConvexPolytope 3) {v : E 3} {q : ℕ}
    (hq : 3 ≤ q) (D : P.asFinite.CyclicVertexData v q) (k : Fin q) :
    P.IsFace (D.faccetta k ∩ D.faccetta (finRotate q k)) ∧
      faceDim (D.faccetta k ∩ D.faccetta (finRotate q k)) = 1 :=
  ⟨(adiacenza_passo_uno_locale P hq D k).1,
   (adiacenza_passo_uno_locale P hq D k).2.1⟩

/-- **L'IPOTESI SUI DIAMETRI, SCARICATA**: se un qualunque spigolo di `P`
e un qualunque spigolo di `R` hanno lo stesso diametro, allora lo hanno
tutti gli spigoli dei rispettivi ventagli. -/
theorem hdiam_da_lati (P R : ConvexPolytope 3)
    (hregP : P.IsRegular) (hregR : R.IsRegular) {q : ℕ} (hq : 3 ≤ q)
    {δ₀ ε₀ : Set (E 3)}
    (hδ₀ : P.IsFace δ₀) (hdδ₀ : faceDim δ₀ = 1)
    (hε₀ : R.IsFace ε₀) (hdε₀ : faceDim ε₀ = 1)
    (hlato : Metric.diam δ₀ = Metric.diam ε₀) :
    ∀ (v : E 3) (_hvP : v ∈ P.vertices) (_hvR : v ∈ R.vertices)
      (DP : P.asFinite.CyclicVertexData v q)
      (DR : R.asFinite.CyclicVertexData v q) (k : Fin q),
      Metric.diam (DP.faccetta k ∩ DP.faccetta (finRotate q k)) =
        Metric.diam (DR.faccetta k ∩ DR.faccetta (finRotate q k)) := by
  intro v _hvP _hvR DP DR k
  obtain ⟨hfP, hdP⟩ := spigolo_fan_faccia P hq DP k
  obtain ⟨hfR, hdR⟩ := spigolo_fan_faccia R hq DR k
  rw [spigoli_congrui P hregP hfP hdP hδ₀ hdδ₀,
    spigoli_congrui R hregR hfR hdR hε₀ hdε₀]
  exact hlato

/-- Il diametro di uno spigolo trasportato: scala del fattore e resta
invariante sotto isometria. -/
theorem diam_spigolo_trasportato {a : ℝ} (ha : 0 < a) (g : Isom 3)
    (s : Set (E 3)) :
    Metric.diam ((⇑g) '' ((fun x : E 3 => a • x) '' s)) =
      a * Metric.diam s := by
  rw [diam_image_isom]
  exact diam_smul_image a ha s

end LeanEval.Geometry.PlatonicClassification
