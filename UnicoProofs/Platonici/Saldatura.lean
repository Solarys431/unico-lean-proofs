import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.Scala
import UnicoProofs.Platonici.ScalaTipo
import UnicoProofs.Platonici.Muovi
import UnicoProofs.Platonici.MuoviTipo
import UnicoProofs.Platonici.TrasportoFinale
import UnicoProofs.Platonici.Registro
import UnicoProofs.Platonici.RaggiTrasporto
import UnicoProofs.Platonici.Fattore
import UnicoProofs.Platonici.DiamPositivo
import UnicoProofs.Platonici.CorpiUguali
import UnicoProofs.Platonici.Assemblaggio

/-!
RIGIDITÀ — LA SALDATURA (19 lug 2026).

Il montaggio finale, in forma condizionale ai due lemmi sui raggi
trasportati (fascicolo 33). La sequenza è quella fissata con Daniele:

  fattore positivo dai diametri  →  omotetia  →  registrazione dalla Gram
  →  isometria  →  ventagli allineati  →  propagazione  →  hull uguali
  →  similarità.

Verso della registrazione: `registro_del_fan` manda i raggi del PRIMO
politopo su quelli del secondo, quindi per portare `Q` su `P` va invocato
con gli argomenti scambiati.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- **LA SALDATURA**: con i raggi trasportati (ipotesi che il fascicolo 33
scarica) e un vertice di partenza, i due politopi sono simili. -/
theorem similar_da_saldatura (P Q : ConvexPolytope 3) {p q : ℕ} [NeZero q]
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (hQ : Q.asFinite.IsCyclicallyRegularOfType p q)
    (hfullP : P.IsFullDim) (hfullQ : Q.IsFullDim)
    {a : ℝ} (ha : 0 < a)
    (g : Isom 3)
    -- il vertice comune e l'allineamento, forniti dal montaggio
    {v : E 3}
    (hvP : v ∈ P.vertices)
    (hvQ'' : v ∈ (muovi g (scala a (ne_of_gt ha) Q)).vertices)
    (hall : VentagliAllineati P (muovi g (scala a (ne_of_gt ha) Q)) q v)
    (hQ'' : (muovi g (scala a (ne_of_gt ha) Q)).asFinite.IsCyclicallyRegularOfType p q)
    (hfullQ'' : (muovi g (scala a (ne_of_gt ha) Q)).IsFullDim)
    (hdiamPQ : ∀ (w : E 3) (hwP : w ∈ P.vertices)
      (hwQ : w ∈ (muovi g (scala a (ne_of_gt ha) Q)).vertices)
      (DP : P.asFinite.CyclicVertexData w q)
      (DQ : (muovi g (scala a (ne_of_gt ha) Q)).asFinite.CyclicVertexData w q)
      (k : Fin q),
      Metric.diam (DP.faccetta k ∩ DP.faccetta (finRotate q k)) =
        Metric.diam (DQ.faccetta k ∩ DQ.faccetta (finRotate q k)))
    (hdiamQP : ∀ (w : E 3)
      (hwQ : w ∈ (muovi g (scala a (ne_of_gt ha) Q)).vertices)
      (hwP : w ∈ P.vertices)
      (DQ : (muovi g (scala a (ne_of_gt ha) Q)).asFinite.CyclicVertexData w q)
      (DP : P.asFinite.CyclicVertexData w q)
      (k : Fin q),
      Metric.diam (DQ.faccetta k ∩ DQ.faccetta (finRotate q k)) =
        Metric.diam (DP.faccetta k ∩ DP.faccetta (finRotate q k))) :
    Similar P Q := by
  have hcorpi : P.toSet = (muovi g (scala a (ne_of_gt ha) Q)).toSet :=
    corpi_uguali_dai_vertici P (muovi g (scala a (ne_of_gt ha) Q))
      hP hQ'' hfullP hfullQ'' hdiamPQ hdiamQP hvP hvQ'' hall
  exact similar_di_registro P Q ha g hcorpi

end LeanEval.Geometry.PlatonicClassification
