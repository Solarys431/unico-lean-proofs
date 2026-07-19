import Mathlib
import Challenge
import Solution.Scala
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
import Solution.SpigoloTrasportato
import Solution.RegolareTrasporto
import Solution.Fattore
import Solution.Riduzione
import Solution.TipiTestimoni
import Solution.Estrazione

/-!
RIGIDITÀ — LA CHIUSURA (19 lug 2026).

L'assemblaggio finale. Due politopi regolari dello stesso tipo ciclico
sono simili, e con questo il conteggio del benchmark è chiuso:

    platonicCount 3 = 5.

La catena, tutta su invarianti canonici:
  fattore dai diametri → omotetia → registrazione dalla Gram → isometria
  → ventagli allineati → propagazione sui vertici → hull uguali → Similar.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- **LA RIGIDITÀ**: due politopi regolari dello stesso tipo ciclico sono
simili. -/
theorem rigidita_stesso_tipo (P Q : ConvexPolytope 3) {p q : ℕ} [NeZero q]
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (hQ : Q.asFinite.IsCyclicallyRegularOfType p q)
    (hregP : P.IsRegular) (hregQ : Q.IsRegular) :
    Similar P Q := by
  classical
  -- 1. il fattore di normalizzazione, positivo
  obtain ⟨a, ha, hfatt⟩ := esiste_fattore P Q hregP hregQ
  -- 2. il politopo scalato conserva tipo e regolarità
  have hQ' : (scala a (ne_of_gt ha) Q).asFinite.IsCyclicallyRegularOfType p q :=
    cyclicallyRegular_scala Q ha hQ
  have hregQ' : (scala a (ne_of_gt ha) Q).IsRegular :=
    isRegular_scala Q ha hregQ
  -- 3. vertici e ventagli
  obtain ⟨v, hvP⟩ := esiste_vertice P
  obtain ⟨DP⟩ := esiste_ventaglio P hP hvP
  obtain ⟨v', hv'⟩ := esiste_vertice (scala a (ne_of_gt ha) Q)
  obtain ⟨DQ'⟩ := esiste_ventaglio (scala a (ne_of_gt ha) Q) hQ' hv'
  -- 4. la registrazione: porta il ventaglio scalato su quello di P
  have hspan := span_raggi_top (scala a (ne_of_gt ha) Q) hregQ'.1 hQ' hv' DQ'
  obtain ⟨g, hgv, hgreg⟩ :=
    registro_del_fan (scala a (ne_of_gt ha) Q) P hQ' hP hv' hvP DQ' DP hspan
  -- 5. il politopo mosso, con il suo ventaglio esplicito
  obtain ⟨D'', hfacce''⟩ :=
    cyclicVertexData_muovi_esplicito (scala a (ne_of_gt ha) Q) g DQ'
  have hQ'' : (muovi g (scala a (ne_of_gt ha) Q)).asFinite.IsCyclicallyRegularOfType p q :=
    cyclicallyRegular_muovi (scala a (ne_of_gt ha) Q) g hQ'
  have hregQ'' : (muovi g (scala a (ne_of_gt ha) Q)).IsRegular :=
    isRegular_muovi (scala a (ne_of_gt ha) Q) g hregQ'
  -- 6. i raggi coincidono, dunque i ventagli sono allineati
  have hall := allineamento_da_registro (scala a (ne_of_gt ha) Q) P hQ'
    hv' hvP DQ' DP hgv hgreg D'' hfacce''
  -- si sostituisce il vertice registrato ovunque, invece di riscriverlo
  subst hgv
  have hvQ'' : g v' ∈ (muovi g (scala a (ne_of_gt ha) Q)).vertices :=
    mem_vertices_muovi g (scala a (ne_of_gt ha) Q) hv'
  have hallineati :
      VentagliAllineati P (muovi g (scala a (ne_of_gt ha) Q)) q (g v') :=
    ⟨hvP, hvQ'', DP, D'', funext (fun i => (hall i).symm)⟩
  -- 7. i lati pareggiati danno l'ipotesi sui diametri
  obtain ⟨δ₀, ε₀, hδ₀, hdδ₀, hε₀, hdε₀, hlato⟩ :=
    lati_pareggiati P Q hregP hregQ ha hfatt g
  have hq : 3 ≤ q := hP.2.2.1
  have hdiamPQ := hdiam_da_lati P (muovi g (scala a (ne_of_gt ha) Q))
    hregP hregQ'' hq hδ₀ hdδ₀ hε₀ hdε₀ hlato
  have hdiamQP := hdiam_da_lati (muovi g (scala a (ne_of_gt ha) Q)) P
    hregQ'' hregP hq hε₀ hdε₀ hδ₀ hdδ₀ hlato.symm
  -- 8. la saldatura
  exact similar_da_saldatura P Q hP hQ hregP.1 hregQ.1 ha g hvP hvQ''
    hallineati hQ'' hregQ''.1 hdiamPQ hdiamQP

end LeanEval.Geometry.PlatonicClassification
