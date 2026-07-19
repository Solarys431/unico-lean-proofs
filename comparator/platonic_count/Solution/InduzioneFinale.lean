import Mathlib
import Challenge
import Solution.FacceConnesse
import Solution.Balinski
import Solution.FanAHfan
import Solution.Propagazione

/-!
RIGIDITÀ — L'INDUZIONE FINALE (19 lug 2026).

L'allineamento dei ventagli si propaga da un vertice a ogni altro lungo
la connettività di Balinski. Da qui, `coincidenza_da_ventagli` dà
l'uguaglianza dei corpi: è l'ultimo anello della catena locale.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- **LA PROPAGAZIONE LUNGO UN CAMMINO**. -/
theorem allineati_lungo_cammino (P Q : ConvexPolytope 3) {p q : ℕ}
    [NeZero q]
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (hQ : Q.asFinite.IsCyclicallyRegularOfType p q)
    (hdiam : ∀ (v : E 3) (hvP : v ∈ P.vertices) (hvQ : v ∈ Q.vertices)
      (DP : P.asFinite.CyclicVertexData v q)
      (DQ : Q.asFinite.CyclicVertexData v q) (k : Fin q),
      Metric.diam (DP.faccetta k ∩ DP.faccetta (finRotate q k)) =
        Metric.diam (DQ.faccetta k ∩ DQ.faccetta (finRotate q k)))
    {v w : E 3} (hall : VentagliAllineati P Q q v)
    (hcam : Relation.ReflTransGen (AdiacentiVertici P) v w) :
    VentagliAllineati P Q q w := by
  induction hcam with
  | refl => exact hall
  | tail _ hstep ih => exact allineati_al_vicino P Q hP hQ hdiam ih hstep

/-- **VENTAGLI ALLINEATI OVUNQUE**: da un solo vertice allineato, e dalla
connettività di Balinski, l'allineamento si estende a tutti i vertici. -/
theorem allineati_ovunque (P Q : ConvexPolytope 3) {p q : ℕ} [NeZero q]
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (hQ : Q.asFinite.IsCyclicallyRegularOfType p q)
    (hfullP : P.IsFullDim)
    (hdiam : ∀ (v : E 3) (hvP : v ∈ P.vertices) (hvQ : v ∈ Q.vertices)
      (DP : P.asFinite.CyclicVertexData v q)
      (DQ : Q.asFinite.CyclicVertexData v q) (k : Fin q),
      Metric.diam (DP.faccetta k ∩ DP.faccetta (finRotate q k)) =
        Metric.diam (DQ.faccetta k ∩ DQ.faccetta (finRotate q k)))
    {v₀ : E 3} (hv₀P : v₀ ∈ P.vertices)
    (hall₀ : VentagliAllineati P Q q v₀)
    {w : E 3} (hwP : w ∈ P.vertices) :
    VentagliAllineati P Q q w :=
  allineati_lungo_cammino P Q hP hQ hdiam hall₀
    (balinski_light P hfullP v₀ hv₀P w hwP)

/-- **L'UGUAGLIANZA DEI CORPI**: un vertice allineato basta. -/
theorem corpi_uguali_da_un_vertice (P Q : ConvexPolytope 3) {p q : ℕ}
    [NeZero q]
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (hQ : Q.asFinite.IsCyclicallyRegularOfType p q)
    (hfullP : P.IsFullDim) (hfullQ : Q.IsFullDim)
    (hdiam : ∀ (v : E 3) (hvP : v ∈ P.vertices) (hvQ : v ∈ Q.vertices)
      (DP : P.asFinite.CyclicVertexData v q)
      (DQ : Q.asFinite.CyclicVertexData v q) (k : Fin q),
      Metric.diam (DP.faccetta k ∩ DP.faccetta (finRotate q k)) =
        Metric.diam (DQ.faccetta k ∩ DQ.faccetta (finRotate q k)))
    {v₀ : E 3} (hv₀P : v₀ ∈ P.vertices)
    (hall₀ : VentagliAllineati P Q q v₀)
    (hfacce : ∀ i : Fin q, ∀ (v : E 3) (hvP : v ∈ P.vertices)
      (hvQ : v ∈ Q.vertices)
      (DP : P.asFinite.CyclicVertexData v q)
      (DQ : Q.asFinite.CyclicVertexData v q),
      dir P.asFinite v DP = dir Q.asFinite v DQ →
      DP.faccetta i = DQ.faccetta i)
    (A₀ : Set (E 3)) (hA₀ : FaccettaComune P Q A₀) :
    P.toSet = Q.toSet := by
  refine coincidenza_da_ventagli (q := q) P Q hfullP hfullQ ?_ A₀ hA₀
  intro v hvP hvQ
  obtain ⟨_, _, DP, DQ, hdir⟩ :=
    allineati_ovunque P Q hP hQ hfullP hdiam hv₀P hall₀ hvP
  exact ⟨DP, DQ, fun i => hfacce i v hvP hvQ DP DQ hdir⟩

end LeanEval.Geometry.PlatonicClassification
