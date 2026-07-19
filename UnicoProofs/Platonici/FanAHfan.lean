import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FanVertice
import UnicoProofs.Platonici.Chiusura

/-!
RIGIDITÀ — DAL VENTAGLIO ALL'IPOTESI DEL GATE 4 (19 lug 2026).

Il gate 4 (`chiusura_da_fan`) chiede: ogni faccetta di P per un vertice
comune è faccetta di Q. Il ventaglio la consegna quasi da sé: la
completezza locale (`D.complete`) dice che ogni faccetta per v è una
delle enumerate, e se le due enumerazioni coincidono termine a termine,
quella faccetta è anche faccetta di Q. Nessuna geometria qui: solo la
struttura del `CyclicVertexData`.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- **DAL VENTAGLIO ALL'IPOTESI DEL GATE 4**, a un singolo vertice. -/
theorem hfan_di_ventagli_uguali {P Q : ConvexPolytope 3} {q : ℕ}
    {v : E 3}
    (DP : P.asFinite.CyclicVertexData v q)
    (DQ : Q.asFinite.CyclicVertexData v q)
    (huguali : ∀ i : Fin q, DP.faccetta i = DQ.faccetta i) :
    ∀ F : Set (E 3),
      (P.IsFace F ∧ faceDim F = 2 ∧ v ∈ F) →
      (Q.IsFace F ∧ faceDim F = 2 ∧ v ∈ F) := by
  intro F hF
  obtain ⟨hFace, hdim, hvF⟩ := hF
  have hfacetP : P.asFinite.IsFacet F := ⟨hFace, hdim⟩
  obtain ⟨i, hFi⟩ := DP.complete F hfacetP hvF
  have hFQ : F = DQ.faccetta i := by rw [hFi, huguali i]
  have hfacetQ : Q.asFinite.IsFacet F := by
    rw [hFQ]
    exact DQ.isFacet i
  refine ⟨hfacetQ.1, hfacetQ.2, hvF⟩

/-- **LA COINCIDENZA DAI VENTAGLI**: se a ogni vertice comune i due
politopi hanno ventagli enumerati che coincidono termine a termine (nei
due versi), e c'è una faccetta comune di partenza, i corpi coincidono. -/
theorem coincidenza_da_ventagli (P Q : ConvexPolytope 3) {q : ℕ}
    (hfullP : P.IsFullDim) (hfullQ : Q.IsFullDim)
    (ventaglioP : ∀ v : E 3, v ∈ P.vertices → v ∈ Q.vertices →
      ∃ (DP : P.asFinite.CyclicVertexData v q)
        (DQ : Q.asFinite.CyclicVertexData v q),
        ∀ i : Fin q, DP.faccetta i = DQ.faccetta i)
    (A₀ : Set (E 3)) (hA₀ : FaccettaComune P Q A₀) :
    P.toSet = Q.toSet := by
  refine coincidenza_da_fan P Q hfullP hfullQ ?_ ?_ A₀ hA₀
  · intro v hvP hvQ F hF
    obtain ⟨DP, DQ, huguali⟩ := ventaglioP v hvP hvQ
    exact hfan_di_ventagli_uguali DP DQ huguali F hF
  · intro v hvQ hvP F hF
    obtain ⟨DP, DQ, huguali⟩ := ventaglioP v hvP hvQ
    have hsimm : ∀ i : Fin q, DQ.faccetta i = DP.faccetta i :=
      fun i => (huguali i).symm
    exact hfan_di_ventagli_uguali DQ DP hsimm F hF

end LeanEval.Geometry.PlatonicClassification
