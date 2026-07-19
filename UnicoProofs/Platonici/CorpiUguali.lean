import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FanVertice
import UnicoProofs.Platonici.Propagazione
import UnicoProofs.Platonici.InduzioneFinale

/-!
RIGIDITÀ — I CORPI COINCIDONO, SENZA PASSARE DALLE FACCETTE (19 lug 2026).

L'ultima semplificazione. `coincidenza_da_ventagli` chiede che le
FACCETTE dei due ventagli coincidano come insiemi, e per quello servirebbe
il teorema di identificazione, che dipende dai testimoni d'orbita (falla
11). Ma non serve: l'allineamento dei ventagli porta già con sé
l'appartenenza del vertice a ENTRAMBI i politopi. Propagandolo lungo
Balinski si ottiene che ogni vertice di P è vertice di Q e viceversa, e i
corpi coincidono perché sono l'hull dei rispettivi vertici.

Nessun riferimento a faccette, testimoni d'orbita o `ell`: la falla 11
resta definitivamente fuori dalla catena.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- L'allineamento a un vertice ne dà l'appartenenza a entrambi. -/
theorem mem_di_allineati {P Q : ConvexPolytope 3} {q : ℕ} {v : E 3}
    (h : VentagliAllineati P Q q v) : v ∈ P.vertices ∧ v ∈ Q.vertices := by
  obtain ⟨hvP, hvQ, _, _, _⟩ := h
  exact ⟨hvP, hvQ⟩

/-- L'allineamento è simmetrico nei due politopi. -/
theorem allineati_symm {P Q : ConvexPolytope 3} {q : ℕ} {v : E 3}
    (h : VentagliAllineati P Q q v) : VentagliAllineati Q P q v := by
  obtain ⟨hvP, hvQ, DP, DQ, hdir⟩ := h
  exact ⟨hvQ, hvP, DQ, DP, hdir.symm⟩

/-- **OGNI VERTICE DI P È VERTICE DI Q**. -/
theorem vertici_inclusi (P Q : ConvexPolytope 3) {p q : ℕ} [NeZero q]
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (hQ : Q.asFinite.IsCyclicallyRegularOfType p q)
    (hfullP : P.IsFullDim)
    (hdiam : ∀ (v : E 3) (hvP : v ∈ P.vertices) (hvQ : v ∈ Q.vertices)
      (DP : P.asFinite.CyclicVertexData v q)
      (DQ : Q.asFinite.CyclicVertexData v q) (k : Fin q),
      Metric.diam (DP.faccetta k ∩ DP.faccetta (finRotate q k)) =
        Metric.diam (DQ.faccetta k ∩ DQ.faccetta (finRotate q k)))
    {v₀ : E 3} (hv₀P : v₀ ∈ P.vertices)
    (hall₀ : VentagliAllineati P Q q v₀) :
    ∀ w ∈ P.vertices, w ∈ Q.vertices := by
  intro w hwP
  exact (mem_di_allineati
    (allineati_ovunque P Q hP hQ hfullP hdiam hv₀P hall₀ hwP)).2

/-- **I CORPI COINCIDONO**: con un vertice allineato e le due
connettività, i vertici sono gli stessi e dunque anche gli hull. -/
theorem corpi_uguali_dai_vertici (P Q : ConvexPolytope 3) {p q : ℕ}
    [NeZero q]
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (hQ : Q.asFinite.IsCyclicallyRegularOfType p q)
    (hfullP : P.IsFullDim) (hfullQ : Q.IsFullDim)
    (hdiamPQ : ∀ (v : E 3) (hvP : v ∈ P.vertices) (hvQ : v ∈ Q.vertices)
      (DP : P.asFinite.CyclicVertexData v q)
      (DQ : Q.asFinite.CyclicVertexData v q) (k : Fin q),
      Metric.diam (DP.faccetta k ∩ DP.faccetta (finRotate q k)) =
        Metric.diam (DQ.faccetta k ∩ DQ.faccetta (finRotate q k)))
    (hdiamQP : ∀ (v : E 3) (hvQ : v ∈ Q.vertices) (hvP : v ∈ P.vertices)
      (DQ : Q.asFinite.CyclicVertexData v q)
      (DP : P.asFinite.CyclicVertexData v q) (k : Fin q),
      Metric.diam (DQ.faccetta k ∩ DQ.faccetta (finRotate q k)) =
        Metric.diam (DP.faccetta k ∩ DP.faccetta (finRotate q k)))
    {v₀ : E 3} (hv₀P : v₀ ∈ P.vertices) (hv₀Q : v₀ ∈ Q.vertices)
    (hall₀ : VentagliAllineati P Q q v₀) :
    P.toSet = Q.toSet := by
  classical
  have h1 : ∀ w ∈ P.vertices, w ∈ Q.vertices :=
    vertici_inclusi P Q hP hQ hfullP hdiamPQ hv₀P hall₀
  have h2 : ∀ w ∈ Q.vertices, w ∈ P.vertices :=
    vertici_inclusi Q P hQ hP hfullQ hdiamQP hv₀Q (allineati_symm hall₀)
  have hvert : P.vertices = Q.vertices := by
    ext x
    exact ⟨fun hx => h1 x hx, fun hx => h2 x hx⟩
  show convexHull ℝ ((P.vertices : Set (E 3))) =
    convexHull ℝ ((Q.vertices : Set (E 3)))
  rw [hvert]

end LeanEval.Geometry.PlatonicClassification
