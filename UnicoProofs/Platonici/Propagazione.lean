import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FanVertice
import UnicoProofs.Platonici.VerticiFaccette
import UnicoProofs.Platonici.FacceConnesse
import UnicoProofs.Platonici.Chiusura
import UnicoProofs.Platonici.PassoInduttivo
import UnicoProofs.Platonici.Orientazione
import UnicoProofs.Platonici.Registro
import UnicoProofs.Platonici.VicinoEsplicito

/-!
RIGIDITÀ — L'ITERAZIONE LUNGO IL GRAFO DEI VERTICI (19 lug 2026).

L'ultimo anello. Il passo induttivo (`ventagli_uguali_al_vicino_scarico`,
incondizionato) porta l'allineamento dei ventagli da un vertice al suo
vicino lungo un dato spigolo del ventaglio. Qui lo si itera lungo la
connettività di Balinski, per ottenere l'allineamento a OGNI vertice
comune — che è l'ipotesi di `coincidenza_da_ventagli`.

Il punto tecnico: il vicino generico (quello della relazione
`AdiacentiVertici`) va identificato con quello prodotto dal ventaglio.
Passa dal fatto che un vertice del politopo contenuto in uno spigolo ne è
un estremo (`vertici_faccia_estremi`).
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- L'allineamento dei ventagli a un vertice. -/
def VentagliAllineati (P Q : ConvexPolytope 3) (q : ℕ) (v : E 3) : Prop :=
  ∃ (_hvP : v ∈ P.vertices) (_hvQ : v ∈ Q.vertices)
    (DP : P.asFinite.CyclicVertexData v q)
    (DQ : Q.asFinite.CyclicVertexData v q),
    dir P.asFinite v DP = dir Q.asFinite v DQ

/-- Un vertice del politopo contenuto in un segmento-faccia ne è un
estremo. -/
theorem vertice_in_segmento_estremo (P : ConvexPolytope 3)
    {δ : Set (E 3)} (hδ : P.IsFace δ) {x y z : E 3}
    (hseg : δ = segment ℝ x y) (hz : z ∈ P.vertices) (hzδ : z ∈ δ) :
    z = x ∨ z = y := by
  classical
  -- z è un estremo di δ, e gli estremi di un segmento sono i suoi capi
  have hzfilter : z ∈ P.vertices.filter (· ∈ δ) :=
    Finset.mem_filter.mpr ⟨hz, hzδ⟩
  have hzext : z ∈ δ.extremePoints ℝ := by
    have h1 : z ∈ (((facePolytope P hδ).vertices : Finset (E 3)) :
        Set (E 3)) := Finset.mem_coe.mpr hzfilter
    rw [vertici_faccia_estremi P hδ] at h1
    exact h1
  rw [hseg] at hzext
  by_contra hcon
  push_neg at hcon
  obtain ⟨hzx, hzy⟩ := hcon
  -- un punto interno del segmento non è estremo
  have hzmem : z ∈ segment ℝ x y := by
    rw [← hseg]; exact hzδ
  obtain ⟨a, b, ha, hb, hab, hz'⟩ := hzmem
  have hane : a ≠ 0 := by
    intro h
    apply hzy
    rw [← hz', h, zero_smul, zero_add]
    have : b = 1 := by linarith
    rw [this, one_smul]
  have hbne : b ≠ 0 := by
    intro h
    apply hzx
    rw [← hz', h, zero_smul, add_zero]
    have : a = 1 := by linarith
    rw [this, one_smul]
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hane)
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbne)
  have hxy : x ≠ y := by
    intro h
    apply hzx
    rw [← hz', h]
    have : a • y + b • y = (a + b) • y := (add_smul a b y).symm
    rw [this, hab, one_smul]
  -- z è combinazione strettamente convessa di due punti distinti del
  -- segmento, dunque non è estremo
  have hxseg : x ∈ segment ℝ x y := left_mem_segment ℝ x y
  have hyseg : y ∈ segment ℝ x y := right_mem_segment ℝ x y
  have hxz := hzext.2 hxseg hyseg ⟨a, b, hapos, hbpos, hab, hz'⟩
  exact hzx hxz.symm

/-- **LA PROPAGAZIONE AL VICINO GENERICO**: se i ventagli sono allineati a
`v` e `w` gli è adiacente, allora sono allineati a `w`. -/
theorem allineati_al_vicino (P Q : ConvexPolytope 3) {p q : ℕ} [NeZero q]
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (hQ : Q.asFinite.IsCyclicallyRegularOfType p q)
    (hdiam : ∀ (v : E 3) (hvP : v ∈ P.vertices) (hvQ : v ∈ Q.vertices)
      (DP : P.asFinite.CyclicVertexData v q)
      (DQ : Q.asFinite.CyclicVertexData v q) (k : Fin q),
      Metric.diam (DP.faccetta k ∩ DP.faccetta (finRotate q k)) =
        Metric.diam (DQ.faccetta k ∩ DQ.faccetta (finRotate q k)))
    {v w : E 3} (hall : VentagliAllineati P Q q v)
    (hadj : AdiacentiVertici P v w) :
    VentagliAllineati P Q q w := by
  classical
  obtain ⟨hvP, hvQ, DP, DQ, hdir⟩ := hall
  obtain ⟨_, hwP, δ, hδ, hdδ, hvδ, hwδ, hvw⟩ := hadj
  -- lo spigolo δ è uno del ventaglio
  have hq : 3 ≤ q := hP.2.2.1
  obtain ⟨i, hi⟩ := spigolo_adiacente_suriettiva P hq DP
    ⟨δ, hδ, hdδ, hvδ⟩
  -- il vicino prodotto dal ventaglio lungo i
  obtain ⟨w', hw'P, hw'Q, hw'ne, hw'edge, hsegP, _hedgeQ⟩ :=
    vertice_adiacente_comune P Q hP hQ hvP hvQ DP DQ hdir
      (fun k => hdiam v hvP hvQ DP DQ k) i
  -- δ coincide con quello spigolo, dunque w = w'
  have hδeq : δ = DP.faccetta i ∩ DP.faccetta (finRotate q i) := by
    have := congrArg Subtype.val hi
    simpa using this
  have hwseg : w ∈ segment ℝ v w' := by
    rw [← hsegP, ← hδeq]
    exact hwδ
  have hcase := vertice_in_segmento_estremo P hδ
    (by rw [hδeq, hsegP]) hwP hwδ
  have hww' : w = w' := by
    rcases hcase with h | h
    · exact absurd h.symm hvw
    · exact h
  subst hww'
  -- il passo induttivo, ora con il vicino ESPLICITO
  obtain ⟨w'', hw''P, hw''Q, EP, EQ, hdirw, hw''ne, hsegw⟩ :=
    ventagli_uguali_al_vicino_esplicito P Q hP hQ hvP hvQ DP DQ hdir
      (fun k => hdiam v hvP hvQ DP DQ k) i
  -- w'' e w' sono entrambi l'altro estremo dello stesso spigolo
  have hww'' : w = w'' := by
    have hcase2 := vertice_in_segmento_estremo P hδ
      (by rw [hδeq, hsegw]) hwP hwδ
    rcases hcase2 with h | h
    · exact absurd h hvw.symm
    · exact h
  subst hww''
  exact ⟨hw''P, hw''Q, EP, EQ, hdirw⟩

end LeanEval.Geometry.PlatonicClassification
