-- NON RIUSCITO: spigolo_eq_segmento perche' IsRegularFacet permette a rho
-- di percorrere una stella (per p = 5 il suo passo puo' essere una diagonale),
-- quindi ell non e' necessariamente la lunghezza di uno spigolo.
-- NON RIUSCITO: semipiano_comune_di_adiacenti perche' le ipotesi date sono
-- invarianti riflettendo Q nel lato comune, mentre la conclusione non lo e'.

import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.Fondamenta
import UnicoProofs.Platonici.FanVertice
import UnicoProofs.Platonici.Diamante
import UnicoProofs.Platonici.ConnessioneVentaglio
import UnicoProofs.Platonici.PianoDaiRaggi
import UnicoProofs.Platonici.FaccettaDeterminata

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- Due faccette distinte di rango due con due punti comuni distinti si
intersecano in una faccia di rango uno. -/
theorem intersezione_faccette_rango_uno (P : ConvexPolytope 3)
    {A B : Set (E 3)}
    (hA : P.IsFace A) (hdA : faceDim A = 2)
    (hB : P.IsFace B) (hdB : faceDim B = 2)
    (hAB : A ≠ B) {v x : E 3}
    (hvA : v ∈ A) (hvB : v ∈ B)
    (hxA : x ∈ A) (hxB : x ∈ B) (hxv : x ≠ v) :
    P.IsFace (A ∩ B) ∧ faceDim (A ∩ B) = 1 := by
  have hint : P.IsFace (A ∩ B) :=
    ⟨hA.1.inter hB.1, ⟨v, hvA, hvB⟩⟩
  have hge : 1 ≤ Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) :=
    finrank_pos_di_due ⟨hvA, hvB⟩ ⟨hxA, hxB⟩ hxv
  have hproper : A ∩ B ⊂ A := by
    refine ⟨Set.inter_subset_left, fun hsup => ?_⟩
    have hAleB : A ⊆ B := fun z hz => (hsup hz).2
    have hss : A ⊂ B :=
      ⟨hAleB, fun hBA => hAB (Set.Subset.antisymm hAleB hBA)⟩
    have hlt := faceDim_lt_of_ssubset P hA hB hss
    omega
  have hlt := faceDim_lt_of_ssubset P hint hA hproper
  refine ⟨hint, ?_⟩
  show Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) = 1
  have hlt' : Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) < 2 := by
    have hlt0 : Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) <
        Module.finrank ℝ (vectorSpan ℝ A) := hlt
    have hdA' : Module.finrank ℝ (vectorSpan ℝ A) = 2 := hdA
    omega
  omega

/-- L'intersezione di due faccette consecutive e' una faccia di rango uno
passante per il vertice marcato. -/
theorem adiacenza_passo_uno_locale (P : ConvexPolytope 3)
    {v : E 3} {q : ℕ} (hq : 3 ≤ q)
    (D : P.asFinite.CyclicVertexData v q) (i : Fin q) :
    P.IsFace (D.faccetta i ∩ D.faccetta (finRotate q i)) ∧
      faceDim (D.faccetta i ∩ D.faccetta (finRotate q i)) = 1 ∧
      v ∈ D.faccetta i ∩ D.faccetta (finRotate q i) := by
  let A := D.faccetta i
  let B := D.faccetta (finRotate q i)
  have hA := (P.asFinite_isFacet_iff A).1 (D.isFacet i)
  have hB := (P.asFinite_isFacet_iff B).1 (D.isFacet (finRotate q i))
  have hne : A ≠ B := by
    intro heq
    apply _root_.finRotate_ne_self (by omega : 2 ≤ q) i
    exact D.distinte heq.symm
  obtain ⟨x, hxv, hx⟩ := D.spigolo i
  have hedge := intersezione_faccette_rango_uno P
    hA.1 hA.2 hB.1 hB.2 hne
    (D.mem_v i) (D.mem_v (finRotate q i)) hx.1 hx.2 hxv
  exact ⟨hedge.1, hedge.2, D.mem_v i, D.mem_v (finRotate q i)⟩

/-- L'intersezione di due faccette consecutive del certificato, impacchettata
come spigolo del politopo passante per v. -/
noncomputable def spigolo_adiacente (P : ConvexPolytope 3)
    {v : E 3} {q : ℕ} (hq : 3 ≤ q)
    (D : P.asFinite.CyclicVertexData v q) (i : Fin q) : SpigoloPer P v :=
  ⟨D.faccetta i ∩ D.faccetta (finRotate q i),
    (adiacenza_passo_uno_locale P hq D i).1,
    (adiacenza_passo_uno_locale P hq D i).2.1,
    (adiacenza_passo_uno_locale P hq D i).2.2⟩

@[simp] theorem spigolo_adiacente_val (P : ConvexPolytope 3)
    {v : E 3} {q : ℕ} (hq : 3 ≤ q)
    (D : P.asFinite.CyclicVertexData v q) (i : Fin q) :
    (spigolo_adiacente P hq D i).val =
      D.faccetta i ∩ D.faccetta (finRotate q i) := rfl

/-- Il secondo estremo dello spigolo consecutivo sta, con parametro
strettamente positivo, sul raggio unitario scelto da `dir`. -/
theorem altro_estremo_sul_raggio (P : ConvexPolytope 3) {p q : ℕ}
    (h : P.asFinite.IsCyclicallyRegularOfType p q) {v : E 3}
    (hv : v ∈ P.vertices) (D : P.asFinite.CyclicVertexData v q)
    (i : Fin q) :
    ∃ t : ℝ, 0 < t ∧
      SpigoloPer.altro P v hv
          (spigolo_adiacente P h.2.2.1 D i) =
        v + t • dir P.asFinite v D i := by
  classical
  let edge : SpigoloPer P v := spigolo_adiacente P h.2.2.1 D i
  let a : E 3 := SpigoloPer.altro P v hv edge
  let x : E 3 := punto P.asFinite v D i
  have haspec := SpigoloPer.altro_spec P v hv edge
  have hane : a ≠ v := haspec.2.2.1
  have hapos : 0 < ‖a - v‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hane)
  have hxspec := punto_spec P.asFinite v D i
  have hxedge : x ∈ edge.val := by
    simpa [edge, x] using hxspec.2
  have hxseg : x ∈ segment ℝ v a := by
    rw [← haspec.2.2.2]
    exact hxedge
  rw [segment_eq_image_lineMap] at hxseg
  obtain ⟨s, hs, hxs⟩ := hxseg
  have hspos : 0 < s := by
    have hsne : s ≠ 0 := by
      intro hs0
      apply hxspec.1
      have hxv : x = v := by
        rw [← hxs, hs0]
        simp [AffineMap.lineMap_apply]
      simpa [x] using hxv
    exact lt_of_le_of_ne hs.1 (Ne.symm hsne)
  have hrad : x - v = s • (a - v) := by
    rw [← hxs]
    simp [AffineMap.lineMap_apply]
  have hxnorm : ‖x - v‖ = s * ‖a - v‖ := by
    rw [hrad, norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
  refine ⟨‖a - v‖, hapos, ?_⟩
  change a = v + ‖a - v‖ •
    (‖x - v‖⁻¹ • (x - v))
  rw [hxnorm, hrad, smul_smul, smul_smul]
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hnormne : ‖a - v‖ ≠ 0 := ne_of_gt hapos
  have hcoef : ‖a - v‖ * ((s * ‖a - v‖)⁻¹ * s) = 1 := by
    field_simp
  have hcoef' : ‖a - v‖ * (s * ‖a - v‖)⁻¹ * s = 1 := by
    calc
      ‖a - v‖ * (s * ‖a - v‖)⁻¹ * s =
          ‖a - v‖ * ((s * ‖a - v‖)⁻¹ * s) := by ring
      _ = 1 := hcoef
  rw [hcoef', one_smul]
  abel

/-- Forma piu' direttamente riusabile: lo spigolo intero e' il segmento
tagliato sul raggio `dir` da un unico parametro positivo (non identificabile
con `ell` dal solo contratto di `IsRegularFacet`). -/
theorem spigolo_eq_segmento_sul_raggio (P : ConvexPolytope 3) {p q : ℕ}
    (h : P.asFinite.IsCyclicallyRegularOfType p q) {v : E 3}
    (hv : v ∈ P.vertices) (D : P.asFinite.CyclicVertexData v q)
    (i : Fin q) :
    ∃ t : ℝ, 0 < t ∧
      D.faccetta i ∩ D.faccetta (finRotate q i) =
        segment ℝ v (v + t • dir P.asFinite v D i) := by
  obtain ⟨t, ht, ha⟩ := altro_estremo_sul_raggio P h hv D i
  refine ⟨t, ht, ?_⟩
  let edge : SpigoloPer P v := spigolo_adiacente P h.2.2.1 D i
  have hedge := (SpigoloPer.altro_spec P v hv edge).2.2.2
  have hedge' : D.faccetta i ∩ D.faccetta (finRotate q i) =
      segment ℝ v (SpigoloPer.altro P v hv edge) := by
    simpa [edge] using hedge
  have ha' : SpigoloPer.altro P v hv edge =
      v + t • dir P.asFinite v D i := by
    simpa [edge] using ha
  rw [hedge', ha']

/-- Fallback esplicito per il terzo ingrediente: quando il funzionale con
tutte le cinque proprieta' richieste e' disponibile, esso e' esattamente un
testimone di `SemipianoComune`. -/
theorem semipiano_da_funzionale (P Q : ConvexPolytope 3) {p q : ℕ}
    (_hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (_hQ : Q.asFinite.IsCyclicallyRegularOfType p q)
    {v : E 3} (_hvP : v ∈ P.vertices) (_hvQ : v ∈ Q.vertices)
    (DP : P.asFinite.CyclicVertexData v q)
    (DQ : Q.asFinite.CyclicVertexData v q)
    (i : Fin q) {ell : ℝ}
    (_hdir : dir P.asFinite v DP = dir Q.asFinite v DQ)
    (_hpiano : affineSpan ℝ (DP.faccetta i) = affineSpan ℝ (DQ.faccetta i))
    (_hlatoP : DP.faccetta i ∩ DP.faccetta (finRotate q i) =
      segment ℝ v (v + ell • dir P.asFinite v DP i))
    (_hlatoQ : DQ.faccetta i ∩ DQ.faccetta (finRotate q i) =
      segment ℝ v (v + ell • dir Q.asFinite v DQ i))
    (hfun : ∃ g : E 3 →L[ℝ] ℝ,
      g v = g (v + ell • dir P.asFinite v DP i) ∧
      (∀ z ∈ DP.faccetta i, g v ≤ g z) ∧
      (∀ z ∈ DQ.faccetta i, g v ≤ g z) ∧
      {z ∈ DP.faccetta i | g z = g v} =
        segment ℝ v (v + ell • dir P.asFinite v DP i) ∧
      {z ∈ DQ.faccetta i | g z = g v} =
        segment ℝ v (v + ell • dir P.asFinite v DP i)) :
    SemipianoComune (DP.faccetta i) (DQ.faccetta i) v
      (v + ell • dir P.asFinite v DP i) := by
  exact hfun

end LeanEval.Geometry.PlatonicClassification
