import Mathlib
import UnicoProofs.Platonici.Fondamenta
import UnicoProofs.Platonici.Diamante
import UnicoProofs.Platonici.SecondaFaccetta
import UnicoProofs.Platonici.OrbitaFan
import UnicoProofs.Platonici.Immagini
import UnicoProofs.Platonici.ScaricoSpigolo
import UnicoProofs.Platonici.ConnessioneVentaglio
import UnicoProofs.Platonici.VerticeCiclico
import UnicoProofs.Platonici.FaccettaDeterminata

/-!
# Il fan marcato

Il primo blocco chiude l'audit di `CyclicVertexData`: dopo il ponte
`ConvexPolytope.asFinite`, le intersezioni consecutive sono facce di rango
uno e sono esattamente i due spigoli della faccetta per il vertice marcato.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-! ## Parte 1: audit del predicato -/

/-- Due faccette tridimensionali distinte che hanno due punti distinti in
comune hanno intersezione di rango uno. -/
theorem faceDim_inter_faccette_eq_one (P : ConvexPolytope 3)
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
  have hssub : A ∩ B ⊂ A := by
    refine ⟨Set.inter_subset_left, fun hsup => ?_⟩
    have hAleB : A ⊆ B := fun z hz => (hsup hz).2
    have hss : A ⊂ B :=
      ⟨hAleB, fun hBA => hAB (Set.Subset.antisymm hAleB hBA)⟩
    have hlt := faceDim_lt_of_ssubset P hA hB hss
    omega
  have hlt := faceDim_lt_of_ssubset P hint hA hssub
  refine ⟨hint, ?_⟩
  show Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) = 1
  have hlt' : Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) < 2 := by
    have hlt0 : Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) <
        Module.finrank ℝ (vectorSpan ℝ A) := hlt
    have hdA' : Module.finrank ℝ (vectorSpan ℝ A) = 2 := hdA
    omega
  omega

/-- **Adiacenza passo-uno.** L'intersezione della faccetta `i` con la sua
successiva nel certificato ciclico e' una faccia di rango uno per `v`. -/
theorem adiacenza_passo_uno (P : ConvexPolytope 3) {v : E 3} {q : ℕ}
    (hq : 3 ≤ q) (D : P.asFinite.CyclicVertexData v q) (i : Fin q) :
    P.IsFace (D.faccetta i ∩ D.faccetta (finRotate q i)) ∧
      faceDim (D.faccetta i ∩ D.faccetta (finRotate q i)) = 1 ∧
      v ∈ D.faccetta i ∩ D.faccetta (finRotate q i) := by
  have hFi := (P.asFinite_isFacet_iff (D.faccetta i)).1 (D.isFacet i)
  have hFn := (P.asFinite_isFacet_iff
    (D.faccetta (finRotate q i))).1 (D.isFacet (finRotate q i))
  have hne : D.faccetta i ≠ D.faccetta (finRotate q i) := by
    intro h
    exact _root_.finRotate_ne_self (by omega) i (D.distinte h).symm
  obtain ⟨x, hxv, hx⟩ := D.spigolo i
  have hinter := faceDim_inter_faccette_eq_one P
    hFi.1 hFi.2 hFn.1 hFn.2 hne
    (D.mem_v i) (D.mem_v (finRotate q i)) hx.1 hx.2 hxv
  exact ⟨hinter.1, hinter.2, D.mem_v i, D.mem_v (finRotate q i)⟩

/-- **I due spigoli in `v` di una faccetta sono esattamente il precedente
e il successivo.** La conclusione quantifica su qualunque faccia di rango uno
per `v` contenuta nella faccetta `i`; quindi e' direttamente utilizzabile dal
chiamante senza scegliere in anticipo un rappresentante dello spigolo. -/
theorem spigoli_in_v_della_faccetta_esatti
    (P : ConvexPolytope 3) {v : E 3} {q : ℕ}
    (hq : 3 ≤ q) (D : P.asFinite.CyclicVertexData v q) (i : Fin q)
    {delta : Set (E 3)} (hdelta : P.IsFace delta)
    (hddelta : faceDim delta = 1) (hvdelta : v ∈ delta)
    (hdeltaA : delta ⊆ D.faccetta i) :
    delta =
        (D.faccetta ((finRotate q).symm i) ∩ D.faccetta i) ∨
      delta =
        (D.faccetta i ∩ D.faccetta (finRotate q i)) := by
  let iprev : Fin q := (finRotate q).symm i
  have hrotprev : finRotate q iprev = i := (finRotate q).apply_symm_apply i
  have hprev0 := adiacenza_passo_uno P hq D iprev
  have hprevFace : P.IsFace
      (D.faccetta iprev ∩ D.faccetta i) := by
    simpa only [hrotprev] using hprev0.1
  have hprevDim : faceDim
      (D.faccetta iprev ∩ D.faccetta i) = 1 := by
    simpa only [hrotprev] using hprev0.2.1
  have hvprev : v ∈ D.faccetta iprev ∩ D.faccetta i :=
    ⟨D.mem_v iprev, D.mem_v i⟩
  have hnext := adiacenza_passo_uno P hq D i
  have hne : (D.faccetta iprev ∩ D.faccetta i) ≠
      (D.faccetta i ∩ D.faccetta (finRotate q i)) := by
    intro heq
    obtain ⟨x, hxv, hx⟩ := D.spigolo iprev
    have hxprev : x ∈ D.faccetta iprev ∩ D.faccetta i := by
      simpa only [hrotprev] using hx
    have hxnext : x ∈ D.faccetta i ∩ D.faccetta (finRotate q i) := by
      rw [← heq]
      exact hxprev
    rcases D.spigolo_due iprev (finRotate q i) x hx hxv hxnext.2 with h | h
    · have hrot := congrArg (finRotate q) h
      rw [hrotprev] at hrot
      exact finRotate_due_ne hq i hrot
    · apply _root_.finRotate_ne_self (by omega) i
      calc
        finRotate q i = finRotate q iprev := h
        _ = i := hrotprev
  have halt := spigoli_della_faccetta P
    ((P.asFinite_isFacet_iff (D.faccetta i)).1 (D.isFacet i)).1
    ((P.asFinite_isFacet_iff (D.faccetta i)).1 (D.isFacet i)).2
    hprevFace hprevDim hvprev hnext.1 hnext.2.1 hnext.2.2
    Set.inter_subset_right Set.inter_subset_left hne
    hdelta hddelta hvdelta hdeltaA
  simpa only [iprev] using halt

/-! ## Parte 2: unicita' algebrica del fan marcato -/

instance factFinrankETre : Fact (Module.finrank ℝ (E 3) = 3) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- L'orientazione cartesiana fissata di `E 3`. -/
noncomputable def orientazioneTre : Orientation ℝ (E 3) (Fin 3) :=
  ((Pi.basisFun ℝ (Fin 3)).map
    (EuclideanSpace.equiv (Fin 3) ℝ).toLinearEquiv.symm).orientation

/-- Il prodotto misto orientato. Il suo segno individua i due semispazi
aperti separati dal piano delle prime due direzioni. -/
noncomputable def volumeTre (a b z : E 3) : ℝ :=
  orientazioneTre.volumeForm ![a, b, z]

/-- Linearita' del prodotto misto nell'ultimo argomento. -/
theorem volumeTre_add (a b z w : E 3) :
    volumeTre a b (z + w) = volumeTre a b z + volumeTre a b w := by
  let f := orientazioneTre.volumeForm
  have h := f.map_update_add ![a, b, 0] (2 : Fin 3) z w
  have hadd : Function.update ![a, b, 0] (2 : Fin 3) (z + w) =
      ![a, b, z + w] := by
    funext i
    fin_cases i <;> rfl
  have hz : Function.update ![a, b, 0] (2 : Fin 3) z = ![a, b, z] := by
    funext i
    fin_cases i <;> rfl
  have hw : Function.update ![a, b, 0] (2 : Fin 3) w = ![a, b, w] := by
    funext i
    fin_cases i <;> rfl
  change f ![a, b, z + w] = f ![a, b, z] + f ![a, b, w]
  rwa [hadd, hz, hw] at h

/-- **I due candidati speculari.** Due vettori con la stessa norma e gli
stessi prodotti scalari con due direzioni marcate sono scambiati dalla
riflessione nel loro piano. Se appartengono allo stesso semispazio aperto,
cioe' i loro volumi orientati hanno prodotto positivo, coincidono. -/
theorem eq_of_prodotti_scalari_e_stesso_semispazio
    {a b z w : E 3}
    (hnorm : ‖z‖ = ‖w‖)
    (ha : ⟪a, z⟫ = ⟪a, w⟫) (hb : ⟪b, z⟫ = ⟪b, w⟫)
    (hside : 0 < volumeTre a b z * volumeTre a b w) : z = w := by
  by_contra hne
  have hd0 : z - w ≠ 0 := sub_ne_zero.mpr hne
  have had : ⟪a, z - w⟫ = 0 := by
    rw [inner_sub_right, ha, sub_self]
  have hbd : ⟪b, z - w⟫ = 0 := by
    rw [inner_sub_right, hb, sub_self]
  have hsd : ⟪z + w, z - w⟫ = 0 := by
    rw [inner_add_left, inner_sub_right, inner_sub_right,
      real_inner_comm z w, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq]
    rw [hnorm]
    ring
  let t : Fin 3 → E 3 := ![a, b, z + w]
  have htdep : ¬LinearIndependent ℝ t := by
    intro htli
    have hspan : Submodule.span ℝ (Set.range t) = ⊤ :=
      htli.span_eq_top_of_card_eq_finrank (by
        rw [Fintype.card_fin, finrank_euclideanSpace_fin])
    have hle : Submodule.span ℝ (Set.range t) ≤ (ℝ ∙ (z - w))ᗮ := by
      rw [Submodule.span_le]
      intro u hu
      obtain ⟨i, rfl⟩ := hu
      change t i ∈ (ℝ ∙ (z - w))ᗮ
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
      fin_cases i
      · exact had
      · exact hbd
      · exact hsd
    have hdorth : z - w ∈ (ℝ ∙ (z - w))ᗮ := by
      apply hle
      rw [hspan]
      exact Submodule.mem_top
    have hinner : ⟪z - w, z - w⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp hdorth
    exact hd0 (inner_self_eq_zero.mp hinner)
  have hzero : volumeTre a b (z + w) = 0 := by
    exact orientazioneTre.volumeForm.map_linearDependent t htdep
  rw [volumeTre_add] at hzero
  have hwneg : volumeTre a b w = -volumeTre a b z := by linarith
  rw [hwneg] at hside
  nlinarith [sq_nonneg (volumeTre a b z)]

/-- Versione orientata positiva del lemma dei due candidati. -/
theorem eq_of_prodotti_scalari_e_semispazio
    {a b z w : E 3}
    (hnorm : ‖z‖ = ‖w‖)
    (ha : ⟪a, z⟫ = ⟪a, w⟫) (hb : ⟪b, z⟫ = ⟪b, w⟫)
    (hz : 0 < volumeTre a b z) (hw : 0 < volumeTre a b w) : z = w :=
  eq_of_prodotti_scalari_e_stesso_semispazio hnorm ha hb (mul_pos hz hw)

/-- Le cinque coppie di Schlaefli ammesse. -/
def CoppiaPlatonica (p q : ℕ) : Prop :=
  (p = 3 ∧ q = 3) ∨ (p = 4 ∧ q = 3) ∨ (p = 3 ∧ q = 4) ∨
    (p = 5 ∧ q = 3) ∨ (p = 3 ∧ q = 5)

/-- Coseno algebrico dell'angolo facciale interno. -/
noncomputable def cosFacciale (p : ℕ) : ℝ :=
  if p = 3 then 1 / 2
  else if p = 4 then 0
  else if p = 5 then (1 - Real.sqrt 5) / 4
  else 0

/-- Coseno fra raggi non adiacenti. Per i soli casi in cui compare e'
`0` nel fan quadrato e il coniugato aureo nel fan pentagonale. -/
noncomputable def cosLontano (q : ℕ) : ℝ :=
  if q = 4 then 0
  else if q = 5 then (1 - Real.sqrt 5) / 4
  else 0

/-- Matrice di Gram canonica del fan: diagonale, adiacenza ciclica, e
unico valore restante per `q = 4,5`. -/
noncomputable def gramFan (p q : ℕ) (i j : Fin q) : ℝ :=
  if i = j then 1
  else if j = finRotate q i ∨ i = finRotate q j then cosFacciale p
  else cosLontano q

/-- Certificato algebrico di un fan marcato. La matrice di Gram e' quella
finita della coppia di Schlaefli e gli indici `0,1` sono il lato marcato. -/
structure FanMarcatoAlgebrico (p q : ℕ) [NeZero q] where
  raggi : Fin q → E 3
  gram : ∀ i j, ⟪raggi i, raggi j⟫ = gramFan p q i j

/-- L'asse orientato del fan e' la somma dei raggi. -/
noncomputable def FanMarcatoAlgebrico.asse {p q : ℕ} [NeZero q]
    (F : FanMarcatoAlgebrico p q) : E 3 :=
  ∑ i, F.raggi i

/-- La matrice di Gram certifica in particolare che tutti i raggi sono
unitari. -/
theorem FanMarcatoAlgebrico.norma_raggio {p q : ℕ} [NeZero q]
    (F : FanMarcatoAlgebrico p q) (i : Fin q) : ‖F.raggi i‖ = 1 := by
  have hinner : ⟪F.raggi i, F.raggi i⟫ = 1 := by
    simpa [gramFan] using F.gram i i
  rw [real_inner_self_eq_norm_sq] at hinner
  nlinarith [norm_nonneg (F.raggi i)]

/-- **LEMMA DEL FAN MARCATO.** Una volta allineati i due indici marcati
`0,1`, due fan con la stessa matrice di Gram di Schlaefli e con tutti gli
altri raggi nello stesso semispazio aperto coincidono punto per punto.
Questa e' piu' forte dell'uguaglianza a meno di rotazione: il chiamante
ruota prima gli indici per allineare il lato marcato. -/
theorem fan_marcato_unico {p q : ℕ} [NeZero q]
    (F G : FanMarcatoAlgebrico p q)
    (hzero : F.raggi 0 = G.raggi 0) (huno : F.raggi 1 = G.raggi 1)
    (hstesso : ∀ i, i ≠ 0 → i ≠ 1 →
      0 < volumeTre (F.raggi 0) (F.raggi 1) (F.raggi i) *
        volumeTre (G.raggi 0) (G.raggi 1) (G.raggi i)) :
    F.raggi = G.raggi := by
  funext i
  by_cases hi0 : i = 0
  · simpa [hi0] using hzero
  by_cases hi1 : i = 1
  · simpa [hi1] using huno
  apply eq_of_prodotti_scalari_e_stesso_semispazio
  · rw [F.norma_raggio i, G.norma_raggio i]
  · calc
      ⟪F.raggi 0, F.raggi i⟫ = gramFan p q 0 i := F.gram 0 i
      _ = ⟪G.raggi 0, G.raggi i⟫ := (G.gram 0 i).symm
      _ = ⟪F.raggi 0, G.raggi i⟫ := by rw [hzero]
  · calc
      ⟪F.raggi 1, F.raggi i⟫ = gramFan p q 1 i := F.gram 1 i
      _ = ⟪G.raggi 1, G.raggi i⟫ := (G.gram 1 i).symm
      _ = ⟪F.raggi 1, G.raggi i⟫ := by rw [huno]
  · simpa only [hzero, huno] using hstesso i hi0 hi1

theorem sqrt_cinque_lt_tre : Real.sqrt 5 < 3 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3)]
  norm_num

/-- La somma dei raggi non e' nulla e orienta l'asse verso il lato interno:
ha prodotto scalare strettamente positivo con ogni raggio. Il calcolo e'
finito sulle cinque coppie e usa solo i coseni algebrici. -/
theorem asse_fan_marcato_interno {p q : ℕ} [NeZero q]
    (hpq : CoppiaPlatonica p q) (F : FanMarcatoAlgebrico p q) :
    F.asse ≠ 0 ∧ ∀ i, 0 < ⟪F.asse, F.raggi i⟫ := by
  have hinterno : ∀ i, 0 < ⟪F.asse, F.raggi i⟫ := by
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      intro i
      fin_cases i <;>
        simp only [FanMarcatoAlgebrico.asse, Fin.sum_univ_three,
          Fin.sum_univ_four, Fin.sum_univ_five, inner_add_left] <;>
        simp_rw [F.gram] <;>
        simp [gramFan, cosFacciale, cosLontano, finRotate_apply] <;>
        nlinarith [sqrt_cinque_lt_tre]
  refine ⟨?_, hinterno⟩
  intro hzero
  have hpos := hinterno (0 : Fin q)
  rw [hzero, inner_zero_left] at hpos
  linarith

end LeanEval.Geometry.PlatonicClassification
