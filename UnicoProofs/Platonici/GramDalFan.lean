import Mathlib
import UnicoProofs.Platonici.FanMarcato
import UnicoProofs.Platonici.AngoloFaccetta
import UnicoProofs.Platonici.PonteEsposizione
import UnicoProofs.Platonici.Classificazione

/-!
# La Gram canonica dal fan geometrico

Questo modulo estrae dalla struttura geometrica `CyclicVertexData` la
matrice di Gram richiesta da `FanMarcatoAlgebrico`.
-/

open Set Real InnerProductGeometry
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope PlatoniciA13

set_option maxHeartbeats 1000000

/-- Due raggi consecutivi del fan aprono l'angolo interno della faccetta
regolare che li contiene. -/
theorem angolo_direzioni_consecutive
    (P : FiniteConvexPolytope (E 3)) {p q : ℕ}
    (h : P.IsCyclicallyRegularOfType p q) {v : E 3}
    (hv : v ∈ P.vertices) (D : P.CyclicVertexData v q) (i : Fin q) :
    angle (dir P v D i) (dir P v D (finRotate q i)) =
      ((p : ℝ) - 2) * π / p := by
  classical
  obtain ⟨h3, hp3, hq3, ℓ, hℓ0, hreg, hcyc⟩ := h
  have hvex : v ∈ P.toSet.extremePoints ℝ := by
    rw [FiniteConvexPolytope.toSet, ← P.vertices_eq_extremePoints]
    exact hv
  let i1 : Fin q := finRotate q i
  let i2 : Fin q := finRotate q i1
  have hi1 : i1 ≠ i := by
    exact _root_.finRotate_ne_self (by omega) i
  have hi2i : i2 ≠ i := by
    exact finRotate_due_ne hq3 i
  have hi2i1 : i2 ≠ i1 := by
    exact _root_.finRotate_ne_self (by omega) i1
  have hFreg := hreg (D.faccetta i1) (D.isFacet i1)
  set x1 : E 3 := punto P v D i with hx1def
  set x2 : E 3 := punto P v D i1 with hx2def
  have hs1 := punto_spec P v D i
  have hs2 := punto_spec P v D i1
  have hn1 : (0 : ℝ) < ‖x1 - v‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hs1.1)
  have hn2 : (0 : ℝ) < ‖x2 - v‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hs2.1)
  have hB1exp : IsExposed ℝ (D.faccetta i1)
      (D.faccetta i1 ∩ D.faccetta i) :=
    spigolo_esposto_nella_faccetta (D.isFacet i1).1.1 (D.isFacet i).1.1
  have hB2exp : IsExposed ℝ (D.faccetta i1)
      (D.faccetta i1 ∩ D.faccetta i2) :=
    spigolo_esposto_nella_faccetta (D.isFacet i1).1.1 (D.isFacet i2).1.1
  have hvB1 : v ∈ D.faccetta i1 ∩ D.faccetta i :=
    ⟨D.mem_v i1, D.mem_v i⟩
  have hvB2 : v ∈ D.faccetta i1 ∩ D.faccetta i2 :=
    ⟨D.mem_v i1, D.mem_v i2⟩
  have hx1B : x1 ∈ D.faccetta i1 ∩ D.faccetta i := by
    exact ⟨hs1.2.2, hs1.2.1⟩
  have hx2B : x2 ∈ D.faccetta i1 ∩ D.faccetta i2 := by
    exact ⟨hs2.2.1, hs2.2.2⟩
  have hx2B1 : x2 ∉ D.faccetta i1 ∩ D.faccetta i := by
    rintro ⟨-, hx2i⟩
    rcases D.spigolo_due i1 i x2 hs2.2 hs2.1 hx2i with hc | hc
    · exact hi1 hc.symm
    · exact hi2i hc.symm
  have hx1B2 : x1 ∉ D.faccetta i1 ∩ D.faccetta i2 := by
    rintro ⟨-, hx1i2⟩
    rcases D.spigolo_due i i2 x1 hs1.2 hs1.1 hx1i2 with hc | hc
    · exact hi2i hc
    · exact hi2i1 hc
  have hdir : ∀ c : ℝ, 0 < c → x2 - v ≠ c • (x1 - v) := by
    intro c hc heq
    have hd : dir P v D i1 = dir P v D i := by
      show ‖punto P v D i1 - v‖⁻¹ • (punto P v D i1 - v) =
        ‖punto P v D i - v‖⁻¹ • (punto P v D i - v)
      rw [← hx2def, ← hx1def, heq, norm_smul, Real.norm_eq_abs,
        abs_of_pos hc, smul_smul, mul_inv]
      congr 1
      field_simp
    exact hi1 (dir_iniettiva P v hq3 D hd)
  have hA := angolo_della_faccetta P hFreg (D.mem_v i1) hvex hB1exp hB2exp
    hvB1 hvB2 hx1B hx2B hs1.1 hs2.1 hx2B1 hx1B2 hdir
  have hlink : angle (dir P v D i) (dir P v D i1) =
      EuclideanGeometry.angle x1 v x2 := by
    show angle (‖punto P v D i - v‖⁻¹ • (punto P v D i - v))
        (‖punto P v D i1 - v‖⁻¹ • (punto P v D i1 - v)) =
      angle (x1 - v) (x2 - v)
    rw [← hx1def, ← hx2def,
      angle_smul_left_of_pos _ _ (inv_pos.mpr hn1),
      angle_smul_right_of_pos _ _ (inv_pos.mpr hn2)]
  simpa only [i1] using hlink.trans hA

/-- Valore algebrico del coseno dell'angolo interno per i tre possibili
numeri di lati. -/
theorem cos_angolo_facciale {p : ℕ} (hp : p = 3 ∨ p = 4 ∨ p = 5) :
    Real.cos (((p : ℝ) - 2) * π / p) = cosFacciale p := by
  rcases hp with rfl | rfl | rfl
  · norm_num [cosFacciale, Real.cos_pi_div_three]
  · norm_num [cosFacciale]
    convert Real.cos_pi_div_two using 2
    all_goals ring
  · rw [show ((((5 : ℕ) : ℝ) - 2) * π / (5 : ℕ)) =
        π - 2 * (π / 5) by norm_num; ring,
      Real.cos_pi_sub, Real.cos_two_mul, Real.cos_pi_div_five]
    have hs : (Real.sqrt 5) ^ 2 = 5 := by norm_num
    change -(2 * ((1 + Real.sqrt 5) / 4) ^ 2 - 1) =
      (1 - Real.sqrt 5) / 4
    nlinarith

/-- Il prodotto scalare di raggi consecutivi e' il coseno facciale
canonico. -/
theorem inner_direzioni_consecutive
    (P : FiniteConvexPolytope (E 3)) {p q : ℕ}
    (h : P.IsCyclicallyRegularOfType p q) {v : E 3}
    (hv : v ∈ P.vertices) (D : P.CyclicVertexData v q) (i : Fin q) :
    ⟪dir P v D i, dir P v D (finRotate q i)⟫ = cosFacciale p := by
  have hpq := (cyclicallyRegular_schlafli P h).2
  have hp : p = 3 ∨ p = 4 ∨ p = 5 := by
    rcases hpq with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -⟩
    all_goals simp
  rw [inner_eq_cos_angle_of_norm_eq_one (dir_unitaria P v D i)
    (dir_unitaria P v D (finRotate q i)),
    angolo_direzioni_consecutive P h hv D i, cos_angolo_facciale hp]

/-- L'isometria del certificato rende la Gram invariante per traslazione
ciclica simultanea degli indici. -/
theorem inner_direzioni_rotate
    (P : FiniteConvexPolytope (E 3)) {v : E 3} {q : ℕ}
    (hq : 3 ≤ q) (hv : v ∈ P.vertices)
    (D : P.CyclicVertexData v q) (i j : Fin q) :
    ⟪dir P v D (finRotate q i), dir P v D (finRotate q j)⟫ =
      ⟪dir P v D i, dir P v D j⟫ := by
  have hvex : v ∈ P.toSet.extremePoints ℝ := by
    rw [FiniteConvexPolytope.toSet, ← P.vertices_eq_extremePoints]
    exact hv
  rw [← dir_passo P v hq D hvex i, ← dir_passo P v hq D hvex j,
    LinearIsometryEquiv.inner_map_map]

/-- Il funzionale di supporto della faccetta `i`, traslato in `v`, si
annulla sui suoi due raggi e e' strettamente negativo su tutti gli altri. -/
theorem funzionale_sul_fan
    (P : FiniteConvexPolytope (E 3)) {v : E 3} {q : ℕ}
    (D : P.CyclicVertexData v q) (i : Fin q) :
    ∃ l : E 3 →L[ℝ] ℝ,
      (∀ j : Fin q, j = i ∨ finRotate q j = i → l (dir P v D j) = 0) ∧
      (∀ j : Fin q, j ≠ i → finRotate q j ≠ i →
        l (dir P v D j) < 0) := by
  obtain ⟨l, hzero, hneg⟩ := funzionale_faccetta P D i
  refine ⟨l, ?_, ?_⟩
  · intro j hj
    have hs := punto_spec P v D j
    have hp : punto P v D j ∈ D.faccetta i := by
      rcases hj with rfl | hj
      · exact hs.2.1
      · rw [← hj]
        exact hs.2.2
    rw [dir, map_smul, map_sub, hzero _ hp, hzero v (D.mem_v i), sub_self,
      smul_eq_mul, mul_zero]
  · intro j hji hrji
    have hs := punto_spec P v D j
    have hlt := hneg j hji hrji (punto P v D j) hs.2 hs.1
    have hn : (0 : ℝ) < ‖punto P v D j - v‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hs.1)
    rw [dir, map_smul, map_sub, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hn) (sub_neg.mpr hlt)

/-- Quattro vettori di `E 3` hanno Gram singolare. -/
theorem det_gram_quattro_eq_zero (u : Fin 4 → E 3) :
    (Matrix.gram ℝ u).det = 0 := by
  have hdep : ¬LinearIndependent ℝ u := by
    intro hli
    have hc := hli.fintype_card_le_finrank
    norm_num [finrank_euclideanSpace_fin] at hc
  by_contra hne
  exact hdep (Matrix.linearIndependent_of_det_gram_ne_zero hne)

/-- Tre vettori non linearmente indipendenti hanno Gram singolare. -/
theorem det_gram_tre_eq_zero_of_dependent {u : Fin 3 → E 3}
    (hdep : ¬LinearIndependent ℝ u) : (Matrix.gram ℝ u).det = 0 := by
  by_contra hne
  exact hdep (Matrix.linearIndependent_of_det_gram_ne_zero hne)

/-- Nel fan quadrato triangolare i raggi opposti sono ortogonali. -/
theorem inner_opposte_quattro
    (P : FiniteConvexPolytope (E 3))
    (h : P.IsCyclicallyRegularOfType 3 4) {v : E 3}
    (hv : v ∈ P.vertices) (D : P.CyclicVertexData v 4) :
    ⟪dir P v D 0, dir P v D 2⟫ = 0 := by
  let u : Fin 4 → E 3 := dir P v D
  let d : ℝ := ⟪u 0, u 2⟫
  have hu : ∀ i, ⟪u i, u i⟫ = 1 := by
    intro i
    rw [real_inner_self_eq_norm_sq, show ‖u i‖ = 1 from dir_unitaria P v D i]
    norm_num
  have hunorm : ∀ i, ‖u i‖ = 1 := fun i => dir_unitaria P v D i
  have hc : ∀ i, ⟪u i, u (finRotate 4 i)⟫ = 1 / 2 := by
    intro i
    simpa [u, cosFacciale] using inner_direzioni_consecutive P h hv D i
  have h01 : ⟪u 0, u 1⟫ = 1 / 2 := by
    simpa [finRotate_apply] using hc 0
  have h12 : ⟪u 1, u 2⟫ = 1 / 2 := by
    simpa [finRotate_apply] using hc 1
  have h23 : ⟪u 2, u 3⟫ = 1 / 2 := by
    simpa [finRotate_apply] using hc 2
  have h30 : ⟪u 3, u 0⟫ = 1 / 2 := by
    simpa [finRotate_apply] using hc 3
  have h13 : ⟪u 1, u 3⟫ = d := by
    have hr := inner_direzioni_rotate P (q := 4) (by norm_num) hv D 0 2
    simpa [u, d, finRotate_apply] using hr
  have h03 : ⟪u 0, u 3⟫ = 1 / 2 := by simpa [real_inner_comm] using h30
  have h10 : ⟪u 1, u 0⟫ = 1 / 2 := by simpa [real_inner_comm] using h01
  have h21 : ⟪u 2, u 1⟫ = 1 / 2 := by simpa [real_inner_comm] using h12
  have h32 : ⟪u 3, u 2⟫ = 1 / 2 := by simpa [real_inner_comm] using h23
  have h31 : ⟪u 3, u 1⟫ = d := by simpa [real_inner_comm] using h13
  have hdep : ¬LinearIndependent ℝ u := by
    intro hli
    have hc4 := hli.fintype_card_le_finrank
    norm_num [finrank_euclideanSpace_fin] at hc4
  obtain ⟨g, hg, hgne⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let a : ℝ := g 0
  let b : ℝ := g 1
  let c : ℝ := g 2
  let e : ℝ := g 3
  have hrel : a • u 0 + b • u 1 + c • u 2 + e • u 3 = 0 := by
    simpa only [Fin.sum_univ_four, a, b, c, e] using hg
  have heq0 := congrArg (fun z => ⟪u 0, z⟫) hrel
  have heq1 := congrArg (fun z => ⟪u 1, z⟫) hrel
  have heq2 := congrArg (fun z => ⟪u 2, z⟫) hrel
  have heq3 := congrArg (fun z => ⟪u 3, z⟫) hrel
  simp only [inner_add_right, real_inner_smul_right, inner_zero_right] at heq0 heq1 heq2 heq3
  rw [hu, h01, show ⟪u 0, u 2⟫ = d from rfl, h03] at heq0
  rw [h10, hu, h12, h13] at heq1
  have h20 : ⟪u 2, u 0⟫ = d := by simp only [d, real_inner_comm]
  rw [h20, h21, hu, h23] at heq2
  rw [h30, h31, h32, hu] at heq3
  have hdne1 : d ≠ 1 := by
    intro hd1
    have heq : u 0 = u 2 := by
      have hzero : ⟪u 0 - u 2, u 0 - u 2⟫ = 0 := by
        rw [inner_sub_left, inner_sub_right, inner_sub_right,
          hu, hu, h20, show ⟪u 0, u 2⟫ = d from rfl, hd1]
        norm_num
      exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
    exact (by decide : (0 : Fin 4) ≠ 2) (dir_iniettiva P v (by norm_num) D heq)
  have hac : a = c := by
    have hp : (1 - d) * (a - c) = 0 := by nlinarith [heq0, heq2]
    rcases mul_eq_zero.mp hp with hd | hac
    · exact False.elim (hdne1 (by linarith))
    · linarith
  have hbe : b = e := by
    have hp : (1 - d) * (b - e) = 0 := by nlinarith [heq1, heq3]
    rcases mul_eq_zero.mp hp with hd | hbe
    · exact False.elim (hdne1 (by linarith))
    · linarith
  have hnon : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ e ≠ 0 := by
    obtain ⟨i, hi⟩ := hgne
    fin_cases i
    · exact Or.inl (by simpa [a] using hi)
    · exact Or.inr (Or.inl (by simpa [b] using hi))
    · exact Or.inr (Or.inr (Or.inl (by simpa [c] using hi)))
    · exact Or.inr (Or.inr (Or.inr (by simpa [e] using hi)))
  rw [← hac, ← hbe] at heq0 heq1 hnon
  have ha : a ≠ 0 := by
    intro ha0
    have hb0 : b = 0 := by rw [ha0] at heq0; linarith
    exact hnon.elim (fun h => h ha0) fun h =>
      h.elim (fun hb => hb hb0) fun h => h.elim (fun hc => hc ha0) (fun he => he hb0)
  have hpoly : d * (d + 2) * a = 0 := by
    linear_combination (1 + d) * heq0 - heq1
  have hd0m2 : d = 0 ∨ d = -2 := by
    rcases mul_eq_zero.mp hpoly with hprod | ha0
    · rcases mul_eq_zero.mp hprod with hd0 | hdm2
      · exact Or.inl hd0
      · exact Or.inr (by linarith)
    · exact False.elim (ha ha0)
  rcases hd0m2 with hd0 | hdneg
  · exact hd0
  ·
    have hb := abs_real_inner_le_norm (u 0) (u 2)
    rw [show ‖u 0‖ = 1 from dir_unitaria P v D 0,
      show ‖u 2‖ = 1 from dir_unitaria P v D 2] at hb
    norm_num at hb
    change |⟪u 0, u 2⟫| ≤ 1 at hb
    rw [show ⟪u 0, u 2⟫ = d from rfl, hdneg] at hb
    norm_num at hb

/-- Nel fan pentagonale triangolare il prodotto scalare dei raggi a
distanza ciclica due e' il coniugato aureo negativo. La radice aurea
positiva e' esclusa dal funzionale di supporto della faccetta: produrrebbe
un raggio dal lato sbagliato. -/
theorem inner_lontane_cinque
    (P : FiniteConvexPolytope (E 3))
    (h : P.IsCyclicallyRegularOfType 3 5) {v : E 3}
    (hv : v ∈ P.vertices) (D : P.CyclicVertexData v 5) :
    ⟪dir P v D 0, dir P v D 2⟫ = (1 - Real.sqrt 5) / 4 := by
  let u : Fin 5 → E 3 := dir P v D
  let d : ℝ := ⟪u 0, u 2⟫
  have hu : ∀ i, ⟪u i, u i⟫ = 1 := by
    intro i
    rw [real_inner_self_eq_norm_sq, show ‖u i‖ = 1 from dir_unitaria P v D i]
    norm_num
  have hc : ∀ i, ⟪u i, u (finRotate 5 i)⟫ = 1 / 2 := by
    intro i
    simpa [u, cosFacciale] using inner_direzioni_consecutive P h hv D i
  have h01 : ⟪u 0, u 1⟫ = 1 / 2 := by
    simpa [finRotate_apply] using hc 0
  have h12 : ⟪u 1, u 2⟫ = 1 / 2 := by
    simpa [finRotate_apply] using hc 1
  have h23 : ⟪u 2, u 3⟫ = 1 / 2 := by
    simpa [finRotate_apply] using hc 2
  have h34 : ⟪u 3, u 4⟫ = 1 / 2 := by
    simpa [finRotate_apply] using hc 3
  have h40 : ⟪u 4, u 0⟫ = 1 / 2 := by
    simpa [finRotate_apply] using hc 4
  have h13 : ⟪u 1, u 3⟫ = d := by
    have hr := inner_direzioni_rotate P (q := 5) (by norm_num) hv D 0 2
    simpa [u, d, finRotate_apply] using hr
  have h24 : ⟪u 2, u 4⟫ = d := by
    have hr := inner_direzioni_rotate P (q := 5) (by norm_num) hv D 1 3
    simpa [u, finRotate_apply, h13] using hr
  have h30 : ⟪u 3, u 0⟫ = d := by
    have hr := inner_direzioni_rotate P (q := 5) (by norm_num) hv D 2 4
    simpa [u, finRotate_apply, h24] using hr
  have h41 : ⟪u 4, u 1⟫ = d := by
    have hr := inner_direzioni_rotate P (q := 5) (by norm_num) hv D 3 0
    simpa [u, finRotate_apply, h30] using hr
  let L : E 3 ≃ₗᵢ[ℝ] E 3 := D.σ.linearIsometryEquiv
  have hvex : v ∈ P.toSet.extremePoints ℝ := by
    rw [FiniteConvexPolytope.toSet, ← P.vertices_eq_extremePoints]
    exact hv
  have hL : ∀ i, L (u i) = u (finRotate 5 i) := fun i =>
    dir_passo P v (by norm_num) D hvex i
  obtain ⟨l, hlzero, hlneg⟩ := funzionale_sul_fan P D (1 : Fin 5)
  have hl0 : l (u 0) = 0 := by
    apply hlzero 0
    right
    norm_num [finRotate_apply]
  have hl1 : l (u 1) = 0 := hlzero 1 (Or.inl rfl)
  have hl2 : l (u 2) < 0 := by
    exact hlneg 2 (by decide) (by decide)
  have hl3 : l (u 3) < 0 := by
    exact hlneg 3 (by decide) (by decide)
  have hl4 : l (u 4) < 0 := by
    exact hlneg 4 (by decide) (by decide)
  let s : E 3 := ∑ i, u i
  have hsne : s ≠ 0 := by
    intro hs0
    have hls : l s < 0 := by
      change l (∑ i, u i) < 0
      rw [map_sum, Fin.sum_univ_five, hl0, hl1]
      linarith
    rw [hs0, map_zero] at hls
    linarith
  let x : Fin 3 → E 3 := ![u 0 - u 1, u 1 - u 2, u 2 - u 3]
  have hxs : ∀ k, ⟪x k, s⟫ = 0 := by
    intro k
    fin_cases k
    · change ⟪u 0 - u 1, ∑ i, u i⟫ = 0
      rw [inner_sub_left, colatitudine_comune L u hL 0 1, sub_self]
    · change ⟪u 1 - u 2, ∑ i, u i⟫ = 0
      rw [inner_sub_left, colatitudine_comune L u hL 1 2, sub_self]
    · change ⟪u 2 - u 3, ∑ i, u i⟫ = 0
      rw [inner_sub_left, colatitudine_comune L u hL 2 3, sub_self]
  have hxdep : ¬LinearIndependent ℝ x := by
    intro hxli
    have hspan : Submodule.span ℝ (Set.range x) = ⊤ :=
      hxli.span_eq_top_of_card_eq_finrank (by
        rw [Fintype.card_fin, finrank_euclideanSpace_fin])
    have hle : Submodule.span ℝ (Set.range x) ≤ (ℝ ∙ s)ᗮ := by
      rw [Submodule.span_le]
      rintro z ⟨k, rfl⟩
      change x k ∈ (ℝ ∙ s)ᗮ
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
      exact hxs k
    have hsorth : s ∈ (ℝ ∙ s)ᗮ := by
      apply hle
      rw [hspan]
      exact Submodule.mem_top
    have hss : ⟪s, s⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp hsorth
    exact hsne (inner_self_eq_zero.mp hss)
  have h10 : ⟪u 1, u 0⟫ = 1 / 2 := by simpa [real_inner_comm] using h01
  have h20 : ⟪u 2, u 0⟫ = d := by simp only [d, real_inner_comm]
  have h21 : ⟪u 2, u 1⟫ = 1 / 2 := by simpa [real_inner_comm] using h12
  have h03 : ⟪u 0, u 3⟫ = d := by simpa [real_inner_comm] using h30
  have h31 : ⟪u 3, u 1⟫ = d := by simpa [real_inner_comm] using h13
  have h32 : ⟪u 3, u 2⟫ = 1 / 2 := by simpa [real_inner_comm] using h23
  have hxx00 : ⟪u 0 - u 1, u 0 - u 1⟫ = 1 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hu, hu, h01, h10]
    ring
  have hxx11 : ⟪u 1 - u 2, u 1 - u 2⟫ = 1 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hu, hu, h12, h21]
    ring
  have hxx22 : ⟪u 2 - u 3, u 2 - u 3⟫ = 1 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hu, hu, h23, h32]
    ring
  have hxx01 : ⟪u 0 - u 1, u 1 - u 2⟫ = -d := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, h01,
      show ⟪u 0, u 2⟫ = d from rfl, hu, h12]
    ring
  have hxx02 : ⟪u 0 - u 1, u 2 - u 3⟫ = d - 1 / 2 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      show ⟪u 0, u 2⟫ = d from rfl, h03, h12, h13]
    ring
  have hxx12 : ⟪u 1 - u 2, u 2 - u 3⟫ = -d := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, h12, h13, hu, h23]
    ring
  have hxx10 : ⟪u 1 - u 2, u 0 - u 1⟫ = -d := by
    calc
      ⟪u 1 - u 2, u 0 - u 1⟫ = ⟪u 0 - u 1, u 1 - u 2⟫ := real_inner_comm _ _
      _ = -d := hxx01
  have hxx20 : ⟪u 2 - u 3, u 0 - u 1⟫ = d - 1 / 2 := by
    calc
      ⟪u 2 - u 3, u 0 - u 1⟫ = ⟪u 0 - u 1, u 2 - u 3⟫ := real_inner_comm _ _
      _ = d - 1 / 2 := hxx02
  have hxx21 : ⟪u 2 - u 3, u 1 - u 2⟫ = -d := by
    calc
      ⟪u 2 - u 3, u 1 - u 2⟫ = ⟪u 1 - u 2, u 2 - u 3⟫ := real_inner_comm _ _
      _ = -d := hxx12
  obtain ⟨g, hg, hgne⟩ := Fintype.not_linearIndependent_iff.mp hxdep
  let a : ℝ := g 0
  let b : ℝ := g 1
  let c : ℝ := g 2
  have hrel : a • (u 0 - u 1) + b • (u 1 - u 2) + c • (u 2 - u 3) = 0 := by
    rw [Fin.sum_univ_three] at hg
    change a • (u 0 - u 1) + b • (u 1 - u 2) + c • (u 2 - u 3) = 0 at hg
    exact hg
  have heq0 := congrArg (fun z => ⟪u 0 - u 1, z⟫) hrel
  have heq1 := congrArg (fun z => ⟪u 1 - u 2, z⟫) hrel
  have heq2 := congrArg (fun z => ⟪u 2 - u 3, z⟫) hrel
  simp only [inner_add_right, real_inner_smul_right, inner_zero_right] at heq0 heq1 heq2
  rw [hxx00, hxx01, hxx02] at heq0
  rw [hxx10, hxx11, hxx12] at heq1
  rw [hxx20, hxx21, hxx22] at heq2
  have hnon : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 := by
    obtain ⟨i, hi⟩ := hgne
    fin_cases i
    · exact Or.inl (by simpa [a] using hi)
    · exact Or.inr (Or.inl (by simpa [b] using hi))
    · exact Or.inr (Or.inr (by simpa [c] using hi))
  have hdle : d ≤ 1 := by
    have hbnd := abs_real_inner_le_norm (u 0) (u 2)
    rw [show ‖u 0‖ = 1 from dir_unitaria P v D 0,
      show ‖u 2‖ = 1 from dir_unitaria P v D 2] at hbnd
    exact (le_abs_self d).trans (by simpa only [mul_one, show ⟪u 0, u 2⟫ = d from rfl] using hbnd)
  have hac : a = c := by
    have hp : (3 / 2 - d) * (a - c) = 0 := by nlinarith [heq0, heq2]
    rcases mul_eq_zero.mp hp with hd | hac
    · exfalso
      nlinarith
    · linarith
  rw [← hac] at heq1 hnon
  have hb : b = 2 * d * a := by linarith [heq1]
  have ha : a ≠ 0 := by
    intro ha0
    have hb0 : b = 0 := by rw [hb, ha0, mul_zero]
    exact hnon.elim (fun h => h ha0) fun h => h.elim (fun hb' => hb' hb0) (fun hc => hc ha0)
  have hpoly : a * (4 * d ^ 2 - 2 * d - 1) = 0 := by
    rw [hac, hb] at heq0
    nlinarith
  have hquad : 4 * d ^ 2 - 2 * d - 1 = 0 :=
    (mul_eq_zero.mp hpoly).resolve_left ha
  have hsqrt : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  have hroots : 4 * d - 1 = Real.sqrt 5 ∨
      4 * d - 1 = -Real.sqrt 5 := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    nlinarith only [hquad, hsqrt]
  rcases hroots with hplus | hminus
  · have hdplus : d = (1 + Real.sqrt 5) / 4 := by linarith only [hplus]
    let b : ℝ := (Real.sqrt 5 - 1) / 2
    let c : ℝ := (1 - Real.sqrt 5) / 2
    have hrel : u 3 = u 0 + b • u 1 + c • u 2 := by
      apply sub_eq_zero.mp
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right]
      simp only [real_inner_smul_left, real_inner_smul_right]
      rw [hu, hu, hu, hu, h01, h10, h12, h21, h23, h32,
        h13, h31, h30, h03, h20, show ⟪u 0, u 2⟫ = d from rfl]
      dsimp only [b, c]
      rw [hdplus]
      ring_nf
      nlinarith only [hsqrt]
    have hlrel := congrArg l hrel
    rw [map_add, map_add, map_smul, map_smul, hl0, hl1, zero_add, smul_eq_mul,
      mul_zero, zero_add] at hlrel
    have hsqrt1 : 1 < Real.sqrt 5 := by
      nlinarith only [hsqrt, Real.sqrt_nonneg 5]
    have hcneg : c < 0 := by
      dsimp only [c]
      linarith only [hsqrt1]
    have hcpos : 0 < c * l (u 2) := mul_pos_of_neg_of_neg hcneg hl2
    have hlrel' : l (u 3) = c * l (u 2) := by
      simpa only [smul_eq_mul] using hlrel
    linarith only [hlrel', hl3, hcpos]
  · change d = (1 - Real.sqrt 5) / 4
    linarith only [hminus]

/-- Ricomposizione astratta della Gram dalle tre classi di coppie di indici:
diagonale, adiacenza ciclica e coppie lontane. -/
theorem gramFan_eq_of_unit_adjacent_far {p q : ℕ} (u : Fin q → E 3)
    (hu : ∀ i, ⟪u i, u i⟫ = 1)
    (hc : ∀ i, ⟪u i, u (finRotate q i)⟫ = cosFacciale p)
    (hfar : ∀ i j, i ≠ j → ¬ (j = finRotate q i ∨ i = finRotate q j) →
      ⟪u i, u j⟫ = cosLontano q) :
    ∀ i j, ⟪u i, u j⟫ = gramFan p q i j := by
  intro i j
  by_cases hij : i = j
  · rw [gramFan, if_pos hij]
    simpa only [hij] using hu i
  · rw [gramFan, if_neg hij]
    by_cases hadj : j = finRotate q i ∨ i = finRotate q j
    · rw [if_pos hadj]
      rcases hadj with hnext | hprev
      · simpa only [hnext] using hc i
      · calc
          ⟪u i, u j⟫ = ⟪u j, u i⟫ := real_inner_comm _ _
          _ = cosFacciale p := by simpa only [hprev] using hc j
    · rw [if_neg hadj]
      exact hfar i j hij hadj

/-- **ESTRAZIONE DELLA GRAM.** Le direzioni-spigolo unitarie del certificato
geometrico hanno esattamente la matrice `gramFan` dell'interfaccia
`FanMarcatoAlgebrico`. -/
noncomputable def fanMarcatoAlgebrico_dal_geometrico
    (P : FiniteConvexPolytope (E 3)) {p q : ℕ} [NeZero q]
    (h : P.IsCyclicallyRegularOfType p q) {v : E 3}
    (hv : v ∈ P.vertices) (D : P.CyclicVertexData v q) :
    FanMarcatoAlgebrico p q where
  raggi := dir P v D
  gram := by
    have hpq := (cyclicallyRegular_schlafli P h).2
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hu : ∀ i : Fin 3, ⟪dir P v D i, dir P v D i⟫ = 1 := by
        intro i
        rw [real_inner_self_eq_norm_sq, dir_unitaria P v D i]
        norm_num
      have hc := inner_direzioni_consecutive P h hv D
      apply gramFan_eq_of_unit_adjacent_far (dir P v D) hu hc
      intro i j hij hadj
      exfalso
      fin_cases i <;> fin_cases j <;>
        simp [finRotate_apply] at hij hadj
    · have hu : ∀ i : Fin 3, ⟪dir P v D i, dir P v D i⟫ = 1 := by
        intro i
        rw [real_inner_self_eq_norm_sq, dir_unitaria P v D i]
        norm_num
      have hc := inner_direzioni_consecutive P h hv D
      apply gramFan_eq_of_unit_adjacent_far (dir P v D) hu hc
      intro i j hij hadj
      exfalso
      fin_cases i <;> fin_cases j <;>
        simp [finRotate_apply] at hij hadj
    · have hu : ∀ i : Fin 4, ⟪dir P v D i, dir P v D i⟫ = 1 := by
        intro i
        rw [real_inner_self_eq_norm_sq, dir_unitaria P v D i]
        norm_num
      have hc := inner_direzioni_consecutive P h hv D
      have hd02 := inner_opposte_quattro P h hv D
      have hd13 : ⟪dir P v D 1, dir P v D 3⟫ = 0 := by
        have hr := inner_direzioni_rotate P (q := 4) (by norm_num) hv D 0 2
        simpa [finRotate_apply, hd02] using hr
      have hd20 : ⟪dir P v D 2, dir P v D 0⟫ = 0 := by
        simpa only [real_inner_comm] using hd02
      have hd31 : ⟪dir P v D 3, dir P v D 1⟫ = 0 := by
        simpa only [real_inner_comm] using hd13
      apply gramFan_eq_of_unit_adjacent_far (dir P v D) hu hc
      intro i j hij hadj
      fin_cases i <;> fin_cases j <;>
        simp [finRotate_apply] at hij hadj ⊢ <;>
        simp [cosLontano, hd02, hd20, hd13, hd31]
    · have hu : ∀ i : Fin 3, ⟪dir P v D i, dir P v D i⟫ = 1 := by
        intro i
        rw [real_inner_self_eq_norm_sq, dir_unitaria P v D i]
        norm_num
      have hc := inner_direzioni_consecutive P h hv D
      apply gramFan_eq_of_unit_adjacent_far (dir P v D) hu hc
      intro i j hij hadj
      exfalso
      fin_cases i <;> fin_cases j <;>
        simp [finRotate_apply] at hij hadj
    · have hu : ∀ i : Fin 5, ⟪dir P v D i, dir P v D i⟫ = 1 := by
        intro i
        rw [real_inner_self_eq_norm_sq, dir_unitaria P v D i]
        norm_num
      have hc := inner_direzioni_consecutive P h hv D
      have hd02 := inner_lontane_cinque P h hv D
      have hd13 : ⟪dir P v D 1, dir P v D 3⟫ = (1 - Real.sqrt 5) / 4 := by
        have hr := inner_direzioni_rotate P (q := 5) (by norm_num) hv D 0 2
        simpa [finRotate_apply, hd02] using hr
      have hd24 : ⟪dir P v D 2, dir P v D 4⟫ = (1 - Real.sqrt 5) / 4 := by
        have hr := inner_direzioni_rotate P (q := 5) (by norm_num) hv D 1 3
        simpa [finRotate_apply, hd13] using hr
      have hd30 : ⟪dir P v D 3, dir P v D 0⟫ = (1 - Real.sqrt 5) / 4 := by
        have hr := inner_direzioni_rotate P (q := 5) (by norm_num) hv D 2 4
        simpa [finRotate_apply, hd24] using hr
      have hd41 : ⟪dir P v D 4, dir P v D 1⟫ = (1 - Real.sqrt 5) / 4 := by
        have hr := inner_direzioni_rotate P (q := 5) (by norm_num) hv D 3 0
        simpa [finRotate_apply, hd30] using hr
      have hd20 : ⟪dir P v D 2, dir P v D 0⟫ = (1 - Real.sqrt 5) / 4 := by
        simpa only [real_inner_comm] using hd02
      have hd31 : ⟪dir P v D 3, dir P v D 1⟫ = (1 - Real.sqrt 5) / 4 := by
        simpa only [real_inner_comm] using hd13
      have hd42 : ⟪dir P v D 4, dir P v D 2⟫ = (1 - Real.sqrt 5) / 4 := by
        simpa only [real_inner_comm] using hd24
      have hd03 : ⟪dir P v D 0, dir P v D 3⟫ = (1 - Real.sqrt 5) / 4 := by
        simpa only [real_inner_comm] using hd30
      have hd14 : ⟪dir P v D 1, dir P v D 4⟫ = (1 - Real.sqrt 5) / 4 := by
        simpa only [real_inner_comm] using hd41
      apply gramFan_eq_of_unit_adjacent_far (dir P v D) hu hc
      intro i j hij hadj
      fin_cases i <;> fin_cases j <;>
        simp [finRotate_apply] at hij hadj ⊢ <;>
        simp [cosLontano, hd02, hd20, hd13, hd31, hd24, hd42,
          hd30, hd03, hd41, hd14]

/-- Forma proposizionale dell'estrazione, utile quando il chiamante non vuole
fissare la scelta definizionale del certificato algebrico. -/
theorem gram_direzioni_dal_fan
    (P : FiniteConvexPolytope (E 3)) {p q : ℕ} [NeZero q]
    (h : P.IsCyclicallyRegularOfType p q) {v : E 3}
    (hv : v ∈ P.vertices) (D : P.CyclicVertexData v q) :
    ∀ i j, ⟪dir P v D i, dir P v D j⟫ = gramFan p q i j :=
  (fanMarcatoAlgebrico_dal_geometrico P h hv D).gram

/-- **TEOREMA D'USO DEL GATE 2.** Due poliedri dello stesso tipo, allo
stesso vertice e con la stessa coppia marcata di raggi consecutivi, hanno
lo stesso fan marcato se ogni altra coppia di raggi cade nello stesso
semispazio aperto determinato dalla coppia marcata. -/
theorem fan_geometrico_marcato_unico
    (P Q : ConvexPolytope 3) {p q : ℕ} [NeZero q] {v : E 3}
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (hQ : Q.asFinite.IsCyclicallyRegularOfType p q)
    (hvP : v ∈ P.vertices) (hvQ : v ∈ Q.vertices)
    (DP : P.asFinite.CyclicVertexData v q)
    (DQ : Q.asFinite.CyclicVertexData v q)
    (hzero : dir P.asFinite v DP 0 = dir Q.asFinite v DQ 0)
    (huno : dir P.asFinite v DP 1 = dir Q.asFinite v DQ 1)
    (hstesso : ∀ i, i ≠ 0 → i ≠ 1 →
      0 < volumeTre (dir P.asFinite v DP 0) (dir P.asFinite v DP 1)
          (dir P.asFinite v DP i) *
        volumeTre (dir Q.asFinite v DQ 0) (dir Q.asFinite v DQ 1)
          (dir Q.asFinite v DQ i)) :
    dir P.asFinite v DP = dir Q.asFinite v DQ := by
  let FP := fanMarcatoAlgebrico_dal_geometrico P.asFinite hP hvP DP
  let FQ := fanMarcatoAlgebrico_dal_geometrico Q.asFinite hQ hvQ DQ
  exact fan_marcato_unico FP FQ hzero huno hstesso

end LeanEval.Geometry.PlatonicClassification
