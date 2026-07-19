import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.MossaInvolutiva
import UnicoProofs.Platonici.Equivarianza
import UnicoProofs.Platonici.Trasportatore
import UnicoProofs.Platonici.RelazioniCoxeter
import UnicoProofs.Platonici.GruppoFinito
import UnicoProofs.Platonici.Ordini
import UnicoProofs.Platonici.Coniugazione

/-!
MOTORE COXETER, PASSO 23 — IL PONTE FRA GRUPPO E MOSSE (19 lug 2026).

Se due riflessioni semplici COMMUTANO nel gruppo, allora le due MOSSE
di adiacenza commutano sulle bandiere. Non è ovvio: `rᵢ` è il
trasportatore da `F` alla sua adiacente, e applicato a una bandiera
diversa da `F` non compie in generale la mossa `i`.

L'argomento: la bandiera `H := act (rᵢ · rⱼ) F` si calcola in due modi
grazie alla commutazione, e i due calcoli, confrontati rango per rango,
mostrano che `H` è adiacente ad `adj_i F` esattamente in `j` e ad
`adj_j F` esattamente in `i`. L'unicità dell'adiacente chiude.

Vale per QUALSIASI coppia di ranghi distinti, non solo per i lontani.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- **Il ponte**: la commutazione nel gruppo dà la commutazione delle
mosse. -/
theorem mosse_commutano_di_riflessioni (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) {i j : Fin n} (hij : i ≠ j)
    (hcomm : simpleGen P hreg F i * simpleGen P hreg F j =
      simpleGen P hreg F j * simpleGen P hreg F i) :
    adjacentFlag P hreg.1 (adjacentFlag P hreg.1 F i) j =
      adjacentFlag P hreg.1 (adjacentFlag P hreg.1 F j) i := by
  set A := adjacentFlag P hreg.1 F i with hA
  set B := adjacentFlag P hreg.1 F j with hB
  set H := act P (simpleGen P hreg F i * simpleGen P hreg F j) F with hH
  have hAdjA := adjacentFlag_isAdjacent P hreg.1 F i
  have hAdjB := adjacentFlag_isAdjacent P hreg.1 F j
  -- primo calcolo: H = act rᵢ (act rⱼ F) = act rᵢ B
  have hH1 : H = act P (simpleGen P hreg F i) B := by
    rw [hH, act_mul, act_simpleGen P hreg F j]
  -- secondo calcolo, per commutazione: H = act rⱼ A
  have hH2 : H = act P (simpleGen P hreg F j) A := by
    rw [hH, hcomm, act_mul, act_simpleGen P hreg F i]
  -- le facce di H fuori dai due ranghi
  have hface_i : H.face i = A.face i := by
    rw [hH1]
    show (⇑(simpleReflection P hreg F i)) '' B.face i = A.face i
    rw [hAdjB.1 i hij]
    have := simpleReflection_mapFlag P hreg F i
    have hk := congrArg (fun G : P.Flag => G.face i) this
    simpa only [mapFlag_face] using hk
  have hface_j : H.face j = B.face j := by
    rw [hH2]
    show (⇑(simpleReflection P hreg F j)) '' A.face j = B.face j
    rw [hAdjA.1 j (Ne.symm hij)]
    have := simpleReflection_mapFlag P hreg F j
    have hk := congrArg (fun G : P.Flag => G.face j) this
    simpa only [mapFlag_face] using hk
  have hface_out : ∀ k : Fin n, k ≠ i → k ≠ j → H.face k = F.face k := by
    intro k hki hkj
    rw [hH1]
    show (⇑(simpleReflection P hreg F i)) '' B.face k = F.face k
    rw [hAdjB.1 k hkj]
    have := simpleReflection_mapFlag P hreg F i
    have hk := congrArg (fun G : P.Flag => G.face k) this
    have hAk : (⇑(simpleReflection P hreg F i)) '' F.face k = A.face k := by
      simpa only [mapFlag_face] using hk
    rw [hAk]
    exact hAdjA.1 k hki
  -- H è adiacente ad A esattamente in j
  have hHA : FlagAdjacentAt P A H j := by
    constructor
    · intro k hk
      by_cases hki : k = i
      · rw [hki, hface_i]
      · rw [hface_out k hki hk, hAdjA.1 k hki]
    · rw [hface_j, hAdjA.1 j (Ne.symm hij)]
      exact hAdjB.2
  -- H è adiacente a B esattamente in i
  have hHB : FlagAdjacentAt P B H i := by
    constructor
    · intro k hk
      by_cases hkj : k = j
      · rw [hkj, hface_j]
      · rw [hface_out k hk hkj, hAdjB.1 k hkj]
    · rw [hface_i, hAdjB.1 i hij]
      exact hAdjA.2
  have e1 : H = adjacentFlag P hreg.1 A j :=
    adjacentFlag_eq_of_isAdjacent P hreg.1 j hHA
  have e2 : H = adjacentFlag P hreg.1 B i :=
    adjacentFlag_eq_of_isAdjacent P hreg.1 i hHB
  rw [← e1, ← e2]

/-- Se l'ordine del prodotto è 2, le due riflessioni commutano. -/
theorem simpleGen_comm_of_order_two (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i j : Fin n)
    (h2 : coxeterMatrix P hreg F i j = 2) :
    simpleGen P hreg F i * simpleGen P hreg F j =
      simpleGen P hreg F j * simpleGen P hreg F i := by
  have hsq : (simpleGen P hreg F i * simpleGen P hreg F j) *
      (simpleGen P hreg F i * simpleGen P hreg F j) = 1 := by
    have := orderOf_dvd_iff_pow_eq_one (n := 2)
      (x := simpleGen P hreg F i * simpleGen P hreg F j)
    have hdvd : orderOf (simpleGen P hreg F i * simpleGen P hreg F j) ∣ 2 := by
      unfold coxeterMatrix at h2
      rw [h2]
    have hpow := this.mp hdvd
    rw [pow_two] at hpow
    exact hpow
  have ha : (simpleGen P hreg F i)⁻¹ = simpleGen P hreg F i := by
    rw [inv_eq_iff_mul_eq_one]
    exact simpleGen_sq P hreg F i
  have hb : (simpleGen P hreg F j)⁻¹ = simpleGen P hreg F j := by
    rw [inv_eq_iff_mul_eq_one]
    exact simpleGen_sq P hreg F j
  have h := mul_eq_one_iff_eq_inv.mp hsq
  rwa [mul_inv_rev, ha, hb] at h

/-- **Se `mᵢⱼ = 2` allora le mosse commutano.** -/
theorem mosse_commutano_di_ordine_due (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) {i j : Fin n} (hij : i ≠ j)
    (h2 : coxeterMatrix P hreg F i j = 2) :
    adjacentFlag P hreg.1 (adjacentFlag P hreg.1 F i) j =
      adjacentFlag P hreg.1 (adjacentFlag P hreg.1 F j) i :=
  mosse_commutano_di_riflessioni P hreg F hij
    (simpleGen_comm_of_order_two P hreg F i j h2)

end LeanEval.Geometry.PlatonicClassification
