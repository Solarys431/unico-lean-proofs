import Mathlib
import UnicoProofs.Platonici.FinestraQuattro
import UnicoProofs.Platonici.PropagazioneFinestre
import UnicoProofs.Platonici.DoppioQuattro
import UnicoProofs.Platonici.OrdineTreBordi

/-!
ESCLUSIVITÀ ALTO-DIMENSIONALE (20 lug 2026) — la saldatura.

Raccorda i teoremi sugli ordini ai bordi (`coxeterMatrix_adiacente_ge_tre_ovunque`)
alla funzione `schlafli`, poi assembla: finestre → quattro forme → esclusione del
doppio-4 → i tre soli simboli `(3…3)`, `(4,3…3)`, `(3…3,4)` per `d ≥ 5`.
-/

open Real

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- **Ogni ordine del simbolo è ≥ 3, bordi inclusi.** Raccordo a
`coxeterMatrix_adiacente_ge_tre_ovunque`. -/
theorem schlafli_ge_tre_all (P : ConvexPolytope n) (hreg : P.IsRegular) (F : P.Flag)
    (hn : 3 ≤ n) (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    3 ≤ schlafli P hreg F i := by
  rw [schlafli_apply P hreg F i hi, schlafliDi, rangoSucc]
  exact coxeterMatrix_adiacente_ge_tre_ovunque P hreg F i hi hn

/-- Il simbolo come funzione `ℕ → ℕ` (0 oltre l'ultimo arco). -/
noncomputable def schlafliFun (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) : ℕ → ℕ :=
  fun i => if h : i + 1 < n then schlafli P hreg F ⟨i, by omega⟩ else 0

theorem schlafliFun_eq (P : ConvexPolytope n) (hreg : P.IsRegular) (F : P.Flag)
    (i : ℕ) (hi : i + 1 < n) :
    schlafliFun P hreg F i = schlafli P hreg F ⟨i, by omega⟩ := by
  rw [schlafliFun, dif_pos hi]

/-- **Ogni finestra di 4 archi del simbolo è `3333`, `4333` o `3334`.** -/
theorem finestraPattern_schlafli (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (hn : 3 ≤ n) :
    FinestraPattern (schlafliFun P hreg F) (n - 1) := by
  intro s hs
  have hs5 : s + 5 ≤ n := by omega
  have e0 : schlafliFun P hreg F s = schlafli P hreg F ⟨s, by omega⟩ :=
    schlafliFun_eq P hreg F s (by omega)
  have e1 : schlafliFun P hreg F (s + 1) = schlafli P hreg F ⟨s + 1, by omega⟩ :=
    schlafliFun_eq P hreg F (s + 1) (by omega)
  have e2 : schlafliFun P hreg F (s + 2) = schlafli P hreg F ⟨s + 2, by omega⟩ :=
    schlafliFun_eq P hreg F (s + 2) (by omega)
  have e3 : schlafliFun P hreg F (s + 3) = schlafli P hreg F ⟨s + 3, by omega⟩ :=
    schlafliFun_eq P hreg F (s + 3) (by omega)
  rw [e0, e1, e2, e3]
  exact finestra_quadrupla P hreg F hn s hs5
    (schlafli_ge_tre_all P hreg F hn ⟨s, by omega⟩ (show s + 1 < n by omega))
    (schlafli_ge_tre_all P hreg F hn ⟨s + 1, by omega⟩ (show s + 1 + 1 < n by omega))
    (schlafli_ge_tre_all P hreg F hn ⟨s + 2, by omega⟩ (show s + 2 + 1 < n by omega))
    (schlafli_ge_tre_all P hreg F hn ⟨s + 3, by omega⟩ (show s + 3 + 1 < n by omega))

/-- **ESCLUSIVITÀ ALTO-DIMENSIONALE**: per `d ≥ 5`, il simbolo di Schläfli di
un politopo regolare è `(3…3)`, `(4,3…3)` oppure `(3…3,4)`.  Il doppio-4 è escluso
dal ponte di Sylvester (`D_d > 0`) contro la formula chiusa (`D_d = 0`). -/
theorem schlafli_high_dim_exclusive {d : ℕ} (P : ConvexPolytope d)
    (hreg : P.IsRegular) (F : P.Flag) (hd : 5 ≤ d) :
    allThree (schlafliFun P hreg F) (d - 1) ∨ leftFour (schlafliFun P hreg F) (d - 1) ∨
      rightFour (schlafliFun P hreg F) (d - 1) := by
  have hn : 3 ≤ d := by omega
  rcases propagazione (schlafliFun P hreg F) (d - 1) (by omega)
      (finestraPattern_schlafli P hreg F hn) with h3 | h4L | h4R | h44
  · exact Or.inl h3
  · exact Or.inr (Or.inl h4L)
  · exact Or.inr (Or.inr h4R)
  · exfalso
    obtain ⟨h0, hmid, hL1⟩ := h44
    have link : ∀ j, j + 1 < d →
        (coxeterCoeff P hreg F j) ^ 2 = Real.cos (π / (schlafliFun P hreg F j : ℝ)) ^ 2 := by
      intro j hj
      rw [coxeterCoeff_eq_cos_schlafli P hreg F j (by omega) hj, schlafliFun_eq P hreg F j hj]
    have hc0 : (coxeterCoeff P hreg F 0) ^ 2 = 1 / 2 := by
      rw [link 0 (by omega), h0, show ((4 : ℕ) : ℝ) = 4 by norm_num, cos_pi_div_four_sq]
    have hcL : (coxeterCoeff P hreg F ((d - 1) - 1)) ^ 2 = 1 / 2 := by
      rw [link ((d - 1) - 1) (by omega), hL1, show ((4 : ℕ) : ℝ) = 4 by norm_num,
        cos_pi_div_four_sq]
    have hci : ∀ i, 1 ≤ i → i ≤ (d - 1) - 2 →
        (coxeterCoeff P hreg F i) ^ 2 = 1 / 4 := by
      intro i hi1 hi2
      rw [link i (by omega), hmid i hi1 (by omega), show ((3 : ℕ) : ℝ) = 3 by norm_num,
        cos_pi_div_three_sq]
    have hmin : 0 < minoreGram (coxeterCoeff P hreg F) ((d - 1) + 1) := by
      rw [show (d - 1) + 1 = d from by omega]
      exact canonicalGram_positive_minori P hreg F hn d (le_refl d)
    exact doppio_quattro_impossibile (coxeterCoeff P hreg F) (d - 1) (by omega) hc0 hci hcL hmin

end LeanEval.Geometry.PlatonicClassification
