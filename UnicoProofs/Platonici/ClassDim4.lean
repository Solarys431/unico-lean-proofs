import Mathlib
import UnicoProofs.Platonici.Minori
import UnicoProofs.Platonici.MinoriAurei

/-!
CLASSIFICAZIONE DELLE STRINGHE POSITIVE IN DIMENSIONE 4 (19 lug 2026).

Target C3 del contratto maestro. Una stringa `(m₀, m₁, m₂)` con `mᵢ ≥ 3` la
cui matrice di Coxeter tridiagonale è definita positiva (criterio di
Sylvester: tutti i minori principali positivi) è UNA delle sei:

  (3,3,3)  (4,3,3)  (3,3,4)  (3,4,3)  (5,3,3)  (3,3,5)

corrispondenti a 5-cell, 8-cell, 16-cell, 24-cell, 120-cell, 600-cell.

La strada: la positività del minore di rango 3 forza ogni ordine ≤ 5
(perché `cos²(π/m)` è crescente e due voci `≥ 4` saturano già a 1), poi
una verifica finita sui casi `{3,4,5}³` con i valori esatti dei coseni.
-/

open Real

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

/-- Soglia: per `m ≥ 6`, `cos²(π/m) ≥ 3/4`. -/
theorem cos_sq_ge_of_six {m : ℕ} (hm : 6 ≤ m) : (3 : ℝ) / 4 ≤ Real.cos (π / m) ^ 2 := by
  have h := cos_sq_mono (m := 6) (m' := m) (by norm_num) hm
  have h6 : ((6 : ℕ) : ℝ) = 6 := by norm_num
  rw [h6, cos_pi_div_six_sq] at h
  exact h

/-- Soglia: per `m ≥ 3`, `cos²(π/m) ≥ 1/4`. -/
theorem cos_sq_ge_of_three {m : ℕ} (hm : 3 ≤ m) : (1 : ℝ) / 4 ≤ Real.cos (π / m) ^ 2 := by
  have h := cos_sq_mono (m := 3) (m' := m) (by norm_num) hm
  have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [h3, cos_pi_div_three_sq] at h
  exact h

/-- Se il minore di rango 3 è positivo, i due ordini coinvolti sono ≤ 5. -/
theorem ordini_le_five_di_D3 {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hD3 : 0 < 1 - Real.cos (π / a) ^ 2 - Real.cos (π / b) ^ 2) :
    a ≤ 5 ∧ b ≤ 5 := by
  constructor
  · by_contra h
    have ha6 : 6 ≤ a := by omega
    have h1 := cos_sq_ge_of_six ha6
    have h2 := cos_sq_ge_of_three hb
    linarith
  · by_contra h
    have hb6 : 6 ≤ b := by omega
    have h1 := cos_sq_ge_of_three ha
    have h2 := cos_sq_ge_of_six hb6
    linarith

/-- Valore esatto di `cos²(π/m)` per `m ∈ {3,4,5}`, come disgiunzione. -/
theorem cos_sq_val {m : ℕ} (h3 : 3 ≤ m) (h5 : m ≤ 5) :
    Real.cos (π / m) ^ 2 = 1/4 ∨ Real.cos (π / m) ^ 2 = 1/2 ∨
      Real.cos (π / m) ^ 2 = (3 + Real.sqrt 5) / 8 := by
  interval_cases m
  · left; rw [show ((3:ℕ):ℝ) = 3 by norm_num]; exact cos_pi_div_three_sq
  · right; left; rw [show ((4:ℕ):ℝ) = 4 by norm_num]; exact cos_pi_div_four_sq
  · right; right; rw [show ((5:ℕ):ℝ) = 5 by norm_num]; exact cos_pi_div_five_sq

set_option maxHeartbeats 4000000 in
/-- **CLASSIFICAZIONE IN DIMENSIONE 4.** Una stringa `(a,b,c)` con ogni
ordine `≥ 3` la cui matrice di Coxeter tridiagonale è definita positiva
(i tre minori principali `D₂, D₃, D₄` positivi) è una delle SEI
ammesse. -/
theorem classificazione_dim4 (a b c : ℕ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c)
    (hD3 : 0 < 1 - Real.cos (π / a) ^ 2 - Real.cos (π / b) ^ 2)
    (hD4 : 0 < 1 - Real.cos (π / a) ^ 2 - Real.cos (π / b) ^ 2
      - Real.cos (π / c) ^ 2
      + Real.cos (π / a) ^ 2 * Real.cos (π / c) ^ 2) :
    (a = 3 ∧ b = 3 ∧ c = 3) ∨ (a = 4 ∧ b = 3 ∧ c = 3) ∨
    (a = 3 ∧ b = 3 ∧ c = 4) ∨ (a = 3 ∧ b = 4 ∧ c = 3) ∨
    (a = 5 ∧ b = 3 ∧ c = 3) ∨ (a = 3 ∧ b = 3 ∧ c = 5) := by
  -- a, b ≤ 5 dal minore di rango 3
  obtain ⟨ha5, hb5⟩ := ordini_le_five_di_D3 ha hb hD3
  -- c ≤ 5: se c ≥ 6, cos²(π/c) ≥ 3/4 e il minore D₄ diventa ≤ 0
  have hc5 : c ≤ 5 := by
    by_contra h
    have hc6 : 6 ≤ c := by omega
    have hcc := cos_sq_ge_of_six hc6
    have haa := cos_sq_ge_of_three ha
    have hbb := cos_sq_ge_of_three hb
    -- D₄ = D₃ - cos²(π/c)·(1 - cos²(π/a)) ≤ D₃ - (3/4)·(1 - cos²(π/a))
    -- con cos²(π/a) ≤ 1 (sempre) e i bound: contraddizione
    have hca1 : Real.cos (π / a) ^ 2 ≤ 1 := by
      have := Real.neg_one_le_cos (π / a)
      have := Real.cos_le_one (π / a)
      nlinarith [Real.cos_le_one (π / a), Real.neg_one_le_cos (π / a)]
    nlinarith [hcc, haa, hbb, hca1, hD4, hD3]
  -- ora a, b, c ∈ {3,4,5}: verifica finita
  obtain ⟨lo, hi⟩ := sqrt_five_bounds
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    simp only [show ((3:ℕ):ℝ) = 3 by norm_num, show ((4:ℕ):ℝ) = 4 by norm_num,
      show ((5:ℕ):ℝ) = 5 by norm_num, cos_pi_div_three_sq, cos_pi_div_four_sq,
      cos_pi_div_five_sq] at hD3 hD4 ⊢ <;>
    first
      | tauto
      | (exfalso; nlinarith [lo, hi, hD3, hD4])

end LeanEval.Geometry.PlatonicClassification
