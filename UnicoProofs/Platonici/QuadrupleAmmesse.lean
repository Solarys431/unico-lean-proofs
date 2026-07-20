import Mathlib
import UnicoProofs.Platonici.TripleAmmesse

/-!
QUADRUPLE AMMESSE (20 lug 2026) — le sole quadruple positive sono tre.

Se le due triple sovrapposte `(a,b,c)` e `(b,c,d)` sono ammesse e il minore di
rango 5 è positivo, allora la quadrupla è `3333`, `4333` oppure `3334`.  La
ricorrenza del determinante annulla o rende negativo ogni altro caso.
-/

open Real

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

/-- Il minore di rango 5 in forma esplicita. -/
theorem minoreGram_cinque (c : ℕ → ℝ) :
    minoreGram c 5 = 1 - (c 0) ^ 2 - (c 1) ^ 2 - (c 2) ^ 2 - (c 3) ^ 2
      + (c 0) ^ 2 * (c 2) ^ 2 + (c 0) ^ 2 * (c 3) ^ 2 + (c 1) ^ 2 * (c 3) ^ 2 := by
  rw [show (5 : ℕ) = 3 + 2 from rfl, minoreGram_succ_succ, minoreGram_quattro,
    minoreGram_tre]; ring

set_option maxHeartbeats 3200000 in
/-- **Le sole quadruple positive sono `3333`, `4333`, `3334`.** Consuma le due
triple ammesse (finestre sovrapposte) e la positività del minore di rango 5. -/
theorem quadrupla_classificata (a b c d : ℕ)
    (hleft : (a = 3 ∧ b = 3 ∧ c = 3) ∨ (a = 4 ∧ b = 3 ∧ c = 3) ∨
        (a = 3 ∧ b = 3 ∧ c = 4) ∨ (a = 3 ∧ b = 4 ∧ c = 3) ∨
        (a = 5 ∧ b = 3 ∧ c = 3) ∨ (a = 3 ∧ b = 3 ∧ c = 5))
    (hright : (b = 3 ∧ c = 3 ∧ d = 3) ∨ (b = 4 ∧ c = 3 ∧ d = 3) ∨
        (b = 3 ∧ c = 3 ∧ d = 4) ∨ (b = 3 ∧ c = 4 ∧ d = 3) ∨
        (b = 5 ∧ c = 3 ∧ d = 3) ∨ (b = 3 ∧ c = 3 ∧ d = 5))
    (hD5 : 0 < 1 - Real.cos (π / a) ^ 2 - Real.cos (π / b) ^ 2
        - Real.cos (π / c) ^ 2 - Real.cos (π / d) ^ 2
        + Real.cos (π / a) ^ 2 * Real.cos (π / c) ^ 2
        + Real.cos (π / a) ^ 2 * Real.cos (π / d) ^ 2
        + Real.cos (π / b) ^ 2 * Real.cos (π / d) ^ 2) :
    (a = 3 ∧ b = 3 ∧ c = 3 ∧ d = 3) ∨ (a = 4 ∧ b = 3 ∧ c = 3 ∧ d = 3) ∨
      (a = 3 ∧ b = 3 ∧ c = 3 ∧ d = 4) := by
  obtain ⟨lo, hi⟩ := sqrt_five_bounds
  rcases hleft with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases hright with ⟨hb, hc, rfl⟩ | ⟨hb, hc, rfl⟩ | ⟨hb, hc, rfl⟩ |
        ⟨hb, hc, rfl⟩ | ⟨hb, hc, rfl⟩ | ⟨hb, hc, rfl⟩ <;>
    first
      | omega
      | (exfalso
         simp only [show ((3 : ℕ) : ℝ) = 3 by norm_num,
           show ((4 : ℕ) : ℝ) = 4 by norm_num, show ((5 : ℕ) : ℝ) = 5 by norm_num,
           cos_pi_div_three_sq, cos_pi_div_four_sq, cos_pi_div_five_sq] at hD5
         nlinarith [lo, hi, hD5])

end LeanEval.Geometry.PlatonicClassification
