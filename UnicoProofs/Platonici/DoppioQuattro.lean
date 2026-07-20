import Mathlib
import UnicoProofs.Platonici.QuadrupleAmmesse

/-!
DOPPIO QUATTRO (20 lug 2026) — il residuo `(4,3,…,3,4)` ha minore globale nullo.

La coda "un 4 poi tutti 3" ha `D_k = (1/2)^{k-1}` (formula chiusa).  Con un
secondo 4 all'estremo, il passo finale della ricorrenza dà `D_d = D_{d-1} −
(1/2)·D_{d-2} = (1/2)^{d-2} − (1/2)^{d-2} = 0`.  Questo contraddice la
positività dei minori (ponte di Sylvester): il diagramma affine C̃ è degenere.
-/

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

/-- **La coda "4 poi tutti 3"**: `minoreGram c (k+1) = (1/2)^k` finché gli archi
usati restano nella coda (`c₀²=1/2`, gli interni `cᵢ²=1/4`). -/
theorem coda_pattern (c : ℕ → ℝ) (L : ℕ) (hc0 : (c 0) ^ 2 = 1 / 2)
    (hci : ∀ i, 1 ≤ i → i ≤ L - 2 → (c i) ^ 2 = 1 / 4) :
    ∀ k, k + 1 ≤ L → minoreGram c (k + 1) = (1 / 2) ^ k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => intro _; simp [minoreGram]
  | one => intro _; rw [minoreGram_due, hc0]; norm_num
  | more j ih1 ih2 =>
    intro hjL
    rw [show j + 2 + 1 = (j + 1) + 2 from by ring, minoreGram_succ_succ,
      ih2 (by omega), ih1 (by omega), hci (j + 1) (by omega) (by omega),
      pow_succ, pow_succ]
    ring

/-- **Il minore globale del doppio-4 è nullo.** -/
theorem doppio_quattro_D_zero (c : ℕ → ℝ) (L : ℕ) (hL : 2 ≤ L)
    (hc0 : (c 0) ^ 2 = 1 / 2) (hci : ∀ i, 1 ≤ i → i ≤ L - 2 → (c i) ^ 2 = 1 / 4)
    (hcL : (c (L - 1)) ^ 2 = 1 / 2) :
    minoreGram c (L + 1) = 0 := by
  have hcoda := coda_pattern c L hc0 hci
  have hDL : minoreGram c L = (1 / 2) ^ (L - 1) := by
    have := hcoda (L - 1) (by omega); rwa [show (L - 1) + 1 = L from by omega] at this
  have hDLm1 : minoreGram c (L - 1) = (1 / 2) ^ (L - 2) := by
    have := hcoda (L - 2) (by omega); rwa [show (L - 2) + 1 = L - 1 from by omega] at this
  rw [show L + 1 = (L - 1) + 2 from by omega, minoreGram_succ_succ, hcL,
    show (L - 1) + 1 = L from by omega, hDL, hDLm1,
    show L - 1 = (L - 2) + 1 from by omega, pow_succ]
  ring

/-- **Il doppio-4 è impossibile per un politopo regolare**: contraddice la
positività di tutti i minori. -/
theorem doppio_quattro_impossibile (c : ℕ → ℝ) (L : ℕ) (hL : 2 ≤ L)
    (hc0 : (c 0) ^ 2 = 1 / 2) (hci : ∀ i, 1 ≤ i → i ≤ L - 2 → (c i) ^ 2 = 1 / 4)
    (hcL : (c (L - 1)) ^ 2 = 1 / 2)
    (hmin : 0 < minoreGram c (L + 1)) : False := by
  rw [doppio_quattro_D_zero c L hL hc0 hci hcL] at hmin
  exact lt_irrefl 0 hmin

end LeanEval.Geometry.PlatonicClassification
