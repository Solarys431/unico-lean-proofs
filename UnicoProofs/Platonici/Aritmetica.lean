import Mathlib

/-- L'aritmetica finale della campagna #50: dalla disuguaglianza di Schläfli
`q(p−2) < 2p` con p,q ≥ 3 seguono ESATTAMENTE le cinque coppie platoniche.
(Il quarto lemma portante del disegno di gate.) -/
theorem nat_pairs_of_schlafli (p q : ℕ) (hp : 3 ≤ p) (hq : 3 ≤ q)
    (h : q * (p - 2) < 2 * p) :
    (p = 3 ∧ q = 3) ∨ (p = 4 ∧ q = 3) ∨ (p = 3 ∧ q = 4) ∨
    (p = 5 ∧ q = 3) ∨ (p = 3 ∧ q = 5) := by
  have h3 : 3 * (p - 2) ≤ q * (p - 2) := Nat.mul_le_mul_right _ hq
  have hp5 : p ≤ 5 := by omega
  interval_cases p <;> omega
