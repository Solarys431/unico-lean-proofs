import Mathlib

/-!
PROPAGAZIONE DELLE FINESTRE (20 lug 2026) — modulo combinatorio esplicito.

Se ogni finestra consecutiva di quattro archi è `3333`, `4333` o `3334`, allora
l'intera stringa di `L` archi è una delle quattro forme:
`(3…3)`, `(4,3…3)`, `(3…3,4)`, `(4,3…3,4)`.  Le posizioni interne sono forzate
a `3` perché ciascuna è centrale in almeno una finestra (dove le due posizioni
centrali valgono sempre `3`).  Restano libere solo le due estremità.
-/

namespace LeanEval.Geometry.PlatonicClassification

/-- Ipotesi di finestra: ogni blocco di 4 archi è `3333`, `4333` o `3334`. -/
def FinestraPattern (m : ℕ → ℕ) (L : ℕ) : Prop :=
  ∀ s, s + 4 ≤ L →
    (m s = 3 ∧ m (s + 1) = 3 ∧ m (s + 2) = 3 ∧ m (s + 3) = 3) ∨
    (m s = 4 ∧ m (s + 1) = 3 ∧ m (s + 2) = 3 ∧ m (s + 3) = 3) ∨
    (m s = 3 ∧ m (s + 1) = 3 ∧ m (s + 2) = 3 ∧ m (s + 3) = 4)

/-- Tutti gli archi valgono 3. -/
def allThree (m : ℕ → ℕ) (L : ℕ) : Prop := ∀ i, i < L → m i = 3

/-- Un 4 al primo estremo, il resto 3. -/
def leftFour (m : ℕ → ℕ) (L : ℕ) : Prop :=
  m 0 = 4 ∧ ∀ i, 1 ≤ i → i < L → m i = 3

/-- Un 4 all'ultimo estremo, il resto 3. -/
def rightFour (m : ℕ → ℕ) (L : ℕ) : Prop :=
  (∀ i, i < L - 1 → m i = 3) ∧ m (L - 1) = 4

/-- Un 4 a entrambi gli estremi, il resto 3 (residuo, poi escluso). -/
def doubleFour (m : ℕ → ℕ) (L : ℕ) : Prop :=
  m 0 = 4 ∧ (∀ i, 1 ≤ i → i < L - 1 → m i = 3) ∧ m (L - 1) = 4

/-- **Ogni posizione interna è forzata a 3.** -/
theorem interna_tre (m : ℕ → ℕ) (L : ℕ) (hL : 4 ≤ L)
    (hwin : FinestraPattern m L) (i : ℕ) (hi1 : 1 ≤ i) (hiL : i + 1 < L) :
    m i = 3 := by
  by_cases h : i + 3 ≤ L
  · have hw := hwin (i - 1) (by omega)
    have he : i - 1 + 1 = i := by omega
    rcases hw with ⟨_, h1, _, _⟩ | ⟨_, h1, _, _⟩ | ⟨_, h1, _, _⟩ <;>
      (rw [he] at h1; exact h1)
  · have hw := hwin (L - 4) (by omega)
    have he : L - 4 + 2 = i := by omega
    rcases hw with ⟨_, _, h2, _⟩ | ⟨_, _, h2, _⟩ | ⟨_, _, h2, _⟩ <;>
      (rw [he] at h2; exact h2)

/-- **La propagazione**: la stringa è una delle quattro forme. -/
theorem propagazione (m : ℕ → ℕ) (L : ℕ) (hL : 4 ≤ L)
    (hwin : FinestraPattern m L) :
    allThree m L ∨ leftFour m L ∨ rightFour m L ∨ doubleFour m L := by
  have hint : ∀ i, 1 ≤ i → i + 1 < L → m i = 3 := interna_tre m L hL hwin
  have h0 : m 0 = 3 ∨ m 0 = 4 := by
    rcases hwin 0 (by omega) with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl h
  have hLm1 : m (L - 1) = 3 ∨ m (L - 1) = 4 := by
    have he : L - 4 + 3 = L - 1 := by omega
    rcases hwin (L - 4) (by omega) with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;>
      rw [he] at h
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
  -- copertura di ogni posizione: 0, interne, L-1
  have hcover : ∀ i, 1 ≤ i → i < L - 1 → m i = 3 := by
    intro i hi1 hi; exact hint i hi1 (by omega)
  rcases h0 with h0 | h0 <;> rcases hLm1 with hL1 | hL1
  · -- (3,3): allThree
    refine Or.inl ?_
    intro i hi
    rcases Nat.lt_or_ge i 1 with h | h
    · have : i = 0 := by omega
      rw [this]; exact h0
    · rcases Nat.lt_or_ge i (L - 1) with h' | h'
      · exact hcover i h h'
      · have : i = L - 1 := by omega
        rw [this]; exact hL1
  · -- (3,4): rightFour
    refine Or.inr (Or.inr (Or.inl ⟨?_, hL1⟩))
    intro i hi
    rcases Nat.lt_or_ge i 1 with h | h
    · have : i = 0 := by omega
      rw [this]; exact h0
    · exact hcover i h hi
  · -- (4,3): leftFour
    refine Or.inr (Or.inl ⟨h0, ?_⟩)
    intro i hi1 hi
    rcases Nat.lt_or_ge i (L - 1) with h' | h'
    · exact hcover i hi1 h'
    · have : i = L - 1 := by omega
      rw [this]; exact hL1
  · -- (4,4): doubleFour
    exact Or.inr (Or.inr (Or.inr ⟨h0, hcover, hL1⟩))

end LeanEval.Geometry.PlatonicClassification
