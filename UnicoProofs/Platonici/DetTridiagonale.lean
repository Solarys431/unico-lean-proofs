import Mathlib
import UnicoProofs.Platonici.Minori

/-!
S4 — IL DETERMINANTE TRIDIAGONALE (kill-gate del ponte di Sylvester, 20 lug 2026).

La matrice di Gram canonica, ristretta alle prime `k` righe/colonne, è
tridiagonale simmetrica con diagonale 1 e sottodiagonale `-cᵢ`.  Il suo
determinante segue la ricorrenza `Dₖ₊₂ = Dₖ₊₁ − cₖ²·Dₖ`, cioè `minoreGram`.

La prova del passo induttivo è una doppia espansione di Laplace:
* sull'ultima colonna (indice `k+1`): sopravvivono solo `i = k+1` (segno +,
  minore `= tridiag (k+1)`) e `i = k` (segno −, entrata `-cₖ`);
* il minore laterale di `i = k` si espande sull'ultima riga: sopravvive solo
  l'entrata `(k,k) = -cₖ`, minore `= tridiag k`.
Netto: `Dₖ₊₂ = Dₖ₊₁ + cₖ·(-cₖ·Dₖ) = Dₖ₊₁ − cₖ²·Dₖ`.
-/

open Matrix

namespace LeanEval.Geometry.PlatonicClassification

/-- La matrice tridiagonale simmetrica: diagonale 1, off-diagonale `-cᵢ`. -/
def tridiag (c : ℕ → ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of (fun i j =>
    if i = j then 1
    else if (i : ℕ) + 1 = (j : ℕ) then - c i
    else if (j : ℕ) + 1 = (i : ℕ) then - c j
    else 0)

theorem tridiag_apply (c : ℕ → ℝ) (k : ℕ) (i j : Fin k) :
    tridiag c k i j =
      if i = j then 1
      else if (i : ℕ) + 1 = (j : ℕ) then - c i
      else if (j : ℕ) + 1 = (i : ℕ) then - c j
      else 0 := rfl

/-- Rimuovendo l'ultima riga e colonna si ottiene `tridiag (k+1)`. -/
theorem tridiag_submatrix_last (c : ℕ → ℝ) (k : ℕ) :
    (tridiag c (k+2)).submatrix (Fin.last (k+1)).succAbove (Fin.last (k+1)).succAbove
      = tridiag c (k+1) := by
  ext i j
  simp only [Matrix.submatrix_apply, Fin.succAbove_last, tridiag, Matrix.of_apply,
    Fin.val_castSucc, Fin.castSucc_inj]

/-- **Il minore laterale**: cancellando la riga `k` e la colonna `k+1` dalla
tridiagonale `(k+2)×(k+2)`, il determinante vale `-cₖ · det(tridiag k)`.
Espansione di Laplace sull'ultima riga: unica entrata non nulla `(k,k) = -cₖ`. -/
theorem minore_laterale (c : ℕ → ℝ) (k : ℕ) :
    ((tridiag c (k+2)).submatrix (Fin.last k).castSucc.succAbove
      (Fin.last (k+1)).succAbove).det = - c k * (tridiag c k).det := by
  have hra : ∀ x : Fin k,
      ((Fin.last k).castSucc.succAbove ((Fin.last k).succAbove x) : ℕ) = (x : ℕ) := by
    intro x; rw [Fin.succAbove_last, Fin.succAbove_of_castSucc_lt]
    · simp
    · exact Fin.castSucc_lt_castSucc_iff.mpr (Fin.castSucc_lt_last x)
  have hcb : ∀ x : Fin k,
      (((Fin.last (k+1)).succAbove) ((Fin.last k).succAbove x) : ℕ) = (x : ℕ) := by
    intro x; rw [Fin.succAbove_last, Fin.succAbove_last]; simp
  have hplast : (Fin.last k).castSucc.succAbove (Fin.last k) = Fin.last (k+1) := by
    rw [Fin.succAbove_of_lt_succ] <;> simp [Fin.castSucc_lt_last]
  rw [Matrix.det_succ_row _ (Fin.last k)]
  rw [Finset.sum_eq_single (Fin.last k)]
  · have hsub : (((tridiag c (k+2)).submatrix (Fin.last k).castSucc.succAbove
        (Fin.last (k+1)).succAbove).submatrix (Fin.last k).succAbove (Fin.last k).succAbove)
        = tridiag c k := by
      rw [Matrix.submatrix_submatrix]
      ext a b
      have hcond : ((Fin.last k).castSucc.succAbove ((Fin.last k).succAbove a)
          = (Fin.last (k+1)).succAbove ((Fin.last k).succAbove b)) = (a = b) := by
        apply propext
        constructor
        · intro h; apply Fin.ext
          have := congrArg (Fin.val) h; rw [hra, hcb] at this; exact this
        · intro h; apply Fin.ext; rw [hra, hcb, Fin.ext_iff] at *; exact h
      simp only [Matrix.submatrix_apply, Function.comp_apply, tridiag, Matrix.of_apply,
        hra, hcb, hcond]
    rw [hsub]
    have hentry : (tridiag c (k+2)).submatrix (Fin.last k).castSucc.succAbove
        (Fin.last (k+1)).succAbove (Fin.last k) (Fin.last k) = - c k := by
      simp only [Matrix.submatrix_apply, hplast, Fin.succAbove_last, tridiag, Matrix.of_apply]
      rw [if_neg (by apply Fin.ne_of_val_ne; simp only [Fin.val_last, Fin.val_castSucc]; omega),
          if_neg (by simp only [Fin.val_last, Fin.val_castSucc]; omega),
          if_pos (by simp only [Fin.val_last, Fin.val_castSucc])]
      simp only [Fin.val_castSucc, Fin.val_last]
    rw [hentry]; simp [Fin.val_last]
  · intro b _ hb
    have hz : (tridiag c (k+2)).submatrix (Fin.last k).castSucc.succAbove
        (Fin.last (k+1)).succAbove (Fin.last k) b = 0 := by
      simp only [Matrix.submatrix_apply, hplast, Fin.succAbove_last]
      have hblt : (b : ℕ) < k := by
        rcases Nat.lt_or_ge (b:ℕ) k with h | h
        · exact h
        · exact absurd (Fin.ext (Nat.le_antisymm (Nat.lt_succ_iff.mp b.isLt) h)) hb
      simp only [tridiag, Matrix.of_apply, Fin.val_last, Fin.val_castSucc]
      rw [if_neg (by rw [Fin.ext_iff]; simp only [Fin.val_last, Fin.val_castSucc]; omega),
          if_neg (by omega), if_neg (by omega)]
    rw [hz]; ring
  · simp

/-- **Il passo della ricorrenza**: `Dₖ₊₂ = Dₖ₊₁ − cₖ²·Dₖ` per il determinante
tridiagonale, via espansione sull'ultima colonna e il minore laterale. -/
theorem det_tridiag_succ_succ (c : ℕ → ℝ) (k : ℕ) :
    (tridiag c (k+2)).det = (tridiag c (k+1)).det - (c k)^2 * (tridiag c k).det := by
  rw [Matrix.det_succ_column _ (Fin.last (k+1)), Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hrest : ∀ i : Fin k,
      (-1:ℝ) ^ ((Fin.castSucc (Fin.castSucc i) : Fin (k+2)) + Fin.last (k+1) : ℕ)
      * (tridiag c (k+2)) (Fin.castSucc (Fin.castSucc i)) (Fin.last (k+1))
      * ((tridiag c (k+2)).submatrix (Fin.castSucc (Fin.castSucc i)).succAbove
          (Fin.last (k+1)).succAbove).det = 0 := by
    intro i
    have hz : (tridiag c (k+2)) (Fin.castSucc (Fin.castSucc i)) (Fin.last (k+1)) = 0 := by
      simp only [tridiag, Matrix.of_apply, Fin.val_last, Fin.val_castSucc]
      rw [if_neg (by rw [Fin.ext_iff]; simp only [Fin.val_last, Fin.val_castSucc]; omega),
          if_neg (by omega), if_neg (by omega)]
    rw [hz]; ring
  rw [Finset.sum_eq_zero (fun i _ => hrest i), zero_add]
  rw [tridiag_submatrix_last]
  have hB2 : (tridiag c (k+2)) (Fin.castSucc (Fin.last k)) (Fin.last (k+1)) = - c k := by
    simp only [tridiag, Matrix.of_apply, Fin.val_last, Fin.val_castSucc]
    rw [if_neg (by rw [Fin.ext_iff]; simp only [Fin.val_last, Fin.val_castSucc]; omega),
        if_pos (by simp only [Fin.val_last, Fin.val_castSucc])]
  have hB1 : (tridiag c (k+2)) (Fin.last (k+1)) (Fin.last (k+1)) = 1 := by
    simp [tridiag]
  rw [hB2, hB1, minore_laterale]
  have hs1 : (-1:ℝ) ^ ((Fin.castSucc (Fin.last k) : Fin (k+2)) + Fin.last (k+1) : ℕ) = -1 := by
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [show (k:ℕ) + (k+1) = 2*k+1 by ring, pow_succ, pow_mul]; norm_num
  have hs2 : (-1:ℝ) ^ ((Fin.last (k+1) : Fin (k+2)) + Fin.last (k+1) : ℕ) = 1 := by
    simp only [Fin.val_last]
    rw [show (k+1) + (k+1) = 2*(k+1) by ring, pow_mul]; norm_num
  rw [hs1, hs2]; ring

/-- **S4 — il determinante tridiagonale è il minore di Gram.** -/
theorem det_tridiagonale (c : ℕ → ℝ) (k : ℕ) :
    (tridiag c k).det = minoreGram c k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [tridiag, minoreGram]
  | one => simp [tridiag, minoreGram, Matrix.det_unique]
  | more n ih1 ih2 => rw [det_tridiag_succ_succ, minoreGram_succ_succ, ih1, ih2]

end LeanEval.Geometry.PlatonicClassification
