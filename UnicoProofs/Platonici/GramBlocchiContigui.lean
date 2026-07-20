import Mathlib
import UnicoProofs.Platonici.PonteSylvester

/-!
BLOCCHI CONTIGUI DELLA GRAM (20 lug 2026) — i minori di ogni finestra positiva.

Il ponte di Sylvester dà i minori LEADING (dall'indice 0).  Per l'esclusività
alto-dimensionale servono i minori di OGNI finestra contigua di archi
`(s, s+1, …, s+k-1)`: la sottomatrice principale della Gram indicizzata da
`{s, …, s+k-1}` è definita positiva (l'embedding contiguo è iniettivo e
`PosDef.submatrix` non richiede che parta da 0), dunque il suo determinante
`minoreGram (coxeterCoeff ∘ (s+·)) k` è positivo.
-/

open Matrix
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- L'inclusione contigua `Fin k ↪ Fin n`, `j ↦ s + j`. -/
def embedWindow (s k : ℕ) (hsk : s + k ≤ n) : Fin k → Fin n :=
  fun j => ⟨s + j, by omega⟩

theorem embedWindow_injective (s k : ℕ) (hsk : s + k ≤ n) :
    Function.Injective (embedWindow s k hsk) := by
  intro a b hab
  apply Fin.ext
  have := congrArg Fin.val hab
  simp only [embedWindow] at this
  omega

/-- La finestra contigua della Gram è definita positiva. -/
theorem window_posDef (P : ConvexPolytope n) (hreg : P.IsRegular) (F : P.Flag)
    (hn : 3 ≤ n) (s k : ℕ) (hsk : s + k ≤ n) :
    ((gramMatrix P hreg F).submatrix (embedWindow s k hsk)
      (embedWindow s k hsk)).PosDef :=
  (gramMatrix_posDef P hreg F hn).submatrix (embedWindow_injective s k hsk)

/-- La finestra contigua della Gram È la tridiagonale dei coefficienti spostati. -/
theorem window_eq_tridiag (P : ConvexPolytope n) (hreg : P.IsRegular) (F : P.Flag)
    (hn : 3 ≤ n) (s k : ℕ) (hsk : s + k ≤ n) :
    (gramMatrix P hreg F).submatrix (embedWindow s k hsk) (embedWindow s k hsk)
      = tridiag (fun j => coxeterCoeff P hreg F (s + j)) k := by
  ext a b
  rw [Matrix.submatrix_apply, tridiag_apply]
  show ⟪normaleOrientato P hreg F (embedWindow s k hsk a),
        normaleOrientato P hreg F (embedWindow s k hsk b)⟫ = _
  have hava : ((embedWindow s k hsk a : Fin n) : ℕ) = s + (a : ℕ) := rfl
  have havb : ((embedWindow s k hsk b : Fin n) : ℕ) = s + (b : ℕ) := rfl
  by_cases hab : a = b
  · subst hab; rw [gram_diag_orientata, if_pos rfl]
  · have habv : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
    rw [if_neg hab]
    rcases lt_trichotomy (a : ℕ) (b : ℕ) with hlt | heq | hgt
    · by_cases hadj : (a : ℕ) + 1 = (b : ℕ)
      · rw [if_pos hadj]
        have hi : ((embedWindow s k hsk a : Fin n) : ℕ) + 1 < n := by rw [hava]; omega
        have hjn : s + (a : ℕ) + 1 < n := by omega
        have hbeq : embedWindow s k hsk b
            = ⟨((embedWindow s k hsk a : Fin n) : ℕ) + 1, hi⟩ := by
          apply Fin.ext; change s + (b : ℕ) = s + (a : ℕ) + 1; omega
        have hcm : coxeterMatrix P hreg F (embedWindow s k hsk a)
              ⟨((embedWindow s k hsk a : Fin n) : ℕ) + 1, hi⟩
            = coxeterMatrix P hreg F ⟨s + (a : ℕ), by omega⟩ ⟨s + (a : ℕ) + 1, hjn⟩ := by
          congr 1
        rw [hbeq, gram_adiacente_orientata P hreg F (embedWindow s k hsk a) hi hn,
            coxeterCoeff, dif_pos (by omega : s + (a : ℕ) + 1 < n), hcm]
      · rw [if_neg hadj, if_neg (by omega)]
        exact gram_lontane_orientata P hreg F (by rw [hava, havb]; omega)
    · exact absurd heq habv
    · rw [real_inner_comm]
      by_cases hadj : (b : ℕ) + 1 = (a : ℕ)
      · rw [if_neg (by omega), if_pos hadj]
        have hi : ((embedWindow s k hsk b : Fin n) : ℕ) + 1 < n := by rw [havb]; omega
        have hjn : s + (b : ℕ) + 1 < n := by omega
        have haeq : embedWindow s k hsk a
            = ⟨((embedWindow s k hsk b : Fin n) : ℕ) + 1, hi⟩ := by
          apply Fin.ext; change s + (a : ℕ) = s + (b : ℕ) + 1; omega
        have hcm : coxeterMatrix P hreg F (embedWindow s k hsk b)
              ⟨((embedWindow s k hsk b : Fin n) : ℕ) + 1, hi⟩
            = coxeterMatrix P hreg F ⟨s + (b : ℕ), by omega⟩ ⟨s + (b : ℕ) + 1, hjn⟩ := by
          congr 1
        rw [haeq, gram_adiacente_orientata P hreg F (embedWindow s k hsk b) hi hn,
            coxeterCoeff, dif_pos (by omega : s + (b : ℕ) + 1 < n), hcm]
      · rw [if_neg (by omega), if_neg hadj]
        exact gram_lontane_orientata P hreg F (by rw [hava, havb]; omega)

/-- **I minori di ogni finestra contigua sono positivi.** -/
theorem window_minori_positivi (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (hn : 3 ≤ n) (s k : ℕ) (hsk : s + k ≤ n) :
    0 < minoreGram (fun j => coxeterCoeff P hreg F (s + j)) k := by
  have hdet := (window_posDef P hreg F hn s k hsk).det_pos
  rw [window_eq_tridiag P hreg F hn s k hsk, det_tridiagonale] at hdet
  exact hdet

end LeanEval.Geometry.PlatonicClassification
