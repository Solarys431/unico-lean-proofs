import Mathlib
import UnicoProofs.Platonici.GramCanonica
import UnicoProofs.Platonici.GramPositiva
import UnicoProofs.Platonici.DetTridiagonale
import UnicoProofs.Platonici.Minori

/-!
IL PONTE DI SYLVESTER (20 lug 2026) — dal politopo regolare ai minori positivi.

Collega il mondo geometrico (`gram_canonica`) al classificatore astratto
(`minoreGram`).  Cammino: la Gram canonica dei normali orientati è definita
positiva (S1); ogni sua sottomatrice principale leading lo è (S2), dunque ha
determinante positivo (S3); quella leading È la tridiagonale (S5), il cui
determinante è il minore di Gram (S4, in `DetTridiagonale`); netto, i minori
di Gram del politopo sono positivi (S6, apicale).
-/

open Matrix
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- **S1 — la matrice di Gram** dei normali orientati. -/
noncomputable def gramMatrix (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ⟪normaleOrientato P hreg F i, normaleOrientato P hreg F j⟫

theorem gramMatrix_isHermitian (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) : (gramMatrix P hreg F).IsHermitian := by
  ext i j
  simp only [gramMatrix, Matrix.conjTranspose_apply, star_trivial, real_inner_comm]

/-- **S1 — la Gram è definita positiva** (forma forte). -/
theorem gramMatrix_posDef (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (hn : 3 ≤ n) : (gramMatrix P hreg F).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (gramMatrix_isHermitian P hreg F)
  intro x hx
  have hform := gram_canonica_forma_positiva P hreg F hn x hx
  have heq : star x ⬝ᵥ (gramMatrix P hreg F).mulVec x
      = ∑ i, ∑ j, x i * x j *
          ⟪normaleOrientato P hreg F i, normaleOrientato P hreg F j⟫ := by
    simp only [dotProduct, Matrix.mulVec, gramMatrix, star_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  rw [heq]; exact hform

/-- **S2 — le sottomatrici principali leading sono definite positive.** -/
theorem gram_leading_posDef (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (hn : 3 ≤ n) (k : ℕ) (hk : k ≤ n) :
    ((gramMatrix P hreg F).submatrix (Fin.castLE hk) (Fin.castLE hk)).PosDef :=
  (gramMatrix_posDef P hreg F hn).submatrix (Fin.castLE_injective hk)

/-- **S3 — il determinante di ogni minore principale leading è positivo.** -/
theorem gram_leading_det_pos (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (hn : 3 ≤ n) (k : ℕ) (hk : k ≤ n) :
    0 < ((gramMatrix P hreg F).submatrix (Fin.castLE hk) (Fin.castLE hk)).det :=
  (gram_leading_posDef P hreg F hn k hk).det_pos

/-- Il coefficiente dell'arco `(j, j+1)` del diagramma di Coxeter, come funzione
`ℕ → ℝ`: `cos(π / m_{j,j+1})` quando l'arco esiste, `0` oltre il bordo. -/
noncomputable def coxeterCoeff (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (j : ℕ) : ℝ :=
  if h : j + 1 < n then
    Real.cos (Real.pi / (coxeterMatrix P hreg F ⟨j, by omega⟩ ⟨j + 1, h⟩ : ℝ))
  else 0

/-- **S5 — la sottomatrice leading della Gram È la tridiagonale** dei coefficienti
di Coxeter. -/
theorem gram_leading_eq_tridiag (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (hn : 3 ≤ n) (k : ℕ) (hk : k ≤ n) :
    (gramMatrix P hreg F).submatrix (Fin.castLE hk) (Fin.castLE hk)
      = tridiag (coxeterCoeff P hreg F) k := by
  ext a b
  rw [Matrix.submatrix_apply, tridiag_apply]
  show ⟪normaleOrientato P hreg F (Fin.castLE hk a),
        normaleOrientato P hreg F (Fin.castLE hk b)⟫ = _
  have hava : ((Fin.castLE hk a : Fin n) : ℕ) = (a : ℕ) := rfl
  have havb : ((Fin.castLE hk b : Fin n) : ℕ) = (b : ℕ) := rfl
  by_cases hab : a = b
  · subst hab; rw [gram_diag_orientata, if_pos rfl]
  · have habv : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
    rw [if_neg hab]
    rcases lt_trichotomy (a : ℕ) (b : ℕ) with hlt | heq | hgt
    · by_cases hadj : (a : ℕ) + 1 = (b : ℕ)
      · rw [if_pos hadj]
        have hi : ((Fin.castLE hk a : Fin n) : ℕ) + 1 < n := by rw [hava]; omega
        have hjn : (a : ℕ) + 1 < n := by omega
        have hbeq : Fin.castLE hk b = ⟨((Fin.castLE hk a : Fin n) : ℕ) + 1, hi⟩ := by
          apply Fin.ext; change (b : ℕ) = (a : ℕ) + 1; omega
        have hcm : coxeterMatrix P hreg F (Fin.castLE hk a)
              ⟨((Fin.castLE hk a : Fin n) : ℕ) + 1, hi⟩
            = coxeterMatrix P hreg F ⟨(a : ℕ), by omega⟩ ⟨(a : ℕ) + 1, hjn⟩ := by
          congr 1
        rw [hbeq, gram_adiacente_orientata P hreg F (Fin.castLE hk a) hi hn,
            coxeterCoeff, dif_pos hjn, hcm]
      · rw [if_neg hadj, if_neg (by omega)]
        exact gram_lontane_orientata P hreg F (by rw [hava, havb]; omega)
    · exact absurd heq habv
    · rw [real_inner_comm]
      by_cases hadj : (b : ℕ) + 1 = (a : ℕ)
      · rw [if_neg (by omega), if_pos hadj]
        have hi : ((Fin.castLE hk b : Fin n) : ℕ) + 1 < n := by rw [havb]; omega
        have hjn : (b : ℕ) + 1 < n := by omega
        have haeq : Fin.castLE hk a = ⟨((Fin.castLE hk b : Fin n) : ℕ) + 1, hi⟩ := by
          apply Fin.ext; change (a : ℕ) = (b : ℕ) + 1; omega
        have hcm : coxeterMatrix P hreg F (Fin.castLE hk b)
              ⟨((Fin.castLE hk b : Fin n) : ℕ) + 1, hi⟩
            = coxeterMatrix P hreg F ⟨(b : ℕ), by omega⟩ ⟨(b : ℕ) + 1, hjn⟩ := by
          congr 1
        rw [haeq, gram_adiacente_orientata P hreg F (Fin.castLE hk b) hi hn,
            coxeterCoeff, dif_pos hjn, hcm]
      · rw [if_neg (by omega), if_neg hadj]
        exact gram_lontane_orientata P hreg F (by rw [hava, havb]; omega)

/-- **S6 — il ponte apicale**: i minori di Gram di un politopo regolare `d ≥ 3`
sono tutti strettamente positivi. -/
theorem canonicalGram_positive_minori (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (hn : 3 ≤ n) (k : ℕ) (hk : k ≤ n) :
    0 < minoreGram (coxeterCoeff P hreg F) k := by
  have h3 := gram_leading_det_pos P hreg F hn k hk
  rw [gram_leading_eq_tridiag P hreg F hn k hk, det_tridiagonale] at h3
  exact h3

end LeanEval.Geometry.PlatonicClassification
