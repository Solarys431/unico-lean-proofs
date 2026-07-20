import Mathlib
import UnicoProofs.Platonici.GramBlocchiContigui
import UnicoProofs.Platonici.ClassDim4
import UnicoProofs.Platonici.Schlafli

/-!
TRIPLE AMMESSE (20 lug 2026) — ogni finestra di 3 archi è una delle sei 4D.

I minori delle finestre contigue sono positivi (`window_minori_positivi`).  Il
minore di rango 3 è `1 − cos²(π/mₛ) − cos²(π/mₛ₊₁)` e quello di rango 4 è la
forma di `classificazione_dim4`.  Dunque ogni tripla consecutiva di ordini è
una delle sei: `333, 433, 334, 343, 533, 335`.
-/

open Real
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Il minore di rango 2 in forma esplicita. -/
theorem minoreGram_due (c : ℕ → ℝ) : minoreGram c 2 = 1 - (c 0) ^ 2 := by
  rw [minoreGram_succ_succ]; norm_num [minoreGram]

/-- Il minore di rango 3 in forma esplicita. -/
theorem minoreGram_tre (c : ℕ → ℝ) :
    minoreGram c 3 = 1 - (c 0) ^ 2 - (c 1) ^ 2 := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, minoreGram_succ_succ, minoreGram_due]
  norm_num [minoreGram]

/-- Il minore di rango 4 in forma esplicita. -/
theorem minoreGram_quattro (c : ℕ → ℝ) :
    minoreGram c 4 = 1 - (c 0) ^ 2 - (c 1) ^ 2 - (c 2) ^ 2
      + (c 0) ^ 2 * (c 2) ^ 2 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, minoreGram_succ_succ, minoreGram_tre,
    minoreGram_due]; ring

/-- Il coefficiente di Coxeter è il coseno dell'angolo del simbolo di Schläfli. -/
theorem coxeterCoeff_eq_cos (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (j : ℕ) (hj : j + 1 < n) :
    coxeterCoeff P hreg F j
      = Real.cos (Real.pi / (schlafliDi P hreg F ⟨j, by omega⟩ hj : ℝ)) := by
  rw [coxeterCoeff, dif_pos hj]
  rfl

/-- Il coefficiente di Coxeter come coseno dell'entrata della famiglia `schlafli`. -/
theorem coxeterCoeff_eq_cos_schlafli (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (j : ℕ) (hj0 : j < n) (hj : j + 1 < n) :
    coxeterCoeff P hreg F j
      = Real.cos (Real.pi / (schlafli P hreg F ⟨j, hj0⟩ : ℝ)) := by
  rw [coxeterCoeff_eq_cos P hreg F j hj, schlafli_apply P hreg F ⟨j, hj0⟩ hj]

/-- **Ogni finestra di tre archi consecutivi è una delle sei triple 4D.**
Salda `window_minori_positivi` (minori positivi) a `classificazione_dim4`. -/
theorem finestra_classificata (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (hn : 3 ≤ n) (s : ℕ) (hs4 : s + 4 ≤ n)
    (ha : 3 ≤ schlafli P hreg F ⟨s, by omega⟩)
    (hb : 3 ≤ schlafli P hreg F ⟨s + 1, by omega⟩)
    (hc : 3 ≤ schlafli P hreg F ⟨s + 2, by omega⟩) :
    (schlafli P hreg F ⟨s, by omega⟩ = 3 ∧
        schlafli P hreg F ⟨s + 1, by omega⟩ = 3 ∧
        schlafli P hreg F ⟨s + 2, by omega⟩ = 3) ∨
      (schlafli P hreg F ⟨s, by omega⟩ = 4 ∧
        schlafli P hreg F ⟨s + 1, by omega⟩ = 3 ∧
        schlafli P hreg F ⟨s + 2, by omega⟩ = 3) ∨
      (schlafli P hreg F ⟨s, by omega⟩ = 3 ∧
        schlafli P hreg F ⟨s + 1, by omega⟩ = 3 ∧
        schlafli P hreg F ⟨s + 2, by omega⟩ = 4) ∨
      (schlafli P hreg F ⟨s, by omega⟩ = 3 ∧
        schlafli P hreg F ⟨s + 1, by omega⟩ = 4 ∧
        schlafli P hreg F ⟨s + 2, by omega⟩ = 3) ∨
      (schlafli P hreg F ⟨s, by omega⟩ = 5 ∧
        schlafli P hreg F ⟨s + 1, by omega⟩ = 3 ∧
        schlafli P hreg F ⟨s + 2, by omega⟩ = 3) ∨
      (schlafli P hreg F ⟨s, by omega⟩ = 3 ∧
        schlafli P hreg F ⟨s + 1, by omega⟩ = 3 ∧
        schlafli P hreg F ⟨s + 2, by omega⟩ = 5) := by
  have hcos0 : coxeterCoeff P hreg F s
      = Real.cos (Real.pi / (schlafli P hreg F ⟨s, by omega⟩ : ℝ)) :=
    coxeterCoeff_eq_cos_schlafli P hreg F s (by omega) (by omega)
  have hcos1 : coxeterCoeff P hreg F (s + 1)
      = Real.cos (Real.pi / (schlafli P hreg F ⟨s + 1, by omega⟩ : ℝ)) :=
    coxeterCoeff_eq_cos_schlafli P hreg F (s + 1) (by omega) (by omega)
  have hcos2 : coxeterCoeff P hreg F (s + 2)
      = Real.cos (Real.pi / (schlafli P hreg F ⟨s + 2, by omega⟩ : ℝ)) :=
    coxeterCoeff_eq_cos_schlafli P hreg F (s + 2) (by omega) (by omega)
  have hD3 := window_minori_positivi P hreg F hn s 3 (by omega)
  rw [minoreGram_tre] at hD3
  have hD4 := window_minori_positivi P hreg F hn s 4 (by omega)
  rw [minoreGram_quattro] at hD4
  simp only [Nat.add_zero, hcos0, hcos1, hcos2] at hD3 hD4
  exact classificazione_dim4 _ _ _ ha hb hc hD3 hD4

end LeanEval.Geometry.PlatonicClassification
