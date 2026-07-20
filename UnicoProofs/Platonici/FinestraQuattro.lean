import Mathlib
import UnicoProofs.Platonici.QuadrupleAmmesse

/-!
FINESTRA DI QUATTRO ARCHI (20 lug 2026) — il collegamento geometrico → quadrupla.

Ogni finestra di 4 archi consecutivi di un politopo regolare, con ordini ≥ 3, è
`3333`, `4333` o `3334`.  Salda le due triple classificate (`finestra_classificata`
su `s` e `s+1`) e la positività del minore di rango 5 (`window_minori_positivi`)
a `quadrupla_classificata`.
-/

open Real

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- **Ogni finestra di quattro archi è `3333`, `4333` o `3334`.** -/
theorem finestra_quadrupla (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (hn : 3 ≤ n) (s : ℕ) (hs5 : s + 5 ≤ n)
    (ha : 3 ≤ schlafli P hreg F ⟨s, by omega⟩)
    (hb : 3 ≤ schlafli P hreg F ⟨s + 1, by omega⟩)
    (hc : 3 ≤ schlafli P hreg F ⟨s + 2, by omega⟩)
    (hd : 3 ≤ schlafli P hreg F ⟨s + 3, by omega⟩) :
    (schlafli P hreg F ⟨s, by omega⟩ = 3 ∧ schlafli P hreg F ⟨s + 1, by omega⟩ = 3 ∧
        schlafli P hreg F ⟨s + 2, by omega⟩ = 3 ∧ schlafli P hreg F ⟨s + 3, by omega⟩ = 3) ∨
      (schlafli P hreg F ⟨s, by omega⟩ = 4 ∧ schlafli P hreg F ⟨s + 1, by omega⟩ = 3 ∧
        schlafli P hreg F ⟨s + 2, by omega⟩ = 3 ∧ schlafli P hreg F ⟨s + 3, by omega⟩ = 3) ∨
      (schlafli P hreg F ⟨s, by omega⟩ = 3 ∧ schlafli P hreg F ⟨s + 1, by omega⟩ = 3 ∧
        schlafli P hreg F ⟨s + 2, by omega⟩ = 3 ∧ schlafli P hreg F ⟨s + 3, by omega⟩ = 4) := by
  have hleft := finestra_classificata P hreg F hn s (by omega) ha hb hc
  have hright := finestra_classificata P hreg F hn (s + 1) (by omega) hb hc hd
  simp only [show s + 1 + 1 = s + 2 from rfl, show s + 1 + 2 = s + 3 from rfl] at hright
  have h0 : coxeterCoeff P hreg F s
      = Real.cos (π / (schlafli P hreg F ⟨s, by omega⟩ : ℝ)) :=
    coxeterCoeff_eq_cos_schlafli P hreg F s (by omega) (by omega)
  have h1 : coxeterCoeff P hreg F (s + 1)
      = Real.cos (π / (schlafli P hreg F ⟨s + 1, by omega⟩ : ℝ)) :=
    coxeterCoeff_eq_cos_schlafli P hreg F (s + 1) (by omega) (by omega)
  have h2 : coxeterCoeff P hreg F (s + 2)
      = Real.cos (π / (schlafli P hreg F ⟨s + 2, by omega⟩ : ℝ)) :=
    coxeterCoeff_eq_cos_schlafli P hreg F (s + 2) (by omega) (by omega)
  have h3 : coxeterCoeff P hreg F (s + 3)
      = Real.cos (π / (schlafli P hreg F ⟨s + 3, by omega⟩ : ℝ)) :=
    coxeterCoeff_eq_cos_schlafli P hreg F (s + 3) (by omega) (by omega)
  have hD5 := window_minori_positivi P hreg F hn s 5 (by omega)
  rw [minoreGram_cinque] at hD5
  simp only [Nat.add_zero, h0, h1, h2, h3] at hD5
  exact quadrupla_classificata _ _ _ _ hleft hright hD5

end LeanEval.Geometry.PlatonicClassification
