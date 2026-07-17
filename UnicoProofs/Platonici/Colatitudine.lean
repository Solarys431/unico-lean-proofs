import Mathlib

/-!
A6 — LA COLATITUDINE STA SOTTO UNO (campagna #50, assemblaggio).

`puntatezza` (modulo Asse, certificato) dà 0 < ⟪uⱼ, w⟫. Qui l'altro verso:
per direzioni unitarie DISTINTE permutate ciclicamente, la colatitudine
normalizzata è strettamente sotto 1 — se un lato coincidesse con l'asse
normalizzato, la rotazione lo fisserebbe e la distinzione morirebbe.
Con A5 (`beta_di_colatitudine`) questo consegna β ∈ (0, π/2) allo Spike-0.
-/

open Real
open scoped RealInnerProductSpace

namespace PlatoniciA6

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- L'asse normalizzato è fissato dall'isometria del ciclo. -/
theorem asse_normalizzato_fisso {q : ℕ} (L : V ≃ₗᵢ[ℝ] V) (u : Fin q → V)
    (hL : ∀ i, L (u i) = u (finRotate q i)) :
    L (‖∑ i, u i‖⁻¹ • ∑ i, u i) = ‖∑ i, u i‖⁻¹ • ∑ i, u i := by
  rw [map_smul]
  congr 1
  rw [map_sum]
  simp_rw [hL]
  exact Equiv.sum_comp (finRotate q) u

/-- La colatitudine normalizzata di un lato unitario è < 1: il lato non può
essere l'asse, altrimenti la rotazione lo fisserebbe contro la distinzione. -/
theorem colatitudine_sotto_uno {n : ℕ} (hn : 1 ≤ n)
    (L : V ≃ₗᵢ[ℝ] V) (u : Fin (n + 1) → V)
    (hu : ∀ i, ‖u i‖ = 1)
    (hL : ∀ i, L (u i) = u (finRotate (n + 1) i))
    (hdist : Function.Injective u) (j : Fin (n + 1)) :
    ⟪u j, ‖∑ i, u i‖⁻¹ • ∑ i, u i⟫ < 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set w : V := ∑ i, u i with hw
  by_cases hw0 : w = 0
  · rw [hw0]
    simp
  · set ŵ : V := ‖w‖⁻¹ • w with hŵ
    have hŵ1 : ‖ŵ‖ = 1 := by
      rw [hŵ, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]
    rcases lt_or_eq_of_le
        (le_of_le_of_eq (real_inner_le_norm (u j) ŵ)
          (by rw [hu j, hŵ1, one_mul])) with hlt | heq
    · exact hlt
    · exfalso
      have hpar : u j = ŵ := by
        have h1 : ⟪u j, ŵ⟫ = ‖u j‖ * ‖ŵ‖ := by rw [hu j, hŵ1, one_mul, heq]
        have h2 := inner_eq_norm_mul_iff_real.mp h1
        rw [hu j, hŵ1, one_smul, one_smul] at h2
        exact h2
      have hnext : u (finRotate (m + 2) j) = u j := by
        rw [← hL j, hpar, hŵ, hw]
        rw [asse_normalizzato_fisso L u hL]
      have hfix : finRotate (m + 2) j = j := hdist hnext
      rw [finRotate_succ_apply] at hfix
      have hone : (1 : Fin (m + 2)) = 0 := by
        calc (1 : Fin (m + 2)) = j + 1 - j := by abel
          _ = j - j := by rw [hfix]
          _ = 0 := by abel
      have := congrArg Fin.val hone
      simp at this

end PlatoniciA6
