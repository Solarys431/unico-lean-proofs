import Mathlib
import UnicoProofs.Platonici.Minori

/-!
LE FORMULE CHIUSE DEI MINORI PER LE FAMIGLIE CANONICHE (19 lug 2026).

Fondamento della classificazione in dimensione ≥ 5. Le tre famiglie che
sopravvivono hanno minori con formula chiusa, tutti positivi:

  · simplesso `Aₙ` (tutti gli ordini 3): `Dₖ = (k+1)/2ᵏ`;
  · ipercubo/ortoplesse `Bₙ` (un 4 a un estremo, poi 3): `Dₖ = 1/2^{k-1}` per k ≥ 1.

Da qui: le tre famiglie danno matrici definite positive in ogni dimensione.
L'esclusività (nessun'altra stringa è positiva) è la parte induttiva, che
vive in un modulo suo.
-/

open Real

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

/-- La stringa costante `cos(π/3)`: il simplesso. -/
noncomputable def cTutti3 : ℕ → ℝ := fun _ => Real.cos (π / 3)

theorem cTutti3_sq (k : ℕ) : (cTutti3 k) ^ 2 = 1 / 4 := by
  unfold cTutti3
  rw [Real.cos_pi_div_three]
  norm_num

/-- **I minori del simplesso**: `Dₖ = (k+1)/2ᵏ`. Sempre positivi. -/
theorem minoreGram_simplesso (k : ℕ) :
    minoreGram cTutti3 k = (k + 1) / 2 ^ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [minoreGram]
    | 1 => simp [minoreGram]
    | (j + 2) =>
      rw [minoreGram_succ_succ, cTutti3_sq,
        ih (j + 1) (by omega), ih j (by omega)]
      have h2 : (2 : ℝ) ^ (j + 2) = 2 ^ j * 4 := by ring
      have h2' : (2 : ℝ) ^ (j + 1) = 2 ^ j * 2 := by ring
      have hpos : (0 : ℝ) < 2 ^ j := by positivity
      field_simp
      push_cast
      ring

theorem minoreGram_simplesso_pos (k : ℕ) : 0 < minoreGram cTutti3 k := by
  rw [minoreGram_simplesso]
  positivity

/-- La stringa `(4,3,3,…)`: l'ipercubo (e per dualità l'ortoplesse). -/
noncomputable def cQuattroPoi3 : ℕ → ℝ :=
  fun k => if k = 0 then Real.cos (π / 4) else Real.cos (π / 3)

theorem cQuattroPoi3_sq_zero : (cQuattroPoi3 0) ^ 2 = 1 / 2 := by
  unfold cQuattroPoi3
  rw [if_pos rfl, Real.cos_pi_div_four]
  rw [div_pow, Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
  norm_num

theorem cQuattroPoi3_sq_succ (k : ℕ) : (cQuattroPoi3 (k + 1)) ^ 2 = 1 / 4 := by
  unfold cQuattroPoi3
  rw [if_neg (by omega), Real.cos_pi_div_three]
  norm_num

/-- **I minori dell'ipercubo**: `Dₖ = 1/2^{k-1}` per `k ≥ 1`. Sempre positivi. -/
theorem minoreGram_ipercubo (k : ℕ) :
    minoreGram cQuattroPoi3 (k + 1) = 1 / 2 ^ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [minoreGram]
    | 1 =>
      rw [show (1 : ℕ) + 1 = 2 from rfl, minoreGram_succ_succ,
        cQuattroPoi3_sq_zero]
      simp [minoreGram]
      norm_num
    | (j + 2) =>
      rw [minoreGram_succ_succ, cQuattroPoi3_sq_succ,
        ih (j + 1) (by omega), ih j (by omega)]
      have hpos : (0 : ℝ) < 2 ^ j := by positivity
      have h2 : (2 : ℝ) ^ (j + 1) = 2 ^ j * 2 := by ring
      field_simp
      push_cast
      ring

theorem minoreGram_ipercubo_pos (k : ℕ) : 0 < minoreGram cQuattroPoi3 (k + 1) := by
  rw [minoreGram_ipercubo]
  positivity

theorem minoreGram_ipercubo_pos_all (k : ℕ) : 0 < minoreGram cQuattroPoi3 k := by
  match k with
  | 0 => simp [minoreGram]
  | (j + 1) => exact minoreGram_ipercubo_pos j

end LeanEval.Geometry.PlatonicClassification
