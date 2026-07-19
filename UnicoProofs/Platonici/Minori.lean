import Mathlib

/-!
MOTORE COXETER, PASSO 27 — I MINORI DELLA MATRICE TRIDIAGONALE
(19 lug 2026).

Il blocco algebrico della classificazione. Per una matrice di Coxeter a
STRINGA, con diagonale 1 e sottodiagonale `−cᵢ`, i minori principali
soddisfano la ricorrenza a tre termini

    D₀ = 1,  D₁ = 1,  D_{k+2} = D_{k+1} − c_k² · D_k

e la matrice è definita positiva esattamente quando tutti i minori sono
positivi (criterio di Sylvester).

Qui: la ricorrenza, i valori di `cos²(π/m)` per i casi che servono, e
i conti che eliminano le stringhe non ammesse. È algebra pura, senza
politopi: il ponte con la geometria vive altrove.
-/

open Real

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

/-- I minori principali della matrice tridiagonale con diagonale 1 e
sottodiagonale `−c k`. -/
noncomputable def minoreGram (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | (k + 2) => minoreGram c (k + 1) - (c k) ^ 2 * minoreGram c k

@[simp] theorem minoreGram_zero (c : ℕ → ℝ) : minoreGram c 0 = 1 := rfl

@[simp] theorem minoreGram_one (c : ℕ → ℝ) : minoreGram c 1 = 1 := rfl

theorem minoreGram_succ_succ (c : ℕ → ℝ) (k : ℕ) :
    minoreGram c (k + 2) =
      minoreGram c (k + 1) - (c k) ^ 2 * minoreGram c k := rfl

/-- Il coseno del passo elementare per `m = 3`. -/
theorem cos_pi_div_three_sq : Real.cos (π / 3) ^ 2 = 1 / 4 := by
  rw [Real.cos_pi_div_three]
  norm_num

/-- Il coseno del passo elementare per `m = 4`. -/
theorem cos_pi_div_four_sq : Real.cos (π / 4) ^ 2 = 1 / 2 := by
  rw [Real.cos_pi_div_four]
  rw [div_pow, Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
  norm_num

/-- Il coseno del passo elementare per `m = 6`. -/
theorem cos_pi_div_six_sq : Real.cos (π / 6) ^ 2 = 3 / 4 := by
  rw [Real.cos_pi_div_six]
  rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]
  norm_num

/-- La successione dei coseni quadri è crescente in `m`: più grande è
l'ordine, più la voce fuori diagonale pesa. -/
theorem cos_sq_mono {m m' : ℕ} (hm : 3 ≤ m) (hmm : m ≤ m') :
    Real.cos (π / m) ^ 2 ≤ Real.cos (π / m') ^ 2 := by
  have hmpos : (0 : ℝ) < m := by
    have : (3 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hm'pos : (0 : ℝ) < m' := by
    have : (m : ℝ) ≤ m' := by exact_mod_cast hmm
    linarith
  have hle : π / m' ≤ π / m := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le hmpos
    exact_mod_cast hmm
  have hlow : 0 ≤ π / m' := by positivity
  have hhigh : π / m ≤ π / 2 := by
    have h3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have h2m : (2 : ℝ) ≤ m := by linarith
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num : (0:ℝ) < 2) h2m
  have hcos : Real.cos (π / m) ≤ Real.cos (π / m') :=
    Real.cos_le_cos_of_nonneg_of_le_pi hlow (le_trans hhigh (by linarith [Real.pi_pos])) hle
  have hnn : 0 ≤ Real.cos (π / m) := by
    refine Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hlow], hhigh⟩
  nlinarith [hcos, hnn]

/-- **Il minore di rango 2**: `D₂ = 1 − c₀²`, positivo esattamente
quando `|c₀| < 1`. -/
theorem minoreGram_two (c : ℕ → ℝ) :
    minoreGram c 2 = 1 - (c 0) ^ 2 := by
  rw [minoreGram_succ_succ]
  simp

/-- **Il minore di rango 3**: `D₃ = 1 − c₀² − c₁²`. -/
theorem minoreGram_three (c : ℕ → ℝ) :
    minoreGram c 3 = 1 - (c 0) ^ 2 - (c 1) ^ 2 := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, minoreGram_succ_succ, minoreGram_two,
    minoreGram_one]
  ring

/-- **Il minore di rango 4**: `D₄ = 1 − c₀² − c₁² − c₂² + c₀²c₂²`. -/
theorem minoreGram_four (c : ℕ → ℝ) :
    minoreGram c 4 =
      1 - (c 0) ^ 2 - (c 1) ^ 2 - (c 2) ^ 2 + (c 0) ^ 2 * (c 2) ^ 2 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, minoreGram_succ_succ,
    minoreGram_three, minoreGram_two]
  ring

/-- **La stringa (3,3,3) è positiva**: è il simplesso `A₄`. -/
theorem positiva_333 (c : ℕ → ℝ)
    (h0 : (c 0) ^ 2 = 1 / 4) (h1 : (c 1) ^ 2 = 1 / 4)
    (h2 : (c 2) ^ 2 = 1 / 4) :
    0 < minoreGram c 4 := by
  rw [minoreGram_four, h0, h1, h2]
  norm_num

/-- **La stringa (4,3,3) è positiva**: è l'ipercubo `B₄`. -/
theorem positiva_433 (c : ℕ → ℝ)
    (h0 : (c 0) ^ 2 = 1 / 2) (h1 : (c 1) ^ 2 = 1 / 4)
    (h2 : (c 2) ^ 2 = 1 / 4) :
    0 < minoreGram c 4 := by
  rw [minoreGram_four, h0, h1, h2]
  norm_num

/-- **La stringa (3,4,3) è positiva**: è il 24-celle `F₄`. -/
theorem positiva_343 (c : ℕ → ℝ)
    (h0 : (c 0) ^ 2 = 1 / 4) (h1 : (c 1) ^ 2 = 1 / 2)
    (h2 : (c 2) ^ 2 = 1 / 4) :
    0 < minoreGram c 4 := by
  rw [minoreGram_four, h0, h1, h2]
  norm_num

/-- **La stringa (4,3,4) NON è positiva**: è il tassellamento cubico,
non un politopo. -/
theorem non_positiva_434 (c : ℕ → ℝ)
    (h0 : (c 0) ^ 2 = 1 / 2) (h1 : (c 1) ^ 2 = 1 / 4)
    (h2 : (c 2) ^ 2 = 1 / 2) :
    minoreGram c 4 = 0 := by
  rw [minoreGram_four, h0, h1, h2]
  norm_num

/-- **La stringa (4,4) NON è positiva**: tassellamento quadrato del
piano. -/
theorem non_positiva_44 (c : ℕ → ℝ)
    (h0 : (c 0) ^ 2 = 1 / 2) (h1 : (c 1) ^ 2 = 1 / 2) :
    minoreGram c 3 = 0 := by
  rw [minoreGram_three, h0, h1]
  norm_num

/-- **La stringa (3,6) NON è positiva**: tassellamento triangolare. -/
theorem non_positiva_36 (c : ℕ → ℝ)
    (h0 : (c 0) ^ 2 = 1 / 4) (h1 : (c 1) ^ 2 = 3 / 4) :
    minoreGram c 3 = 0 := by
  rw [minoreGram_three, h0, h1]
  norm_num

end LeanEval.Geometry.PlatonicClassification
