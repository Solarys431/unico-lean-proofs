import Mathlib
import UnicoProofs.Platonici.Minori

/-!
MOTORE COXETER, PASSO 28 — LE STRINGHE AUREE E IL CONFINE
(19 lug 2026).

Le stringhe che contengono un 5 escono dai razionali: `cos(π/5)` è
`(1 + √5)/4` e il suo quadrato porta la sezione aurea. Qui i valori
esatti e le verifiche di positività per i due politopi quadridimensionali
aurei (600-celle e 120-celle), più i confini che devono cadere.

Poi il fatto che chiude la dimensione ≥ 5: la stringa `(3,3,5)` è
positiva in rango 4 ma NON in rango 5, ed è per questo che i solidi
aurei non hanno analoghi oltre la quarta dimensione.
-/

open Real

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

/-- Il valore esatto di `cos²(π/5)`: la sezione aurea al quadrato,
diviso quattro. -/
theorem cos_pi_div_five_sq :
    Real.cos (π / 5) ^ 2 = (3 + Real.sqrt 5) / 8 := by
  rw [Real.cos_pi_div_five]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith [h5, Real.sqrt_nonneg 5]

/-- Stime numeriche su `√5`, per i conti di positività. -/
theorem sqrt_five_bounds : 2.23 < Real.sqrt 5 ∧ Real.sqrt 5 < 2.24 := by
  constructor
  · have : (2.23 : ℝ) ^ 2 < 5 := by norm_num
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5),
      Real.sqrt_nonneg 5]
  · have : (5 : ℝ) < 2.24 ^ 2 := by norm_num
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5),
      Real.sqrt_nonneg 5]

/-- **La stringa (5,3,3) è positiva**: è il 120-celle. -/
theorem positiva_533 (c : ℕ → ℝ)
    (h0 : (c 0) ^ 2 = (3 + Real.sqrt 5) / 8) (h1 : (c 1) ^ 2 = 1 / 4)
    (h2 : (c 2) ^ 2 = 1 / 4) :
    0 < minoreGram c 4 := by
  rw [minoreGram_four, h0, h1, h2]
  obtain ⟨hlo, hhi⟩ := sqrt_five_bounds
  nlinarith [hlo, hhi]

/-- **La stringa (3,3,5) è positiva**: è il 600-celle. -/
theorem positiva_335 (c : ℕ → ℝ)
    (h0 : (c 0) ^ 2 = 1 / 4) (h1 : (c 1) ^ 2 = 1 / 4)
    (h2 : (c 2) ^ 2 = (3 + Real.sqrt 5) / 8) :
    0 < minoreGram c 4 := by
  rw [minoreGram_four, h0, h1, h2]
  obtain ⟨hlo, hhi⟩ := sqrt_five_bounds
  nlinarith [hlo, hhi]

/-- **La stringa (5,3) è positiva**: è il dodecaedro. -/
theorem positiva_53 (c : ℕ → ℝ)
    (h0 : (c 0) ^ 2 = (3 + Real.sqrt 5) / 8) (h1 : (c 1) ^ 2 = 1 / 4) :
    0 < minoreGram c 3 := by
  rw [minoreGram_three, h0, h1]
  obtain ⟨hlo, hhi⟩ := sqrt_five_bounds
  nlinarith [hlo, hhi]

/-- **La stringa (5,3,3,3) NON è positiva**: il 120-celle non ha
analogo in dimensione 5. Questo è il fatto che chiude `d ≥ 5`. -/
theorem non_positiva_5333 (c : ℕ → ℝ)
    (h0 : (c 0) ^ 2 = (3 + Real.sqrt 5) / 8) (h1 : (c 1) ^ 2 = 1 / 4)
    (h2 : (c 2) ^ 2 = 1 / 4) (h3 : (c 3) ^ 2 = 1 / 4) :
    minoreGram c 5 < 0 := by
  have h5 : minoreGram c 5 =
      minoreGram c 4 - (c 3) ^ 2 * minoreGram c 3 := by
    rw [show (5 : ℕ) = 3 + 2 from rfl, minoreGram_succ_succ]
  rw [h5, minoreGram_four, minoreGram_three, h0, h1, h2, h3]
  obtain ⟨hlo, hhi⟩ := sqrt_five_bounds
  nlinarith [hlo, hhi]

/-- **La stringa (3,4,4) NON è positiva.** -/
theorem non_positiva_344 (c : ℕ → ℝ)
    (h0 : (c 0) ^ 2 = 1 / 4) (h1 : (c 1) ^ 2 = 1 / 2)
    (h2 : (c 2) ^ 2 = 1 / 2) :
    minoreGram c 4 ≤ 0 := by
  rw [minoreGram_four, h0, h1, h2]
  norm_num

/-- **La stringa (5,5) NON è positiva**: due pentagoni non chiudono. -/
theorem non_positiva_55 (c : ℕ → ℝ)
    (h0 : (c 0) ^ 2 = (3 + Real.sqrt 5) / 8)
    (h1 : (c 1) ^ 2 = (3 + Real.sqrt 5) / 8) :
    minoreGram c 3 < 0 := by
  rw [minoreGram_three, h0, h1]
  obtain ⟨hlo, hhi⟩ := sqrt_five_bounds
  nlinarith [hlo, hhi]

end LeanEval.Geometry.PlatonicClassification
