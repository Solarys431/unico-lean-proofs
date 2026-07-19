import Mathlib

/-!
L2' — L'ARGMAX DEL COSENO È ADIACENTE (campagna #50, G1-mio, il cuore).

Su p posizioni equidistanziate del cerchio, se il coseno assume il massimo
sia nella posizione 0 sia nella posizione j ≠ 0, allora j è una delle due
posizioni adiacenti (1 o p−1). Bastano le ipotesi ai bordi: che le due
posizioni adiacenti a 0 non superino il massimo.

La chiave senza aritmetica intera: da cos(φ+a) = cos φ segue
sin(φ + a/2) = 0 (prostaferesi, con sin(a/2) > 0), dunque
ε := cos(φ + a/2) ∈ {±1}; i bordi diventano −ε·sin((a−b)/2) ≥ 0 e
−ε·sin((a+b)/2) ≤ 0, e i segni del seno su (0, π) chiudono:
ε = 1 ⟹ a = b (j = 1), ε = −1 ⟹ a = 2π − b (j = p−1).
-/

open Real

namespace PlatoniciL2

/-- Argmax del coseno su posizioni equidistanziate: solo le adiacenti
pareggiano il massimo. -/
theorem argmax_coseno_adiacente (p : ℕ) (hp : 3 ≤ p) (φ : ℝ) {j : ℕ}
    (hj1 : 1 ≤ j) (hjp : j ≤ p - 1)
    (heq : Real.cos (φ + 2 * π * j / p) = Real.cos φ)
    (h1 : Real.cos (φ + 2 * π / p) ≤ Real.cos φ)
    (hp1 : Real.cos (φ - 2 * π / p) ≤ Real.cos φ) :
    j = 1 ∨ j = p - 1 := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hp0 : (0 : ℝ) < p := by positivity
  set a : ℝ := 2 * π * j / p with hadef
  set b : ℝ := 2 * π / p with hbdef
  have hb0 : 0 < b := by rw [hbdef]; positivity
  have hba : b ≤ a := by
    rw [hadef, hbdef]
    rw [div_le_div_iff_of_pos_right hp0]
    have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    nlinarith
  have hjp' : (j : ℝ) ≤ (p : ℝ) - 1 := by
    have h := hjp
    have : (j : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub (by omega : 1 ≤ p)] at this
    simpa using this
  have ha2π : a ≤ 2 * π - b := by
    rw [hadef, hbdef]
    rw [div_le_iff₀ hp0]
    have hexp : (2 * π - 2 * π / p) * p = 2 * π * p - 2 * π := by
      field_simp
    rw [hexp]
    nlinarith
  have hbπ : b ≤ 2 * π / 3 := by
    rw [hbdef]
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    exact_mod_cast hp
  have hb2 : 0 < Real.sin (b / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  -- ══ dal pareggio: sin(φ + a/2) = 0 ══
  have hsin_a2 : 0 < Real.sin (a / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have hzero : Real.sin (φ + a / 2) = 0 := by
    have hdiff : Real.cos (φ + a) - Real.cos φ = 0 := by rw [heq]; ring
    rw [Real.cos_sub_cos] at hdiff
    have hmid : (φ + a + φ) / 2 = φ + a / 2 := by ring
    have hhalf : (φ + a - φ) / 2 = a / 2 := by ring
    rw [hmid, hhalf] at hdiff
    rcases mul_eq_zero.mp
        (by linarith : Real.sin (φ + a / 2) * Real.sin (a / 2) = 0) with h | h
    · exact h
    · exact absurd h (ne_of_gt hsin_a2)
  -- ε = cos(φ + a/2) ∈ {1, −1}
  have hε : Real.cos (φ + a / 2) = 1 ∨ Real.cos (φ + a / 2) = -1 := by
    have hpyt := Real.sin_sq_add_cos_sq (φ + a / 2)
    rw [hzero] at hpyt
    have h2 : Real.cos (φ + a / 2) * Real.cos (φ + a / 2) = 1 := by nlinarith
    exact mul_self_eq_one_iff.mp h2
  -- ══ i due bordi in forma di segno ══
  have hbordo1 : 0 ≤ Real.sin (φ + b / 2) := by
    have hdiff : Real.cos (φ + b) - Real.cos φ ≤ 0 := by linarith
    rw [Real.cos_sub_cos] at hdiff
    have hmid : (φ + b + φ) / 2 = φ + b / 2 := by ring
    have hhalf : (φ + b - φ) / 2 = b / 2 := by ring
    rw [hmid, hhalf] at hdiff
    nlinarith
  have hbordo2 : Real.sin (φ - b / 2) ≤ 0 := by
    have hdiff : Real.cos (φ - b) - Real.cos φ ≤ 0 := by linarith
    rw [Real.cos_sub_cos] at hdiff
    have hmid : (φ - b + φ) / 2 = φ - b / 2 := by ring
    have hhalf : (φ - b - φ) / 2 = -(b / 2) := by ring
    rw [hmid, hhalf, Real.sin_neg] at hdiff
    nlinarith
  -- ══ sviluppo attorno a φ + a/2 ══
  have hsvil1 : Real.sin (φ + b / 2)
      = -(Real.cos (φ + a / 2) * Real.sin ((a - b) / 2)) := by
    have harg : φ + b / 2 = (φ + a / 2) - (a - b) / 2 := by ring
    rw [harg, Real.sin_sub, hzero]
    ring
  have hsvil2 : Real.sin (φ - b / 2)
      = -(Real.cos (φ + a / 2) * Real.sin ((a + b) / 2)) := by
    have harg : φ - b / 2 = (φ + a / 2) - (a + b) / 2 := by ring
    rw [harg, Real.sin_sub, hzero]
    ring
  -- ══ i due casi su ε ══
  rcases hε with hε1 | hε1
  · -- ε = 1: sin((a−b)/2) ≤ 0 su [0, π) ⟹ a = b ⟹ j = 1
    left
    have hsleq : Real.sin ((a - b) / 2) ≤ 0 := by
      rw [hsvil1, hε1] at hbordo1
      linarith
    have hab : a = b := by
      by_contra hne
      have hlt : b < a := lt_of_le_of_ne hba (Ne.symm hne)
      have hpos : 0 < Real.sin ((a - b) / 2) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · linarith
        · linarith
      linarith
    rw [hadef, hbdef] at hab
    have hp0' : (p : ℝ) ≠ 0 := ne_of_gt hp0
    have h2π : (2 : ℝ) * π ≠ 0 := by positivity
    have h1 : 2 * π * (j : ℝ) * p = 2 * π * p :=
      (div_eq_div_iff hp0' hp0').mp hab
    have hj : (j : ℝ) = 1 := by
      have h2 : 2 * π * (j : ℝ) = 2 * π * 1 := by
        have := mul_right_cancel₀ hp0' h1
        simpa using this
      exact mul_left_cancel₀ h2π h2
    exact_mod_cast hj
  · -- ε = −1: sin((a+b)/2) ≤ 0 su (0, π] ⟹ a = 2π − b ⟹ j = p − 1
    right
    have hsleq : Real.sin ((a + b) / 2) ≤ 0 := by
      rw [hsvil2, hε1] at hbordo2
      linarith
    have hab : a = 2 * π - b := by
      by_contra hne
      have hlt : a < 2 * π - b := lt_of_le_of_ne ha2π hne
      have hpos : 0 < Real.sin ((a + b) / 2) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · linarith
        · linarith
      linarith
    rw [hadef, hbdef] at hab
    have hp0' : (p : ℝ) ≠ 0 := ne_of_gt hp0
    have h2π : (2 : ℝ) * π ≠ 0 := by positivity
    have hr : 2 * π - 2 * π / (p : ℝ) = (2 * π * p - 2 * π) / p := by
      field_simp
    rw [hr] at hab
    have h1 : 2 * π * (j : ℝ) * p = (2 * π * p - 2 * π) * p :=
      (div_eq_div_iff hp0' hp0').mp hab
    have hj : (j : ℝ) = (p : ℝ) - 1 := by
      have h3 := mul_right_cancel₀ hp0' h1
      have h2 : 2 * π * (j : ℝ) = 2 * π * ((p : ℝ) - 1) := by
        rw [h3]; ring
      exact mul_left_cancel₀ h2π h2
    have hjnat : (j : ℝ) = ((p - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ p)]
      simpa using hj
    exact_mod_cast hjnat

end PlatoniciL2
