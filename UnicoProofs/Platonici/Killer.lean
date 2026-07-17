import Mathlib

open Real

/-!
IL KILLER DI k≥2 (campagna #50, M6) — nucleo aritmetico-trigonometrico puro.
Massimo stretto del coseno sull'orbita esattamente in {0,1} ⟹ passo = ±2π/q:
il fan di un politopo convesso non può essere una stella {q/k}.
-/

/-- KC1 — estrazione dell'angolo dall'ordine (via AddCircle). -/
theorem killer_estrazione (q : ℕ) (hq : 3 ≤ q) (δ : Real.Angle)
    (hord : addOrderOf δ = q) :
    ∃ m : ℕ, m < q ∧ m.gcd q = 1 ∧
      δ = (((m : ℝ) / q * (2 * π) : ℝ) : Real.Angle) := by
  haveI : Fact (0 < 2 * π) := ⟨by positivity⟩
  obtain ⟨m, hmq, hgcd, hδ⟩ :=
    (AddCircle.addOrderOf_eq_pos_iff (by omega : 0 < q)).mp hord
  exact ⟨m, hmq, hgcd, by exact_mod_cast hδ.symm⟩

/-- Ponte modulare: se j·m ≡ r (mod q) allora j•δ = (r/q)·2π in `Real.Angle`. -/
theorem killer_passo_modulare (q m j r : ℕ) (hq : 0 < q)
    (hmod : (j * m) % q = r % q) :
    (j • ((((m : ℝ) / q * (2 * π) : ℝ)) : Real.Angle))
      = (((r : ℝ) / q * (2 * π) : ℝ) : Real.Angle) := by
  rw [← Real.Angle.coe_nsmul, Real.Angle.angle_eq_iff_two_pi_dvd_sub]
  obtain ⟨s, hs⟩ : (q : ℤ) ∣ (((j * m : ℕ) : ℤ) - (r : ℕ)) :=
    dvd_sub_comm.mp (Nat.ModEq.dvd hmod)
  refine ⟨s, ?_⟩
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsr : ((j * m : ℕ) : ℝ) - r = q * s := by exact_mod_cast hs
  rw [nsmul_eq_mul]
  have key : (j : ℝ) * ((m / q) * (2 * π)) - (r / q) * (2 * π)
      = (((j * m : ℕ) : ℝ) - r) / q * (2 * π) := by push_cast; ring
  rw [key, hsr, mul_div_cancel_left₀ _ hq0]
  ring

/-- KC2 — IL COLPO. -/
theorem killer_k_pin (q m : ℕ) (hq : 3 ≤ q) (hmq : m < q) (hgcd : m.gcd q = 1)
    (φ : Real.Angle)
    (heq : Real.Angle.cos (φ + (1 : ℕ) • (((m : ℝ) / q * (2 * π) : ℝ) : Real.Angle))
      = Real.Angle.cos φ)
    (hlt : ∀ j : Fin q, (j : ℕ) ≠ 0 → (j : ℕ) ≠ 1 →
      Real.Angle.cos (φ + (j : ℕ) • (((m : ℝ) / q * (2 * π) : ℝ) : Real.Angle))
        < Real.Angle.cos φ) :
    m = 1 ∨ m = q - 1 := by
  haveI : NeZero q := ⟨by omega⟩
  have hqpos : (0 : ℕ) < q := by omega
  have hqR : (0 : ℝ) < q := by positivity
  have hπq : (0 : ℝ) < π / q := by positivity
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h
    · exfalso; rw [h0] at hgcd; simp at hgcd; omega
    · exact h
  by_contra hcon
  push_neg at hcon
  obtain ⟨hne1, hneq1⟩ := hcon
  have hm2 : 2 ≤ m := by omega
  have hmq2 : m + 2 ≤ q := by omega
  rw [one_smul] at heq
  rcases Real.Angle.cos_eq_iff_eq_or_eq_neg.mp heq with hid | hneg
  · -- φ + δ = φ ⟹ δ = 0 ⟹ assurdo
    have hδ0 : (((m : ℝ) / q * (2 * π) : ℝ) : Real.Angle) = ((0 : ℝ) : Real.Angle) := by
      have h : φ + (((m : ℝ) / q * (2 * π) : ℝ) : Real.Angle) - φ = φ - φ := by rw [hid]
      simpa using h
    rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at hδ0
    obtain ⟨t, ht⟩ := hδ0
    have hmt : (m : ℝ) = q * t := by
      have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
      field_simp at ht
      nlinarith [Real.pi_pos, ht]
    have hmtZ : (m : ℤ) = q * t := by exact_mod_cast hmt
    have hqZ : (3 : ℤ) ≤ q := by exact_mod_cast hq
    have hmZ2 : (2 : ℤ) ≤ m := by exact_mod_cast hm2
    have hmqZ : (m : ℤ) < q := by exact_mod_cast hmq
    by_cases ht : t ≤ 0
    · nlinarith
    · have ht1 : (1 : ℤ) ≤ t := by omega
      nlinarith
  · -- φ + δ = −φ ⟹ 2•φ = 2•(−mπ/q) ⟹ i due rami
    have h2φ : (2 : ℤ) • φ = -(((m : ℝ) / q * (2 * π) : ℝ) : Real.Angle) := by
      have h : φ + (((m : ℝ) / q * (2 * π) : ℝ) : Real.Angle) + φ = 0 := by
        rw [hneg]; abel
      have h2 : (2 : ℤ) • φ + (((m : ℝ) / q * (2 * π) : ℝ) : Real.Angle) = 0 := by
        rw [two_zsmul]; rw [← h]; abel
      exact eq_neg_of_add_eq_zero_left h2
    have hψ : -((((m : ℝ) / q * (2 * π) : ℝ)) : Real.Angle)
        = (2 : ℤ) • (((-((m : ℝ) * π / q) : ℝ)) : Real.Angle) := by
      rw [← Real.Angle.coe_neg, two_zsmul, ← Real.Angle.coe_add]
      apply congrArg
      have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
      field_simp
      ring
    have hcop : Nat.Coprime m q := hgcd
    set u : (ZMod q)ˣ := ZMod.unitOfCoprime m hcop with hu
    have hmu : ((m : ℕ) : ZMod q) = (u : ZMod q) := (ZMod.coe_unitOfCoprime m hcop).symm
    rcases Real.Angle.two_zsmul_eq_iff.mp (h2φ.trans hψ) with hφ | hφ
    · -- RAMO 1: φ = −mπ/q. Testimone j₊ = m⁻¹ mod q.
      set jP : ℕ := ((u⁻¹ : (ZMod q)ˣ) : ZMod q).val with hjP
      have hjPlt : jP < q := ZMod.val_lt _
      have hjmZ : ((jP * m : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
        push_cast
        rw [hjP, ZMod.natCast_val, ZMod.cast_id, hmu]
        exact u.inv_mul
      have hmod1 : (jP * m) % q = 1 % q := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hjmZ
      have h1q : 1 % q = 1 := Nat.mod_eq_of_lt (by omega)
      have hjP0 : jP ≠ 0 := by
        intro h0
        rw [h0, zero_mul, Nat.zero_mod, h1q] at hmod1
        omega
      have hjP1 : jP ≠ 1 := by
        intro h1; rw [h1] at hmod1
        rw [one_mul, Nat.mod_eq_of_lt hmq, h1q] at hmod1
        omega
      have hstep := killer_passo_modulare q m jP 1 hqpos hmod1
      have harg : φ + (jP • ((((m : ℝ) / q * (2 * π) : ℝ)) : Real.Angle))
          = (((-(((m : ℝ) - 2) * π / q)) : ℝ) : Real.Angle) := by
        rw [hstep, hφ, ← Real.Angle.coe_add]
        apply congrArg
        have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
        field_simp
        ring
      have hcosL : Real.Angle.cos (φ + (jP • ((((m : ℝ) / q * (2 * π) : ℝ)) : Real.Angle)))
          = Real.cos (((m : ℝ) - 2) * π / q) := by
        rw [harg, Real.Angle.cos_coe, Real.cos_neg]
      have hcosR : Real.Angle.cos φ = Real.cos ((m : ℝ) * π / q) := by
        rw [hφ, Real.Angle.cos_coe, Real.cos_neg]
      have hm2R : (0 : ℝ) ≤ (m : ℝ) - 2 := by
        have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
        linarith
      have hmem1 : ((m : ℝ) - 2) * π / q ∈ Set.Icc 0 π := by
        constructor
        · positivity
        · rw [div_le_iff₀ hqR]
          have hmqR : (m : ℝ) ≤ q := by exact_mod_cast hmq.le
          nlinarith [Real.pi_pos]
      have hmem2 : (m : ℝ) * π / q ∈ Set.Icc 0 π := by
        constructor
        · positivity
        · rw [div_le_iff₀ hqR]
          have hmqR : (m : ℝ) ≤ q := by exact_mod_cast hmq.le
          nlinarith [Real.pi_pos]
      have hstrict : ((m : ℝ) - 2) * π / q < (m : ℝ) * π / q := by
        rw [div_lt_div_iff_of_pos_right hqR]
        nlinarith [Real.pi_pos]
      have hgt := Real.strictAntiOn_cos hmem1 hmem2 hstrict
      have hcontra := hlt ⟨jP, hjPlt⟩ hjP0 hjP1
      rw [show ((⟨jP, hjPlt⟩ : Fin q) : ℕ) = jP from rfl] at hcontra
      rw [hcosL, hcosR] at hcontra
      linarith
    · -- RAMO 2: φ = −mπ/q + π. Testimone j₋ = −m⁻¹ mod q.
      set jM : ℕ := ((-(u⁻¹) : (ZMod q)ˣ) : ZMod q).val with hjM
      have hjMlt : jM < q := ZMod.val_lt _
      have hjmZ2 : ((jM * m : ℕ) : ZMod q) = ((q - 1 : ℕ) : ZMod q) := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
        rw [hjM, ZMod.natCast_val, ZMod.cast_id, hmu]
        rw [ZMod.natCast_self]
        push_cast
        calc ((-(u⁻¹) : (ZMod q)ˣ) : ZMod q) * (u : ZMod q)
            = -(((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (u : ZMod q)) := by
              rw [Units.val_neg]; ring
          _ = -1 := by rw [u.inv_mul]
          _ = 0 - 1 := by ring
      have hmod2 : (jM * m) % q = (q - 1) % q := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hjmZ2
      have hq1m : (q - 1) % q = q - 1 := Nat.mod_eq_of_lt (by omega)
      have hjM0 : jM ≠ 0 := by
        intro h0
        rw [h0, zero_mul, Nat.zero_mod, hq1m] at hmod2
        omega
      have hjM1 : jM ≠ 1 := by
        intro h1; rw [h1] at hmod2
        rw [one_mul, Nat.mod_eq_of_lt hmq, hq1m] at hmod2
        omega
      have hstep2 := killer_passo_modulare q m jM (q - 1) hqpos hmod2
      have harg2 : φ + (jM • ((((m : ℝ) / q * (2 * π) : ℝ)) : Real.Angle))
          = (((π - ((m : ℝ) + 2) * π / q) : ℝ) : Real.Angle) := by
        rw [hstep2, hφ, ← Real.Angle.coe_add, ← Real.Angle.coe_add,
          Real.Angle.angle_eq_iff_two_pi_dvd_sub]
        refine ⟨1, ?_⟩
        have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
        have hq1R : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ q)]; ring
        rw [hq1R]
        field_simp
        ring
      have hcosL : Real.Angle.cos (φ + (jM • ((((m : ℝ) / q * (2 * π) : ℝ)) : Real.Angle)))
          = -Real.cos (((m : ℝ) + 2) * π / q) := by
        rw [harg2, Real.Angle.cos_coe, Real.cos_pi_sub]
      have hcosR : Real.Angle.cos φ = -Real.cos ((m : ℝ) * π / q) := by
        rw [hφ, ← Real.Angle.coe_add, Real.Angle.cos_coe,
          show (-((m : ℝ) * π / q) + π) = π - (m : ℝ) * π / q by ring, Real.cos_pi_sub]
      have hmem1 : (m : ℝ) * π / q ∈ Set.Icc 0 π := by
        constructor
        · positivity
        · rw [div_le_iff₀ hqR]
          have hmqR : (m : ℝ) ≤ q := by exact_mod_cast hmq.le
          nlinarith [Real.pi_pos]
      have hmem2 : ((m : ℝ) + 2) * π / q ∈ Set.Icc 0 π := by
        constructor
        · positivity
        · rw [div_le_iff₀ hqR]
          have hmqR : (m : ℝ) + 2 ≤ q := by exact_mod_cast hmq2
          nlinarith [Real.pi_pos]
      have hstrict : (m : ℝ) * π / q < ((m : ℝ) + 2) * π / q := by
        rw [div_lt_div_iff_of_pos_right hqR]
        nlinarith [Real.pi_pos]
      have hgt := Real.strictAntiOn_cos hmem1 hmem2 hstrict
      have hcontra := hlt ⟨jM, hjMlt⟩ hjM0 hjM1
      rw [show ((⟨jM, hjMlt⟩ : Fin q) : ℕ) = jM from rfl] at hcontra
      rw [hcosL, hcosR] at hcontra
      linarith

/-!
R1d — IL RACCORDO DEL KILLER: dal funzionale espositore della faccetta
all'ipotesi cos-max, e da lì al passo ±2π/q del fan.
-/

open scoped RealInnerProductSpace

section R1d

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- Le iterate di una rotazione conservano la norma. -/
theorem norm_rotation_iterate (o : Orientation ℝ E (Fin 2)) (θ : Real.Angle)
    (x : E) (j : ℕ) : ‖(⇑(o.rotation θ))^[j] x‖ = ‖x‖ := by
  induction j with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', LinearIsometryEquiv.norm_map, ih]

/-- L'oangle rispetto a un riferimento cresce di θ a ogni passo dell'orbita. -/
theorem oangle_rotation_iterate (o : Orientation ℝ E (Fin 2)) (θ : Real.Angle)
    (n e₀ : E) (hn : n ≠ 0) (he₀ : e₀ ≠ 0) (j : ℕ) :
    o.oangle n ((⇑(o.rotation θ))^[j] e₀) = o.oangle n e₀ + (j : ℕ) • θ := by
  induction j with
  | zero => simp
  | succ k ih =>
      have hek : (⇑(o.rotation θ))^[k] e₀ ≠ 0 := by
        intro h0
        apply he₀
        have := norm_rotation_iterate o θ e₀ k
        rw [h0, norm_zero] at this
        exact norm_eq_zero.mp this.symm
      rw [Function.iterate_succ_apply', o.oangle_rotation_right hn hek θ, ih,
        succ_nsmul]
      abel

/-- Il prodotto interno lungo l'orbita è un coseno. -/
theorem inner_orbita (o : Orientation ℝ E (Fin 2)) (θ : Real.Angle)
    (n e₀ : E) (hn : n ≠ 0) (he₀ : ‖e₀‖ = 1) (j : ℕ) :
    ⟪n, (⇑(o.rotation θ))^[j] e₀⟫
      = ‖n‖ * Real.Angle.cos (o.oangle n e₀ + (j : ℕ) • θ) := by
  have he₀' : e₀ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at he₀; norm_num at he₀
  rw [o.inner_eq_norm_mul_norm_mul_cos_oangle, norm_rotation_iterate, he₀, mul_one,
    oangle_rotation_iterate o θ n e₀ hn he₀' j]

/-- R1d — IL RACCORDO: massimo del prodotto interno sull'orbita esattamente in
{0,1} + ordine q ⟹ il passo della rotazione è ±2π/q. -/
theorem passo_del_fan (o : Orientation ℝ E (Fin 2)) (θ : Real.Angle)
    (q : ℕ) (hq : 3 ≤ q) (hord : addOrderOf θ = q)
    (n e₀ : E) (hn : n ≠ 0) (he₀ : ‖e₀‖ = 1)
    (heq : ⟪n, (⇑(o.rotation θ))^[1] e₀⟫ = ⟪n, e₀⟫)
    (hlt : ∀ j : Fin q, (j : ℕ) ≠ 0 → (j : ℕ) ≠ 1 →
      ⟪n, (⇑(o.rotation θ))^[(j : ℕ)] e₀⟫ < ⟪n, e₀⟫) :
    θ = ((2 * π / q : ℝ) : Real.Angle) ∨ θ = ((-(2 * π / q) : ℝ) : Real.Angle) := by
  obtain ⟨m, hmq, hgcd, hδ⟩ := killer_estrazione q hq θ hord
  set φ := o.oangle n e₀ with hφ
  have hnpos : (0 : ℝ) < ‖n‖ := norm_pos_iff.mpr hn
  have hbase : ⟪n, e₀⟫ = ‖n‖ * Real.Angle.cos φ := by
    have h0 := inner_orbita o θ n e₀ hn he₀ 0
    simpa using h0
  have hcoseq : Real.Angle.cos (φ + (1 : ℕ) • (((m : ℝ) / q * (2 * π) : ℝ) : Real.Angle))
      = Real.Angle.cos φ := by
    have h1 := inner_orbita o θ n e₀ hn he₀ 1
    rw [h1, hbase] at heq
    have := mul_left_cancel₀ (ne_of_gt hnpos) heq
    rw [← hδ]
    exact this
  have hcoslt : ∀ j : Fin q, (j : ℕ) ≠ 0 → (j : ℕ) ≠ 1 →
      Real.Angle.cos (φ + (j : ℕ) • (((m : ℝ) / q * (2 * π) : ℝ) : Real.Angle))
        < Real.Angle.cos φ := by
    intro j hj0 hj1
    have hj := hlt j hj0 hj1
    rw [inner_orbita o θ n e₀ hn he₀ (j : ℕ), hbase] at hj
    have := lt_of_mul_lt_mul_left hj hnpos.le
    rw [← hδ]
    exact this
  rcases killer_k_pin q m hq hmq hgcd φ hcoseq hcoslt with h1 | hq1
  · left
    rw [hδ, h1]
    apply congrArg
    push_cast
    ring
  · right
    rw [hδ, hq1, Real.Angle.angle_eq_iff_two_pi_dvd_sub]
    refine ⟨1, ?_⟩
    have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hq1R : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ q)]; ring
    rw [hq1R]
    field_simp
    ring

end R1d
