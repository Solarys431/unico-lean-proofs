import Mathlib
import UnicoProofs.Platonici.AngoloRiflessioni

open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ComplexConjugate

variable {n : ℕ}

/-- Conjugating a linear isometry by a linear isometric equivalence preserves its order. -/
theorem massimo_consecutivo_order_conj
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (e : W ≃ₗᵢ[ℝ] ℂ) (R : W ≃ₗᵢ[ℝ] W) :
    orderOf (e.symm.trans (R.trans e)) = orderOf R := by
  let S : ℂ ≃ₗᵢ[ℝ] ℂ := e.symm.trans (R.trans e)
  have hpow : ∀ q : ℕ, ∀ x : W, (S ^ q) (e x) = e ((R ^ q) x) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        intro x
        rw [pow_succ, pow_succ]
        change (S ^ q) (S (e x)) = e ((R ^ q) (R x))
        rw [show S (e x) = e (R x) by simp [S], ih]
  rw [orderOf_eq_orderOf_iff]
  intro q
  constructor
  · intro h
    apply LinearIsometryEquiv.ext
    intro x
    have hx := LinearIsometryEquiv.congr_fun h (e x)
    rw [hpow] at hx
    simpa using congrArg e.symm hx
  · intro h
    apply LinearIsometryEquiv.ext
    intro z
    have hp := hpow q (e.symm z)
    rw [h] at hp
    simpa using hp

/-- Powers commute with the conjugacy used in `massimo_consecutivo_order_conj`. -/
theorem massimo_consecutivo_conj_pow_apply
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (e : W ≃ₗᵢ[ℝ] ℂ) (R : W ≃ₗᵢ[ℝ] W) (q : ℕ) (x : W) :
    ((e.symm.trans (R.trans e)) ^ q) (e x) = e ((R ^ q) x) := by
  induction q generalizing x with
  | zero => simp
  | succ q ih =>
      rw [pow_succ, pow_succ]
      change ((e.symm.trans (R.trans e)) ^ q)
          ((e.symm.trans (R.trans e)) (e x)) = e ((R ^ q) (R x))
      rw [show (e.symm.trans (R.trans e)) (e x) = e (R x) by simp, ih]

/-- A conjugation followed by a rotation is an involution. -/
theorem massimo_consecutivo_conj_rotation_sq (a : Circle) :
    (Complex.conjLIE.trans (rotation a)) ^ 2 = 1 := by
  apply LinearIsometryEquiv.ext
  intro z
  have hz : (a : ℂ) * conj ((a : ℂ) * conj z) = z := by
    have ha : (a : ℂ).re * (a : ℂ).re + (a : ℂ).im * (a : ℂ).im = 1 := by
      simpa [Complex.normSq_apply] using Circle.normSq_coe a
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im]
      linear_combination z.re * ha
    · simp [Complex.mul_re, Complex.mul_im]
      linear_combination z.im * ha
  simpa [pow_two, LinearIsometryEquiv.coe_mul, Function.comp_apply,
    LinearIsometryEquiv.trans_apply, rotation_apply, Complex.conjLIE_apply] using hz

/-- Algebraic form of the phase constraint `Re (a*b) = Re b` on the unit circle. -/
theorem massimo_consecutivo_phase (a : Circle) (b : ℂ)
    (ha1 : (a : ℂ) ≠ 1) (ham1 : (a : ℂ) ≠ -1)
    (hb : b ≠ 0) (heq : ((a : ℂ) * b).re = b.re) :
    ∃ c : ℝ, c ≠ 0 ∧ b = (c : ℂ) * (1 + conj (a : ℂ)) := by
  have ha : (a : ℂ).re * (a : ℂ).re + (a : ℂ).im * (a : ℂ).im = 1 := by
    simpa [Complex.normSq_apply] using Circle.normSq_coe a
  have hai : (a : ℂ).im ≠ 0 := by
    intro hz
    have hre_sq : (a : ℂ).re ^ 2 = 1 := by
      simpa [hz, pow_two] using ha
    rcases (sq_eq_one_iff).mp hre_sq with hre | hre
    · apply ha1
      apply Complex.ext <;> simp [hre, hz]
    · apply ham1
      apply Complex.ext <;> simp [hre, hz]
  have heq0 :
      (a : ℂ).re * b.re - (a : ℂ).im * b.im - b.re = 0 := by
    simpa [Complex.mul_re] using sub_eq_zero.mpr heq
  have hrel :
      -b.im * (1 + (a : ℂ).re) = b.re * (a : ℂ).im := by
    have hp : (a : ℂ).im *
        (-b.im * (1 + (a : ℂ).re) - b.re * (a : ℂ).im) = 0 := by
      linear_combination (1 + (a : ℂ).re) * heq0 - b.re * ha
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hai)
  let c : ℝ := -b.im / (a : ℂ).im
  have hc_re : c * (1 + (a : ℂ).re) = b.re := by
    dsimp only [c]
    field_simp [hai]
    linarith
  have hc_im : c * (-(a : ℂ).im) = b.im := by
    dsimp only [c]
    field_simp [hai]
  have hrepr : b = (c : ℂ) * (1 + conj (a : ℂ)) := by
    apply Complex.ext
    · simpa [Complex.mul_re] using hc_re.symm
    · simpa [Complex.mul_im] using hc_im.symm
  refine ⟨c, ?_, hrepr⟩
  intro hc
  apply hb
  rw [hrepr, hc]
  simp

/-- Extract the coprime exponent of a circle element of exact order `m`. -/
theorem massimo_consecutivo_primitive_index {m : ℕ} (hm : 3 ≤ m)
    (a : Circle) (hord : orderOf a = m) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ m - 1 ∧ Nat.Coprime k m ∧
      (a : ℂ) = (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (m : ℂ))) ^ k := by
  have hm0 : m ≠ 0 := by omega
  have hco : orderOf (a : ℂ) = m :=
    (orderOf_injective Circle.coeHom Circle.coe_injective a).trans hord
  have hp : IsPrimitiveRoot (a : ℂ) m :=
    IsPrimitiveRoot.iff_orderOf.mpr hco
  obtain ⟨k, hklt, hcop, hka⟩ :=
    (Complex.isPrimitiveRoot_iff (a : ℂ) m hm0).mp hp
  have hkpos : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    subst k
    simp at hcop
    omega
  refine ⟨k, hkpos, by omega, hcop, ?_⟩
  rw [← hka, ← Complex.exp_nat_mul]
  congr 1
  field_simp

/-- Multiplication by a coprime residue sends every non-endpoint residue to a time
between `2` and `m-1`. -/
theorem massimo_consecutivo_zmod {m k j : ℕ} (hm : 3 ≤ m)
    (hklt : k < m) (hjlt : j < m) (hcop : Nat.Coprime k m)
    (hj0 : j ≠ 0) (hjk : j ≠ k) (ζ b : ℂ) (hζm : ζ ^ m = 1)
    (hlt : ∀ t : ℕ, 2 ≤ t → t ≤ m - 1 →
      (((ζ ^ k) ^ t) * b).re < b.re) :
    (ζ ^ j * b).re < b.re := by
  letI : NeZero m := ⟨by omega⟩
  let uk : (ZMod m)ˣ := ZMod.unitOfCoprime k hcop
  let x : ZMod m := (uk⁻¹ : (ZMod m)ˣ) * (j : ZMod m)
  let t : ℕ := x.val
  have heq : (t : ZMod m) * (k : ZMod m) = (j : ZMod m) := by
    rw [show (t : ZMod m) = x by exact ZMod.natCast_zmod_val x]
    rw [show (k : ZMod m) = (uk : ZMod m) by simp [uk]]
    change ((↑(uk⁻¹) : ZMod m) * (j : ZMod m)) * (uk : ZMod m) = j
    calc
      _ = ((↑(uk⁻¹) : ZMod m) * (uk : ZMod m)) * j := by ring
      _ = j := by simp
  have htlt : t < m := x.val_lt
  have ht0 : t ≠ 0 := by
    intro ht
    have hjcast : (j : ZMod m) = 0 := by simpa [ht] using heq.symm
    have hv := congrArg ZMod.val hjcast
    simp [ZMod.val_natCast_of_lt hjlt] at hv
    exact hj0 hv
  have ht1 : t ≠ 1 := by
    intro ht
    have hjcast : (j : ZMod m) = (k : ZMod m) := by simpa [ht] using heq.symm
    have hv := congrArg ZMod.val hjcast
    simp [ZMod.val_natCast_of_lt hjlt, ZMod.val_natCast_of_lt hklt] at hv
    exact hjk hv
  have hmod : k * t ≡ j [MOD m] := by
    change k * t % m = j % m
    have hv := congrArg ZMod.val heq
    simpa [ZMod.val_mul, ZMod.val_natCast_of_lt hklt,
      ZMod.val_natCast_of_lt hjlt, ZMod.val_natCast,
      Nat.mod_eq_of_lt hjlt, Nat.mul_comm] using hv
  have hp : (ζ ^ k) ^ t = ζ ^ j := by
    rw [← pow_mul]
    exact pow_eq_pow_of_modEq hmod hζm
  rw [← hp]
  exact hlt t (by omega) (by omega)

/-- The real part of the orbit after solving the phase constraint. -/
theorem massimo_consecutivo_value {m k : ℕ} (hm : 3 ≤ m)
    (c : ℝ) (b ζ : ℂ)
    (hζ : ζ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (m : ℂ)))
    (hb : b = (c : ℂ) * (1 + conj (ζ ^ k))) (j : ℕ) :
    (ζ ^ j * b).re =
      2 * (c * Real.cos (Real.pi * (k : ℝ) / (m : ℝ))) *
        Real.cos (Real.pi * (2 * (j : ℝ) - (k : ℝ)) / (m : ℝ)) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hpow (q : ℕ) :
      ζ ^ q = Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * ((q : ℂ) / (m : ℂ))) := by
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  have hre (q : ℕ) :
      (ζ ^ q).re = Real.cos (2 * Real.pi * (q : ℝ) / (m : ℝ)) := by
    rw [hpow, Complex.exp_re]
    simp
    congr 1
    field_simp
  have him (q : ℕ) :
      (ζ ^ q).im = Real.sin (2 * Real.pi * (q : ℝ) / (m : ℝ)) := by
    rw [hpow, Complex.exp_im]
    simp
    congr 1
    field_simp
  have hcross :
      (ζ ^ j * conj (ζ ^ k)).re =
        Real.cos (2 * Real.pi * (j : ℝ) / (m : ℝ) -
          2 * Real.pi * (k : ℝ) / (m : ℝ)) := by
    rw [Complex.mul_re]
    simp only [Complex.conj_re, Complex.conj_im, hre, him]
    rw [Real.cos_sub]
    ring
  rw [hb]
  have hval :
      (ζ ^ j * ((c : ℂ) * (1 + conj (ζ ^ k)))).re =
        c * ((ζ ^ j).re + (ζ ^ j * conj (ζ ^ k)).re) := by
    simp [Complex.mul_re, Complex.add_re]
    ring
  rw [hval, hre, hcross]
  have hx : 2 * Real.pi * (j : ℝ) / (m : ℝ) =
      Real.pi * (2 * (j : ℝ) - (k : ℝ)) / (m : ℝ) +
        Real.pi * (k : ℝ) / (m : ℝ) := by field_simp; ring
  have hsub : 2 * Real.pi * (j : ℝ) / (m : ℝ) -
      2 * Real.pi * (k : ℝ) / (m : ℝ) =
      Real.pi * (2 * (j : ℝ) - (k : ℝ)) / (m : ℝ) -
        Real.pi * (k : ℝ) / (m : ℝ) := by field_simp; ring
  rw [hsub, hx, Real.cos_add, Real.cos_sub]
  ring

/-- The three explicit choices of residue force the primitive exponent to be an endpoint. -/
theorem massimo_consecutivo_index_endpoints {m k : ℕ} (hm : 3 ≤ m)
    (hkpos : 1 ≤ k) (hklt : k < m) (d : ℝ) (hd : d ≠ 0)
    (hmax : ∀ j : ℕ, j < m → j ≠ 0 → j ≠ k →
      2 * d * Real.cos (Real.pi * (2 * (j : ℝ) - (k : ℝ)) / (m : ℝ)) <
        2 * d * Real.cos (Real.pi * (k : ℝ) / (m : ℝ))) :
    k = 1 ∨ k = m - 1 := by
  by_contra hends
  push Not at hends
  have hklo : 2 ≤ k := by omega
  have hkhi : k ≤ m - 2 := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  let y : ℝ := Real.pi * (k : ℝ) / (m : ℝ)
  have hy0 : 0 < y := by dsimp only [y]; positivity
  have hypi : y < Real.pi := by
    dsimp only [y]
    rw [div_lt_iff₀ hmR]
    have hkR : (k : ℝ) < m := by exact_mod_cast hklt
    nlinarith [Real.pi_pos]
  rcases lt_or_gt_of_ne hd with hdneg | hdpos
  · by_cases hpar : k % 2 = m % 2
    · let j : ℕ := (k + m) / 2
      have hjtwice : 2 * j = k + m := by dsimp only [j]; omega
      have hjlt : j < m := by omega
      have hj0 : j ≠ 0 := by omega
      have hjk : j ≠ k := by omega
      have hbad := hmax j hjlt hj0 hjk
      have harg :
          Real.pi * (2 * (j : ℝ) - (k : ℝ)) / (m : ℝ) = Real.pi := by
        have hjR : 2 * (j : ℝ) = (k : ℝ) + (m : ℝ) := by exact_mod_cast hjtwice
        field_simp
        nlinarith
      rw [harg, Real.cos_pi] at hbad
      have hcos : -1 < Real.cos y := by
        have hanti := Real.strictAntiOn_cos
          (show y ∈ Set.Icc (0 : ℝ) Real.pi from ⟨hy0.le, hypi.le⟩)
          (show Real.pi ∈ Set.Icc (0 : ℝ) Real.pi from ⟨Real.pi_pos.le, le_rfl⟩)
          hypi
        simpa using hanti
      dsimp only [y] at hcos
      nlinarith
    · have hpar' : (k + m - 1) % 2 = 0 := by omega
      let j : ℕ := (k + m - 1) / 2
      have hjtwice : 2 * j = k + m - 1 := by dsimp only [j]; omega
      have hjlt : j < m := by omega
      have hj0 : j ≠ 0 := by omega
      have hjk : j ≠ k := by omega
      have hbad := hmax j hjlt hj0 hjk
      let x : ℝ := Real.pi / (m : ℝ)
      let z : ℝ := 2 * Real.pi / (m : ℝ)
      have hx0 : 0 ≤ x := by dsimp only [x]; positivity
      have hxz : x < z := by
        dsimp only [x, z]
        rw [div_lt_div_iff_of_pos_right hmR]
        nlinarith [Real.pi_pos]
      have hzpi : z ≤ Real.pi := by
        dsimp only [z]
        rw [div_le_iff₀ hmR]
        have hmR3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
        nlinarith [Real.pi_pos]
      have hy_le : y ≤ Real.pi - z := by
        dsimp only [y, z]
        rw [div_le_iff₀ hmR]
        have hkadd : k + 2 ≤ m := by omega
        have hkR : (k : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast hkadd
        have hrearr :
            (Real.pi - 2 * Real.pi / (m : ℝ)) * (m : ℝ) =
              Real.pi * ((m : ℝ) - 2) := by field_simp
        rw [hrearr]
        nlinarith [Real.pi_pos]
      have hcos_xz : Real.cos z < Real.cos x :=
        Real.strictAntiOn_cos
          ⟨hx0, hxz.le.trans hzpi⟩ ⟨hx0.trans hxz.le, hzpi⟩ hxz
      have hcos_y : -Real.cos z ≤ Real.cos y := by
        have hanti := Real.strictAntiOn_cos.antitoneOn
          (show y ∈ Set.Icc (0 : ℝ) Real.pi from ⟨hy0.le, hypi.le⟩)
          (show Real.pi - z ∈ Set.Icc (0 : ℝ) Real.pi by
            constructor <;> linarith [Real.pi_pos]) hy_le
        rw [Real.cos_pi_sub] at hanti
        exact hanti
      have hsum : 0 < Real.cos x + Real.cos y := by linarith
      have harg :
          Real.pi * (2 * (j : ℝ) - (k : ℝ)) / (m : ℝ) = Real.pi - x := by
        have hjplus : 2 * j + 1 = k + m := by omega
        have hjR : 2 * (j : ℝ) + 1 = (k : ℝ) + (m : ℝ) := by
          exact_mod_cast hjplus
        dsimp only [x]
        field_simp
        nlinarith
      rw [harg, Real.cos_pi_sub] at hbad
      dsimp only [y] at hsum
      nlinarith
  · let x : ℝ := Real.pi * ((k : ℝ) - 2) / (m : ℝ)
    have hx0 : 0 ≤ x := by
      dsimp only [x]
      have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hklo
      exact div_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hkR)) hmR.le
    have hxy : x < y := by
      dsimp only [x, y]
      rw [div_lt_div_iff_of_pos_right hmR]
      nlinarith [Real.pi_pos]
    have hcos : Real.cos y < Real.cos x :=
      Real.strictAntiOn_cos
        ⟨hx0, hxy.le.trans hypi.le⟩ ⟨hy0.le, hypi.le⟩ hxy
    have hbad := hmax 1 (by omega) (by omega) (by omega)
    have harg :
        Real.pi * (2 * ((1 : ℕ) : ℝ) - (k : ℝ)) / (m : ℝ) = -x := by
      dsimp only [x]
      ring
    rw [harg, Real.cos_neg] at hbad
    dsimp only [y] at hcos
    nlinarith

/-- A primitive root whose real projection has two consecutive strict maxima has exponent `±1`. -/
theorem massimo_consecutivo_complex (a : Circle) (m : ℕ) (hm : 3 ≤ m)
    (hord : orderOf a = m) (z : ℂ) (hz : z ≠ 0) (w : ℂ)
    (heq : (((a : ℂ) * z) * conj w).re = (z * conj w).re)
    (hlt : ∀ t : ℕ, 2 ≤ t → t ≤ m - 1 →
      ((((a : ℂ) ^ t * z) * conj w).re < (z * conj w).re)) :
    (a : ℂ).re = Real.cos (2 * Real.pi / (m : ℝ)) := by
  let b : ℂ := z * conj w
  have hb : b ≠ 0 := by
    intro hb0
    have hbad := hlt 2 (by omega) (by omega)
    change z * conj w = 0 at hb0
    rw [mul_assoc] at hbad
    rw [hb0] at hbad
    simp at hbad
  have horda1 : (a : ℂ) ≠ 1 := by
    intro ha
    have haC : a = 1 := Circle.coe_injective ha
    subst a
    simp at hord
    omega
  have hordam1 : (a : ℂ) ≠ -1 := by
    intro ha
    have hp : a ^ 2 = 1 := by
      apply Circle.coe_injective
      norm_num [map_pow, ha]
    have hd : m ∣ 2 := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hp
    exact (Nat.not_dvd_of_pos_of_lt (by omega : 0 < (2 : ℕ)) (by omega : 2 < m)) hd
  have heqb : ((a : ℂ) * b).re = b.re := by
    simpa [b, mul_assoc] using heq
  obtain ⟨c, hc0, hbc⟩ :=
    massimo_consecutivo_phase a b horda1 hordam1 hb heqb
  obtain ⟨k, hkpos, hkle, hcop, hak⟩ :=
    massimo_consecutivo_primitive_index hm a hord
  let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (m : ℂ))
  have hklt : k < m := by omega
  have hak' : (a : ℂ) = ζ ^ k := by simpa [ζ] using hak
  have hbc' : b = (c : ℂ) * (1 + conj (ζ ^ k)) := by simpa [hak'] using hbc
  have hζm : ζ ^ m = 1 := by
    dsimp only [ζ]
    exact (Complex.isPrimitiveRoot_exp m (by omega)).pow_eq_one
  have hlt' : ∀ t : ℕ, 2 ≤ t → t ≤ m - 1 →
      (((ζ ^ k) ^ t) * b).re < b.re := by
    intro t htlo hthi
    have ht := hlt t htlo hthi
    simpa [b, hak', mul_assoc] using ht
  let d : ℝ := c * Real.cos (Real.pi * (k : ℝ) / (m : ℝ))
  have hd : d ≠ 0 := by
    intro hd0
    have hcos : Real.cos (Real.pi * (k : ℝ) / (m : ℝ)) = 0 := by
      dsimp only [d] at hd0
      exact (mul_eq_zero.mp hd0).resolve_left hc0
    have hre : (a : ℂ).re = -1 := by
      rw [hak']
      have hzre : (ζ ^ k).re =
          Real.cos (2 * Real.pi * (k : ℝ) / (m : ℝ)) := by
        have hpow : ζ ^ k = Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) / (m : ℂ))) := by
          dsimp only [ζ]
          rw [← Complex.exp_nat_mul]
          congr 1
          field_simp
        rw [hpow, Complex.exp_re]
        simp
        congr 1
        field_simp
      rw [hzre]
      rw [show 2 * Real.pi * (k : ℝ) / (m : ℝ) =
          2 * (Real.pi * (k : ℝ) / (m : ℝ)) by ring,
        Real.cos_two_mul, hcos]
      norm_num
    have him : (a : ℂ).im = 0 := by
      have hnorm := Circle.normSq_coe a
      simp [Complex.normSq_apply, hre] at hnorm
      nlinarith [sq_nonneg (a : ℂ).im]
    apply hordam1
    apply Complex.ext <;> simp [hre, him]
  have hbase : b.re =
      2 * d * Real.cos (Real.pi * (k : ℝ) / (m : ℝ)) := by
    have hv := massimo_consecutivo_value hm c b ζ (by rfl) hbc' 0
    simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_sub] at hv
    have hneg : Real.pi * (-(k : ℝ)) / (m : ℝ) =
        -(Real.pi * (k : ℝ) / (m : ℝ)) := by ring
    rw [hneg, Real.cos_neg] at hv
    simpa [d] using hv
  have hmax : ∀ j : ℕ, j < m → j ≠ 0 → j ≠ k →
      2 * d * Real.cos (Real.pi * (2 * (j : ℝ) - (k : ℝ)) / (m : ℝ)) <
        2 * d * Real.cos (Real.pi * (k : ℝ) / (m : ℝ)) := by
    intro j hjlt hj0 hjk
    have hj := massimo_consecutivo_zmod hm hklt hjlt hcop hj0 hjk ζ b hζm hlt'
    rw [massimo_consecutivo_value hm c b ζ (by rfl) hbc' j, hbase] at hj
    simpa [d] using hj
  have hkends := massimo_consecutivo_index_endpoints hm hkpos hklt d hd hmax
  have hre_pow (q : ℕ) :
      (ζ ^ q).re = Real.cos (2 * Real.pi * (q : ℝ) / (m : ℝ)) := by
    have hpow : ζ ^ q = Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * ((q : ℂ) / (m : ℂ))) := by
      dsimp only [ζ]
      rw [← Complex.exp_nat_mul]
      congr 1
      field_simp
    rw [hpow, Complex.exp_re]
    simp
    congr 1
    field_simp
  rw [hak', hre_pow]
  rcases hkends with hk | hk
  · subst k
    congr 1
    ring
  · rw [hk]
    have hm1 : 1 ≤ m := by omega
    have hang : 2 * Real.pi * ((m - 1 : ℕ) : ℝ) / (m : ℝ) =
        2 * Real.pi - 2 * Real.pi / (m : ℝ) := by
      rw [Nat.cast_sub hm1]
      field_simp
      ring
    rw [hang]
    simpa using Real.cos_nat_mul_two_pi_sub (2 * Real.pi / (m : ℝ)) 1

/-- If two consecutive orbit points are the unique maxima of a linear functional,
the step is the elementary angle of the regular `m`-gon. -/
theorem massimo_consecutivo {V : Submodule ℝ (E n)} (hV : Module.finrank ℝ V = 2)
    (R : V ≃ₗᵢ[ℝ] V) (m : ℕ) (hm : 3 ≤ m) (hord : orderOf R = m)
    (v : V) (hv : v ≠ 0) (u : V)
    (heq : ⟪(u : E n), ((R v : V) : E n)⟫ = ⟪(u : E n), (v : E n)⟫)
    (hlt : ∀ t : ℕ, 2 ≤ t → t ≤ m - 1 →
      ⟪(u : E n), (((R ^ t) v : V) : E n)⟫ < ⟪(u : E n), (v : E n)⟫) :
    ⟪(v : E n), ((R v : V) : E n)⟫ =
      ‖(v : E n)‖ ^ 2 * Real.cos (2 * Real.pi / m) := by
  let B : OrthonormalBasis (Fin 2) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (finCongr hV)
  let e : V ≃ₗᵢ[ℝ] ℂ := (Complex.isometryOfOrthonormal B).symm
  let S : ℂ ≃ₗᵢ[ℝ] ℂ := e.symm.trans (R.trans e)
  have horderS : orderOf S = m :=
    (massimo_consecutivo_order_conj e R).trans hord
  obtain ⟨a, hrot | href⟩ := linear_isometry_complex S
  · have horda : orderOf a = m := by
      have hr : orderOf (rotation a) = m := by simpa [hrot] using horderS
      exact (orderOf_injective rotation rotation_injective a).symm.trans hr
    have hrot0 : e.symm.trans (R.trans e) = rotation a := by
      simpa [S] using hrot
    let z : ℂ := e v
    let w : ℂ := e u
    have hz : z ≠ 0 := by
      intro hz0
      apply hv
      exact e.injective (by simpa [z] using hz0)
    have heqC : (((a : ℂ) * z) * conj w).re = (z * conj w).re := by
      have he : (⟪u, R v⟫ : ℝ) = ⟪u, v⟫ := heq
      rw [inner_map_complex e u (R v), inner_map_complex e u v] at he
      have hp := massimo_consecutivo_conj_pow_apply e R 1 v
      simp only [pow_one] at hp
      rw [hrot0] at hp
      simp only [rotation_apply] at hp
      simpa [z, w, hp] using he
    have hltC : ∀ t : ℕ, 2 ≤ t → t ≤ m - 1 →
        ((((a : ℂ) ^ t * z) * conj w).re < (z * conj w).re) := by
      intro t htlo hthi
      have ht : (⟪u, (R ^ t) v⟫ : ℝ) < ⟪u, v⟫ := hlt t htlo hthi
      rw [inner_map_complex e u ((R ^ t) v), inner_map_complex e u v] at ht
      have hp := massimo_consecutivo_conj_pow_apply e R t v
      rw [hrot0] at hp
      have hrotation : (rotation a) ^ t = rotation (a ^ t) := by
        exact (map_pow rotation a t).symm
      rw [hrotation] at hp
      simp only [rotation_apply] at hp
      rw [← hp] at ht
      simpa [z, w] using ht
    have hare := massimo_consecutivo_complex a m hm horda z hz w heqC hltC
    change (⟪v, R v⟫ : ℝ) = ‖v‖ ^ 2 * Real.cos (2 * Real.pi / m)
    rw [inner_map_complex e v (R v)]
    have hp := massimo_consecutivo_conj_pow_apply e R 1 v
    simp only [pow_one] at hp
    rw [hrot0] at hp
    simp only [rotation_apply] at hp
    rw [← hp]
    change (((a : ℂ) * z) * conj z).re =
      ‖v‖ ^ 2 * Real.cos (2 * Real.pi / (m : ℝ))
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hnorm : ‖z‖ = ‖(v : E n)‖ := by
      simpa [z] using e.norm_map v
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hare, hnorm]
    have hnorm_coe : ‖v‖ = ‖(v : E n)‖ := rfl
    rw [hnorm_coe]
    ring
  · have hsquare : S ^ 2 = 1 := by
      rw [href]
      exact massimo_consecutivo_conj_rotation_sq a
    have hd : m ∣ 2 := by
      rw [← horderS]
      exact orderOf_dvd_of_pow_eq_one hsquare
    exfalso
    exact (Nat.not_dvd_of_pos_of_lt (by omega : 0 < (2 : ℕ)) (by omega : 2 < m)) hd

/-- A vector orthogonal to the chord of two equal-length rays in a plane lies on their
angle bisector; the displayed identity is the resulting half-angle formula. -/
theorem bisezione_ortogonale {V : Submodule ℝ (E n)} (hV : Module.finrank ℝ V = 2)
    (m : ℕ) (hm : 3 ≤ m) (v w rv : V)
    (hvne : v ≠ 0) (hwne : w ≠ 0)
    (hnorm : ‖(rv : E n)‖ = ‖(v : E n)‖)
    (hperp : ⟪(w : E n), (v : E n) - (rv : E n)⟫ = 0)
    (hcos : ⟪(v : E n), (rv : E n)⟫ =
      ‖(v : E n)‖ ^ 2 * Real.cos (2 * Real.pi / m)) :
    |⟪(v : E n), (w : E n)⟫| =
      ‖(v : E n)‖ * ‖(w : E n)‖ * Real.cos (Real.pi / m) := by
  let A : ℝ := 2 * Real.pi / (m : ℝ)
  let x : ℝ := Real.pi / (m : ℝ)
  let C : ℝ := Real.cos A
  let c : ℝ := Real.cos x
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hA0 : 0 < A := by dsimp only [A]; positivity
  have hApi : A < Real.pi := by
    dsimp only [A]
    rw [div_lt_iff₀ hmR]
    have hmR3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [Real.pi_pos]
  have hClt : C < 1 := by
    have hanti := Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
      (show A ∈ Set.Icc (0 : ℝ) Real.pi from ⟨hA0.le, hApi.le⟩) hA0
    simpa [C] using hanti
  have hCgt : -1 < C := by
    have hanti := Real.strictAntiOn_cos
      (show A ∈ Set.Icc (0 : ℝ) Real.pi from ⟨hA0.le, hApi.le⟩)
      (show Real.pi ∈ Set.Icc (0 : ℝ) Real.pi from ⟨Real.pi_pos.le, le_rfl⟩) hApi
    simpa [C] using hanti
  have hxpos : 0 < x := by dsimp only [x]; positivity
  have hxhalf : x < Real.pi / 2 := by
    dsimp only [x]
    rw [div_lt_iff₀ hmR]
    have hmR3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [Real.pi_pos]
  have hcpos : 0 < c := by
    dsimp only [c]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxhalf⟩
  have hnormV : ‖rv‖ = ‖v‖ := hnorm
  have hcosV : (⟪v, rv⟫ : ℝ) = ‖v‖ ^ 2 * C := by
    simpa [A, C] using hcos
  have hperpV : (⟪w, v - rv⟫ : ℝ) = 0 := by
    exact hperp
  let p : V := v - rv
  let q : V := v + rv
  have hpne : p ≠ 0 := by
    intro hp
    have hvr : v = rv := by
      apply sub_eq_zero.mp
      exact hp
    have hnpos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hvne)
    rw [← hvr, real_inner_self_eq_norm_sq] at hcosV
    nlinarith
  have hqne : q ≠ 0 := by
    intro hq
    have hvr : rv = -v := eq_neg_of_add_eq_zero_right hq
    have hnpos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hvne)
    rw [hvr, inner_neg_right, real_inner_self_eq_norm_sq] at hcosV
    nlinarith
  let K : Submodule ℝ V := (ℝ ∙ p)ᗮ
  letI : Fact (Module.finrank ℝ V = 1 + 1) := ⟨by omega⟩
  have hKrank : Module.finrank ℝ K = 1 := by
    dsimp only [K]
    exact Submodule.finrank_orthogonal_span_singleton hpne
  have hwK : w ∈ K := by
    dsimp only [K]
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    change (⟪p, w⟫ : ℝ) = 0
    rw [real_inner_comm]
    simpa [p] using hperpV
  have hqK : q ∈ K := by
    dsimp only [K]
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    change (⟪p, q⟫ : ℝ) = 0
    simp only [p, q, inner_add_right, inner_sub_left,
      real_inner_self_eq_norm_sq]
    rw [real_inner_comm rv v, hnormV]
    ring
  let qK : K := ⟨q, hqK⟩
  let wK : K := ⟨w, hwK⟩
  have hqKne : qK ≠ 0 := by
    intro h
    apply hqne
    have hv := congrArg Subtype.val h
    simpa [qK] using hv
  obtain ⟨s, hsK⟩ := exists_smul_eq_of_finrank_eq_one hKrank hqKne wK
  have hs : s • q = w := congrArg Subtype.val hsK
  have hsne : s ≠ 0 := by
    intro hs0
    subst s
    simp at hs
    exact hwne hs.symm
  have hhalf : 1 + C = 2 * c ^ 2 := by
    dsimp only [A, x, C, c]
    rw [show 2 * Real.pi / (m : ℝ) = 2 * (Real.pi / (m : ℝ)) by ring,
      Real.cos_two_mul]
    ring
  have hinner : (⟪v, w⟫ : ℝ) = 2 * s * ‖v‖ ^ 2 * c ^ 2 := by
    rw [← hs]
    change inner ℝ v (s • q) = 2 * s * ‖v‖ ^ 2 * c ^ 2
    rw [real_inner_smul_right v q s, inner_add_right,
      real_inner_self_eq_norm_sq, hcosV]
    calc
      s * (‖v‖ ^ 2 + ‖v‖ ^ 2 * C) = s * ‖v‖ ^ 2 * (1 + C) := by ring
      _ = 2 * s * ‖v‖ ^ 2 * c ^ 2 := by rw [hhalf]; ring
  have hqnormsq : ‖q‖ ^ 2 = (2 * ‖v‖ * c) ^ 2 := by
    calc
      ‖q‖ ^ 2 = (⟪q, q⟫ : ℝ) := (real_inner_self_eq_norm_sq q).symm
      _ = 2 * ‖v‖ ^ 2 * (1 + C) := by
        simp only [q, inner_add_left, inner_add_right,
          real_inner_self_eq_norm_sq]
        rw [real_inner_comm v rv, hnormV, hcosV]
        ring
      _ = (2 * ‖v‖ * c) ^ 2 := by rw [hhalf]; ring
  have hqnorm : ‖q‖ = 2 * ‖v‖ * c := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hqnormsq) with h | h
    · exact h
    · have hpos : 0 < 2 * ‖v‖ * c := by positivity
      nlinarith [norm_nonneg q]
  have hnormw : ‖w‖ = |s| * (2 * ‖v‖ * c) := by
    calc
      ‖w‖ = ‖s • q‖ := congrArg norm hs.symm
      _ = |s| * ‖q‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = |s| * (2 * ‖v‖ * c) := by rw [hqnorm]
  change |(⟪v, w⟫ : ℝ)| = ‖v‖ * ‖w‖ * c
  rw [hinner, hnormw]
  simp only [abs_mul, abs_sq, abs_of_nonneg (norm_nonneg v),
    abs_of_pos hcpos, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  ring

end LeanEval.Geometry.PlatonicClassification
