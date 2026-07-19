import Mathlib
import UnicoProofs.Platonici.FormulaRiflessione
import UnicoProofs.Platonici.Ordini

open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Il calcolo della matrice del prodotto di due riflessioni lineari
nella base formata dai rispettivi normali unitari. -/
theorem prodotto_riflessioni_traccia {α β : E n} (hα : ‖α‖ = 1)
    (hβ : ‖β‖ = 1) (s : E n → E n)
    (hs : ∀ x, s x = (x - (2 * ⟪β, x⟫ : ℝ) • β) -
      (2 * ⟪α, x - (2 * ⟪β, x⟫ : ℝ) • β⟫ : ℝ) • α) :
    s α = ((4 * ⟪α, β⟫ ^ 2 - 1 : ℝ)) • α -
        ((2 * ⟪α, β⟫ : ℝ)) • β ∧
      s β = ((2 * ⟪α, β⟫ : ℝ)) • α - β := by
  have hαα : (⟪α, α⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hα]
    norm_num
  have hββ : (⟪β, β⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hβ]
    norm_num
  have hβα : (⟪β, α⟫ : ℝ) = ⟪α, β⟫ := (real_inner_comm β α).symm
  constructor
  · rw [hs α]
    simp only [inner_sub_right, real_inner_smul_right, hαα, hβα]
    match_scalars <;> ring
  · rw [hs β]
    simp only [inner_sub_right, real_inner_smul_right, hββ]
    match_scalars <;> ring

/-- Se il prodotto delle due riflessioni lineari ha periodo `m`, il
prodotto scalare dei normali è, a segno vicino, il coseno di un multiplo
di `π / m`.  Non si richiede che `m` sia il periodo minimo. -/
theorem coseno_di_ordine {α β : E n} (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1)
    (hind : ∀ t : ℝ, β ≠ t • α) (m : ℕ) (hm : 2 ≤ m)
    (s : E n → E n)
    (hs : ∀ x, s x = (x - (2 * ⟪β, x⟫ : ℝ) • β) -
      (2 * ⟪α, x - (2 * ⟪β, x⟫ : ℝ) • β⟫ : ℝ) • α)
    (hord : ∀ x : E n, s^[m] x = x) :
    ∃ k : ℕ, k < m ∧
      ((⟪α, β⟫ : ℝ) = Real.cos (k * Real.pi / m) ∨
       (⟪α, β⟫ : ℝ) = -Real.cos (k * Real.pi / m)) := by
  let c : ℝ := ⟪α, β⟫
  have hαα : (⟪α, α⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hα]
    norm_num
  have hββ : (⟪β, β⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hβ]
    norm_num
  have hβα : (⟪β, α⟫ : ℝ) = c := by
    dsimp only [c]
    exact (real_inner_comm β α).symm
  have hαβ : (⟪α, β⟫ : ℝ) = c := rfl
  have hα_ne : α ≠ 0 := by
    intro h
    rw [h, norm_zero] at hα
    norm_num at hα
  have hlin : ∀ a b : ℝ,
      s (a • α + b • β) =
        (((4 * c ^ 2 - 1) * a + 2 * c * b) : ℝ) • α +
        ((-2 * c * a - b : ℝ)) • β := by
    intro a b
    rw [hs (a • α + b • β)]
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right,
      hαα, hββ, hβα, hαβ]
    match_scalars <;> ring
  let T : ℝ × ℝ → ℝ × ℝ := fun p =>
    (((4 * c ^ 2 - 1) * p.1 + 2 * c * p.2),
      (-2 * c * p.1 - p.2))
  let v : ℕ → ℝ × ℝ := fun q => T^[q] (1, 0)
  have hv_zero : v 0 = (1, 0) := by simp [v]
  have hv_succ (q : ℕ) : v (q + 1) = T (v q) := by
    simp only [v, Function.iterate_succ_apply']
  have hs_iter : ∀ q : ℕ,
      s^[q] α = (v q).1 • α + (v q).2 • β := by
    intro q
    induction q with
    | zero => simp [hv_zero]
    | succ q ih =>
        calc
          s^[q + 1] α = s (s^[q] α) := by
            rw [Function.iterate_succ_apply']
          _ = s ((v q).1 • α + (v q).2 • β) := congrArg s ih
          _ = (((4 * c ^ 2 - 1) * (v q).1 + 2 * c * (v q).2) : ℝ) • α +
              ((-2 * c * (v q).1 - (v q).2 : ℝ)) • β :=
            hlin (v q).1 (v q).2
          _ = (v (q + 1)).1 • α + (v (q + 1)).2 • β := by
            rw [hv_succ]
  have hvm_vec : (v m).1 • α + (v m).2 • β = α := by
    exact (hs_iter m).symm.trans (hord α)
  have hvm_snd : (v m).2 = 0 := by
    by_contra hb
    apply hind (((v m).2)⁻¹ * (1 - (v m).1))
    have hrel : (v m).2 • β = (1 - (v m).1) • α := by
      calc
        (v m).2 • β = α - (v m).1 • α := by
          exact (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using hvm_vec)
        _ = (1 - (v m).1) • α := by
          match_scalars
          ring
    have hscaled := congrArg (fun x : E n => ((v m).2)⁻¹ • x) hrel
    simpa [smul_smul, hb] using hscaled
  have hvm_fst : (v m).1 = 1 := by
    have heq : (v m).1 • α = α := by simpa [hvm_snd] using hvm_vec
    have hz : ((v m).1 - 1) • α = 0 := by
      rw [sub_smul, one_smul, heq, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hα_ne)
  have hvm : v m = (1, 0) := by
    apply Prod.ext
    · exact hvm_fst
    · exact hvm_snd
  by_cases hc : c = 0
  · have hsα_iter : ∀ q : ℕ, s^[q] α = ((-1 : ℝ) ^ q) • α := by
      intro q
      induction q with
      | zero => simp
      | succ q ih =>
          rw [Function.iterate_succ_apply', ih, hs]
          simp only [inner_smul_right, hβα, hc, mul_zero, zero_smul,
            sub_zero, hαα]
          match_scalars
          ring
    have hpow : (-1 : ℝ) ^ m = 1 := by
      have heq : ((-1 : ℝ) ^ m) • α = (1 : ℝ) • α := by
        simpa [hsα_iter m] using hord α
      exact (smul_left_injective ℝ hα_ne) heq
    have heven : Even m :=
      (neg_one_pow_eq_one_iff_even (R := ℝ) (by norm_num)).mp hpow
    obtain ⟨q, hq⟩ := heven
    have hqpos : 0 < q := by omega
    refine ⟨q, by omega, Or.inl ?_⟩
    change c = Real.cos ((q : ℝ) * Real.pi / (m : ℝ))
    rw [hc]
    have hang : (q : ℝ) * Real.pi / (m : ℝ) = Real.pi / 2 := by
      rw [hq]
      push_cast
      field_simp
      ring
    rw [hang, Real.cos_pi_div_two]
  · have habs : |c| ≤ 1 := by
      dsimp only [c]
      simpa [hα, hβ] using abs_real_inner_le_norm α β
    have hrad : 0 ≤ 1 - c ^ 2 := by
      have := (sq_le_one_iff_abs_le_one c).mpr habs
      linarith
    let d : ℝ := Real.sqrt (1 - c ^ 2)
    have hd_sq : d ^ 2 = 1 - c ^ 2 := by
      dsimp only [d]
      exact Real.sq_sqrt hrad
    let lam : ℂ := ((2 * c ^ 2 - 1 : ℝ) : ℂ) +
      ((2 * c * d : ℝ) : ℂ) * Complex.I
    have hchar : lam ^ 2 - (((4 * c ^ 2 - 2 : ℝ) : ℂ) * lam) + 1 = 0 := by
      dsimp only [lam]
      have hd_sq' : (d : ℂ) ^ 2 = 1 - (c : ℂ) ^ 2 := by
        exact_mod_cast hd_sq
      push_cast
      ring_nf
      rw [Complex.I_sq, hd_sq']
      ring
    have htrace_cast : (((4 * c ^ 2 - 2 : ℝ) : ℂ)) =
        4 * (c : ℂ) ^ 2 - 2 := by
      push_cast
      ring
    have hchar' : lam ^ 2 - (4 * (c : ℂ) ^ 2 - 2) * lam + 1 = 0 := by
      rw [← htrace_cast]
      exact hchar
    let z : ℕ → ℂ := fun q =>
      (lam + 1) * ((v q).1 : ℂ) + ((2 * c : ℝ) : ℂ) * ((v q).2 : ℂ)
    have hz_succ (q : ℕ) : z (q + 1) = lam * z q := by
      rw [show z (q + 1) =
          (lam + 1) * ((v (q + 1)).1 : ℂ) +
            ((2 * c : ℝ) : ℂ) * ((v (q + 1)).2 : ℂ) from rfl,
        hv_succ]
      change (lam + 1) *
          (((4 * c ^ 2 - 1) * (v q).1 + 2 * c * (v q).2 : ℝ) : ℂ) +
          ((2 * c : ℝ) : ℂ) *
            (((-2 * c * (v q).1 - (v q).2 : ℝ)) : ℂ) = lam * z q
      dsimp only [z]
      push_cast
      linear_combination (norm := ring) (-((v q).1 : ℂ)) * hchar'
    have hz_pow : ∀ q : ℕ, z q = lam ^ q * (lam + 1) := by
      intro q
      induction q with
      | zero => simp [z, hv_zero]
      | succ q ih =>
          rw [hz_succ, ih, pow_succ]
          ring
    have hlam_add : lam + 1 ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      simp [lam, pow_two, Complex.mul_re] at hre
      exact hc hre
    have hlampow : lam ^ m = 1 := by
      have hz_m : z m = lam + 1 := by simp [z, hvm]
      have heq : lam ^ m * (lam + 1) = 1 * (lam + 1) := by
        rw [← hz_pow m, hz_m, one_mul]
      exact mul_right_cancel₀ hlam_add heq
    have hm0 : m ≠ 0 := by omega
    letI : NeZero m := ⟨hm0⟩
    obtain ⟨k, hkm, hklam⟩ :=
      (Complex.isPrimitiveRoot_exp m hm0).eq_pow_of_pow_eq_one hlampow
    have hklam' :
        Complex.exp (((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (m : ℂ)))) = lam := by
      rw [Complex.exp_nat_mul]
      simpa [mul_assoc] using hklam
    have hre := congrArg Complex.re hklam'
    have hrelam : lam.re = 2 * c ^ 2 - 1 := by
      simp [lam, pow_two, Complex.mul_re]
    have hexp_re :
        (Complex.exp (((k : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I / (m : ℂ))))).re =
          Real.cos (2 * ((k : ℝ) * Real.pi / (m : ℝ))) := by
      rw [Complex.exp_re]
      simp
      congr 1
      field_simp
    rw [hexp_re, hrelam, Real.cos_two_mul] at hre
    have hsq : c ^ 2 = Real.cos ((k : ℝ) * Real.pi / (m : ℝ)) ^ 2 := by
      linarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with hpos | hneg
    · exact ⟨k, hkm, Or.inl (by simpa [c] using hpos)⟩
    · exact ⟨k, hkm, Or.inr (by simpa [c] using hneg)⟩

/-- Versione senza ipotesi di indipendenza. Se i normali sono paralleli,
la conclusione è il caso `k = 0`; altrimenti si applica
`coseno_di_ordine`. -/
theorem coseno_di_ordine_generale {α β : E n} (hα : ‖α‖ = 1)
    (hβ : ‖β‖ = 1) (m : ℕ) (hm : 2 ≤ m) (s : E n → E n)
    (hs : ∀ x, s x = (x - (2 * ⟪β, x⟫ : ℝ) • β) -
      (2 * ⟪α, x - (2 * ⟪β, x⟫ : ℝ) • β⟫ : ℝ) • α)
    (hord : ∀ x : E n, s^[m] x = x) :
    ∃ k : ℕ, k < m ∧
      ((⟪α, β⟫ : ℝ) = Real.cos (k * Real.pi / m) ∨
       (⟪α, β⟫ : ℝ) = -Real.cos (k * Real.pi / m)) := by
  by_cases hind : ∀ t : ℝ, β ≠ t • α
  · exact coseno_di_ordine hα hβ hind m hm s hs hord
  · push Not at hind
    obtain ⟨t, ht⟩ := hind
    have habst : |t| = 1 := by
      have hn := congrArg norm ht
      rw [hβ, norm_smul, hα, mul_one, Real.norm_eq_abs] at hn
      exact hn.symm
    have ht_sq : t ^ 2 = (1 : ℝ) ^ 2 := by
      have := congrArg (fun x : ℝ => x ^ 2) habst
      simpa using this
    have hinner : (⟪α, β⟫ : ℝ) = t := by
      rw [ht, real_inner_smul_right, real_inner_self_eq_norm_sq, hα]
      norm_num
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp ht_sq) with ht1 | htm1
    · refine ⟨0, by omega, Or.inl ?_⟩
      simp [hinner, ht1]
    · refine ⟨0, by omega, Or.inr ?_⟩
      simp [hinner, htm1]

/-- La parte lineare del prodotto affine delle due riflessioni semplici
ha un periodo che divide la corrispondente voce della matrice di
Coxeter.  La conclusione conserva inizialmente il valore assoluto anche
sul coseno; il lemma successivo lo ripiega nell'intervallo `[0, π/2]`. -/
theorem coseno_di_coxeter_assoluto (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) {i j : Fin n} (hij : i ≠ j)
    {αi pi αj pj : E n} (hαi : ‖αi‖ = 1) (hαj : ‖αj‖ = 1)
    (hri : ∀ x : E n, simpleReflection P hreg F i x =
      x - (2 * ⟪αi, x - pi⟫ : ℝ) • αi)
    (hrj : ∀ x : E n, simpleReflection P hreg F j x =
      x - (2 * ⟪αj, x - pj⟫ : ℝ) • αj) :
    ∃ k : ℕ, k < coxeterMatrix P hreg F i j ∧
      |(⟪αi, αj⟫ : ℝ)| =
        |Real.cos (k * Real.pi / (coxeterMatrix P hreg F i j : ℝ))| := by
  let ri : E n → E n := simpleReflection P hreg F i
  let rj : E n → E n := simpleReflection P hreg F j
  let g : E n → E n := fun x => ri (rj x)
  let s : E n → E n := fun x =>
    (x - (2 * ⟪αj, x⟫ : ℝ) • αj) -
      (2 * ⟪αi, x - (2 * ⟪αj, x⟫ : ℝ) • αj⟫ : ℝ) • αi
  have hs : ∀ x : E n, s x =
      (x - (2 * ⟪αj, x⟫ : ℝ) • αj) -
        (2 * ⟪αi, x - (2 * ⟪αj, x⟫ : ℝ) • αj⟫ : ℝ) • αi :=
    fun _ => rfl
  have hdiff : ∀ x v : E n, g (x + v) - g x = s v := by
    intro x v
    dsimp only [g, ri, rj]
    rw [hrj (x + v), hri, hrj x, hri]
    dsimp only [s]
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
    match_scalars <;> ring
  let a : symGroup P := simpleGen P hreg F i * simpleGen P hreg F j
  let m : ℕ := coxeterMatrix P hreg F i j
  have ha_iter : ∀ q : ℕ, ∀ x : E n,
      (((a ^ q : symGroup P) : Isom n) x) = g^[q] x := by
    intro q
    induction q with
    | zero => intro x; simp
    | succ q ih =>
        intro x
        rw [pow_succ, Function.iterate_succ_apply]
        change (((a ^ q : symGroup P) : Isom n)
          (((a : symGroup P) : Isom n) x)) = g^[q] (g x)
        rw [ih]
        rfl
  have ha_pow : a ^ m = 1 := by
    dsimp only [a, m, coxeterMatrix]
    exact pow_orderOf_eq_one _
  have hg_period : ∀ x : E n, g^[m] x = x := by
    intro x
    have heval := congrArg (fun u : symGroup P => ((u : Isom n) x)) ha_pow
    rw [ha_iter] at heval
    simpa using heval
  have hdiff_iter : ∀ q : ℕ, ∀ x v : E n,
      g^[q] (x + v) - g^[q] x = s^[q] v := by
    intro q
    induction q with
    | zero =>
        intro x v
        simp
    | succ q ih =>
        intro x v
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        have hq := ih x v
        have harg : g^[q] (x + v) = g^[q] x + s^[q] v := by
          exact sub_eq_iff_eq_add.mp hq |>.trans (add_comm _ _)
        rw [harg, hdiff]
        rw [Function.iterate_succ_apply']
  have hs_period : ∀ v : E n, s^[m] v = v := by
    intro v
    have h := hdiff_iter m 0 v
    rw [zero_add, hg_period, hg_period] at h
    simpa using h.symm
  have hm : 2 ≤ m := by
    dsimp only [m]
    exact coxeterMatrix_off_diag_ge P hreg F hij
  obtain ⟨k, hkm, hk⟩ :=
    coseno_di_ordine_generale hαi hαj m hm s hs hs_period
  refine ⟨k, by simpa [m] using hkm, ?_⟩
  rcases hk with hk | hk
  · simpa [m] using congrArg abs hk
  · simpa [m] using congrArg abs hk

/-- Un multiplo `kπ/m`, con `k < m`, può essere ripiegato in
`[0, π/2]` senza cambiare il valore assoluto del coseno. -/
theorem ripiega_coseno {m k : ℕ} (hm : 0 < m) (hk : k < m) :
    ∃ l : ℕ, l < m ∧
      |Real.cos (k * Real.pi / (m : ℝ))| =
        Real.cos (l * Real.pi / (m : ℝ)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  by_cases hhalf : 2 * k ≤ m
  · refine ⟨k, hk, ?_⟩
    apply abs_of_nonneg
    apply Real.cos_nonneg_of_mem_Icc
    have hx0 : (0 : ℝ) ≤ (k : ℝ) * Real.pi / (m : ℝ) := by positivity
    refine ⟨le_trans (by nlinarith [Real.pi_pos]) hx0, ?_⟩
    rw [div_le_iff₀ hmR]
    have hhalfR : (2 : ℝ) * (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hhalf
    nlinarith [Real.pi_pos]
  · have hkpos : 0 < k := by omega
    have hkmle : k ≤ m := Nat.le_of_lt hk
    have hlm : m - k < m := by omega
    have hhalf' : 2 * (m - k) ≤ m := by omega
    let l : ℕ := m - k
    have hl_nonneg : 0 ≤ Real.cos (l * Real.pi / (m : ℝ)) := by
      apply Real.cos_nonneg_of_mem_Icc
      have hy0 : (0 : ℝ) ≤ (l : ℝ) * Real.pi / (m : ℝ) := by positivity
      refine ⟨le_trans (by nlinarith [Real.pi_pos]) hy0, ?_⟩
      rw [div_le_iff₀ hmR]
      have hhalfR : (2 : ℝ) * (l : ℝ) ≤ (m : ℝ) := by
        dsimp only [l]
        exact_mod_cast hhalf'
      nlinarith [Real.pi_pos]
    have hang : (l : ℝ) * Real.pi / (m : ℝ) =
        Real.pi - (k : ℝ) * Real.pi / (m : ℝ) := by
      dsimp only [l]
      rw [Nat.cast_sub hkmle]
      field_simp
    have hcos : Real.cos (l * Real.pi / (m : ℝ)) =
        -Real.cos (k * Real.pi / (m : ℝ)) := by
      rw [hang, Real.cos_pi_sub]
    have hk_nonpos : Real.cos (k * Real.pi / (m : ℝ)) ≤ 0 := by
      linarith
    refine ⟨l, by simpa [l] using hlm, ?_⟩
    rw [abs_of_nonpos hk_nonpos]
    exact hcos.symm

/-- **Il ponte con il politopo.** Il valore assoluto del prodotto
scalare dei normali è un coseno determinato dall'ordine del prodotto
delle riflessioni semplici. -/
theorem coseno_di_coxeter (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) {i j : Fin n} (hij : i ≠ j)
    {αi pi αj pj : E n} (hαi : ‖αi‖ = 1) (hαj : ‖αj‖ = 1)
    (hri : ∀ x : E n, simpleReflection P hreg F i x =
      x - (2 * ⟪αi, x - pi⟫ : ℝ) • αi)
    (hrj : ∀ x : E n, simpleReflection P hreg F j x =
      x - (2 * ⟪αj, x - pj⟫ : ℝ) • αj) :
    ∃ k : ℕ, |(⟪αi, αj⟫ : ℝ)| =
      Real.cos (k * Real.pi / (coxeterMatrix P hreg F i j : ℝ)) := by
  obtain ⟨k, hkm, hk⟩ :=
    coseno_di_coxeter_assoluto P hreg F hij hαi hαj hri hrj
  have hmpos : 0 < coxeterMatrix P hreg F i j := by
    have := coxeterMatrix_off_diag_ge P hreg F hij
    omega
  obtain ⟨l, _hlm, hl⟩ := ripiega_coseno hmpos hkm
  refine ⟨l, hk.trans ?_⟩
  exact hl

end LeanEval.Geometry.PlatonicClassification
