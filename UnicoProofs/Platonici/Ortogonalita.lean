import Mathlib
import UnicoProofs.Platonici.FormulaRiflessione
import UnicoProofs.Platonici.Ordini

open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

theorem normali_lontani_ortogonali (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) {i j : Fin n} (hij : (i : ℕ) + 2 ≤ (j : ℕ))
    {αi pi αj pj : E n}
    (hαi : ‖αi‖ = 1)
    (hri : ∀ x : E n, simpleReflection P hreg F i x =
      x - (2 * ⟪αi, x - pi⟫ : ℝ) • αi)
    (hαj : ‖αj‖ = 1)
    (hrj : ∀ x : E n, simpleReflection P hreg F j x =
      x - (2 * ⟪αj, x - pj⟫ : ℝ) • αj) :
    ⟪αi, αj⟫ = 0 := by
  let ri := simpleReflection P hreg F i
  let rj := simpleReflection P hreg F j
  let c : ℝ := ⟪αi, αj⟫
  let ti : E n → ℝ := fun x => ⟪αi, x - pi⟫
  let tj : E n → ℝ := fun x => ⟪αj, x - pj⟫
  have hcomm : ∀ x : E n, ri (rj x) = rj (ri x) := by
    intro x
    exact congrArg (fun g : symGroup P => (g : Isom n) x)
      (simpleGen_far_comm P hreg F hij)
  have hexpanded : ∀ x : E n,
      (x - (2 * tj x : ℝ) • αj) -
          (2 * ⟪αi, (x - (2 * tj x : ℝ) • αj) - pi⟫ : ℝ) • αi =
        (x - (2 * ti x : ℝ) • αi) -
          (2 * ⟪αj, (x - (2 * ti x : ℝ) • αi) - pj⟫ : ℝ) • αj := by
    intro x
    have hi : ri (rj x) =
        (x - (2 * tj x : ℝ) • αj) -
          (2 * ⟪αi, (x - (2 * tj x : ℝ) • αj) - pi⟫ : ℝ) • αi := by
      calc
        ri (rj x) = rj x - (2 * ⟪αi, rj x - pi⟫ : ℝ) • αi := hri (rj x)
        _ = (x - (2 * tj x : ℝ) • αj) -
            (2 * ⟪αi, (x - (2 * tj x : ℝ) • αj) - pi⟫ : ℝ) • αi := by
          rw [hrj x]
    have hj : rj (ri x) =
        (x - (2 * ti x : ℝ) • αi) -
          (2 * ⟪αj, (x - (2 * ti x : ℝ) • αi) - pj⟫ : ℝ) • αj := by
      calc
        rj (ri x) = ri x - (2 * ⟪αj, ri x - pj⟫ : ℝ) • αj := hrj (ri x)
        _ = (x - (2 * ti x : ℝ) • αi) -
            (2 * ⟪αj, (x - (2 * ti x : ℝ) • αi) - pj⟫ : ℝ) • αj := by
          rw [hri x]
    exact hi.symm.trans ((hcomm x).trans hj)
  have hstar : ∀ x : E n,
      c • (tj x • αi - ti x • αj) = 0 := by
    intro x
    have h := hexpanded x
    have hii : ⟪αi, (x - (2 * tj x : ℝ) • αj) - pi⟫ =
        ti x - 2 * c * tj x := by
      dsimp only [ti, c]
      simp only [inner_sub_right, real_inner_smul_right]
      ring
    have hjj : ⟪αj, (x - (2 * ti x : ℝ) • αi) - pj⟫ =
        tj x - 2 * c * ti x := by
      dsimp only [tj, c]
      simp only [inner_sub_right, real_inner_smul_right]
      have hccomm : ⟪αj, αi⟫ = ⟪αi, αj⟫ := (real_inner_comm αj αi).symm
      rw [hccomm]
      ring
    rw [hii, hjj] at h
    linear_combination (norm := match_scalars <;> ring) (1 / 4 : ℝ) • h
  by_contra hc0
  change c ≠ 0 at hc0
  have hrel : ∀ x : E n, tj x • αi = ti x • αj := by
    intro x
    have hz := hstar x
    have : tj x • αi - ti x • αj = 0 :=
      (smul_eq_zero.mp hz).resolve_left hc0
    exact sub_eq_zero.mp this
  have hαj_ne : αj ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hαj
    norm_num at hαj
  have htipj : ti pj = 0 := by
    have h := hrel pj
    have hs : ti pj • αj = 0 := by
      simpa [tj] using h.symm
    exact (smul_eq_zero.mp hs).resolve_right hαj_ne
  have htj : tj (pj + αj) = 1 := by
    change ⟪αj, (pj + αj) - pj⟫ = 1
    have heq : (pj + αj) - pj = αj := by abel
    rw [heq, real_inner_self_eq_norm_sq, hαj]
    norm_num
  have hti : ti (pj + αj) = c := by
    change ⟪αi, (pj + αj) - pi⟫ = c
    have heq : (pj + αj) - pi = (pj - pi) + αj := by abel
    rw [heq, inner_add_right]
    change ti pj + c = c
    rw [htipj, zero_add]
  have hparallel : αi = c • αj := by
    have h := hrel (pj + αj)
    rw [htj, hti, one_smul] at h
    exact h
  have habs : |c| = 1 := by
    have hn := congrArg norm hparallel
    rw [hαi, norm_smul, hαj, mul_one, Real.norm_eq_abs] at hn
    exact hn.symm
  have hc2 : c * c = 1 := by
    have h := congrArg (fun t : ℝ => t * t) habs
    simpa [abs_mul_abs_self] using h
  let v : E n := (2 * ⟪αj, pi - pj⟫ : ℝ) • αj
  have htrans : ∀ x : E n, ri (rj x) = x + v := by
    intro x
    change simpleReflection P hreg F i
      (simpleReflection P hreg F j x) = x + v
    rw [hrj x, hri, hparallel]
    simp only [inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hαj, one_pow,
      mul_one]
    change _ = x + (2 * ⟪αj, pi - pj⟫ : ℝ) • αj
    rw [inner_sub_right]
    have hc_sq : c ^ 2 = 1 := by simpa [pow_two] using hc2
    match_scalars <;> ring_nf
    rw [hc_sq]
    ring
  have hcycle : ∀ x : E n, (x + v) + v = x := by
    intro x
    calc
      (x + v) + v = ri (rj (ri (rj x))) := by
        rw [htrans x, htrans (x + v)]
      _ = x := simpleReflection_far_rel P hreg F hij x
  have hv : v = 0 := by
    have hz := hcycle (0 : E n)
    have htwo : (2 : ℝ) • v = 0 := by
      simpa [two_smul] using hz
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hone : simpleGen P hreg F i * simpleGen P hreg F j = 1 := by
    apply Subtype.ext
    apply AffineIsometryEquiv.ext
    intro x
    have h := htrans x
    rw [hv, add_zero] at h
    exact h
  have hijne : i ≠ j := by
    intro heq
    subst j
    omega
  have hge := coxeterMatrix_off_diag_ge P hreg F hijne
  have hord : coxeterMatrix P hreg F i j = 1 := by
    unfold coxeterMatrix
    rw [hone]
    exact orderOf_one
  omega

theorem esistono_normali_ortogonali (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) {i j : Fin n} (hij : (i : ℕ) + 2 ≤ (j : ℕ)) :
    ∃ αi αj : E n, ‖αi‖ = 1 ∧ ‖αj‖ = 1 ∧ ⟪αi, αj⟫ = 0 := by
  obtain ⟨αi, pi, hαi, hri⟩ := simpleReflection_formula P hreg F i
  obtain ⟨αj, pj, hαj, hrj⟩ := simpleReflection_formula P hreg F j
  exact ⟨αi, αj, hαi, hαj,
    normali_lontani_ortogonali P hreg F hij hαi hri hαj hrj⟩

end LeanEval.Geometry.PlatonicClassification
