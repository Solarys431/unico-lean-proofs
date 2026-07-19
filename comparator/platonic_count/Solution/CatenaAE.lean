import Mathlib

noncomputable section

open scoped RealInnerProductSpace

namespace CatenaAE

section Restrizione

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A linear isometry fixing `w` preserves the line spanned by `w`. -/
theorem map_span_fixed (L : V ≃ₗᵢ[ℝ] V) (w : V) (hLw : L w = w) :
    (ℝ ∙ w).map (L.toLinearEquiv : V →ₗ[ℝ] V) = ℝ ∙ w := by
  rw [Submodule.map_span]
  rw [Set.image_singleton]
  change ℝ ∙ L w = ℝ ∙ w
  rw [hLw]

/-- The orthogonal complement of a fixed line is invariant. -/
theorem map_orthogonal_span_fixed (L : V ≃ₗᵢ[ℝ] V) (w : V) (hLw : L w = w) :
    ((ℝ ∙ w)ᗮ).map (L.toLinearEquiv : V →ₗ[ℝ] V) = (ℝ ∙ w)ᗮ := by
  calc
    ((ℝ ∙ w)ᗮ).map (L.toLinearEquiv : V →ₗ[ℝ] V) =
        ((ℝ ∙ w).map (L.toLinearEquiv : V →ₗ[ℝ] V))ᗮ :=
      Submodule.map_orthogonal_equiv (ℝ ∙ w) L
    _ = (ℝ ∙ w)ᗮ := congrArg Submodule.orthogonal (map_span_fixed L w hLw)

/-- Restriction of a linear isometry to the invariant orthogonal plane. -/
def restrizione (L : V ≃ₗᵢ[ℝ] V) (w : V) (hLw : L w = w) :
    (ℝ ∙ w)ᗮ ≃ₗᵢ[ℝ] (ℝ ∙ w)ᗮ :=
  (LinearIsometryEquiv.submoduleMap ((ℝ ∙ w)ᗮ) L).trans
    (LinearIsometryEquiv.ofEq _ _ (map_orthogonal_span_fixed L w hLw))

/-- In a three-dimensional space, the orthogonal complement of a nonzero line has dimension two. -/
theorem finrank_orthogonal_span_eq_two [Fact (Module.finrank ℝ V = 3)]
    {w : V} (hw : w ≠ 0) : Module.finrank ℝ ((ℝ ∙ w)ᗮ) = 2 :=
  Submodule.finrank_orthogonal_span_singleton (n := 2) hw

end Restrizione

section DeterminanteNegativo

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- A two-dimensional linear isometry with negative determinant is an involution. -/
theorem involutive_of_det_neg (o : Orientation ℝ E (Fin 2)) (f : E ≃ₗᵢ[ℝ] E)
    (hdet : LinearMap.det (f.toLinearEquiv : E →ₗ[ℝ] E) < 0) :
    ∀ x : E, f (f x) = x := by
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ E := by
    rw [Fintype.card_fin]
    exact (@Fact.out (Module.finrank ℝ E = 2) _).symm
  have hmap : Orientation.map (Fin 2) f.toLinearEquiv o = -o :=
    (o.map_eq_neg_iff_det_neg f.toLinearEquiv hcard).2 hdet
  have hanti : ∀ z : E,
      f (o.rightAngleRotation z) = -o.rightAngleRotation (f z) := by
    intro z
    calc
      f (o.rightAngleRotation z) =
          (Orientation.map (Fin 2) f.toLinearEquiv o).rightAngleRotation (f z) := by
        symm
        simpa using o.rightAngleRotation_map f (f z)
      _ = (-o).rightAngleRotation (f z) := by rw [hmap]
      _ = -o.rightAngleRotation (f z) := o.rightAngleRotation_neg_orientation (f z)
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · let B := o.basisRightAngleRotation x hx
    let a : ℝ := B.repr (f x) 0
    let b : ℝ := B.repr (f x) 1
    have hdecomp : f x = a • x + b • o.rightAngleRotation x := by
      rw [← B.sum_repr (f x)]
      simp [B, a, b, Fin.sum_univ_succ]
    have hab : a ^ 2 + b ^ 2 = 1 := by
      have horth : ⟪a • x, b • o.rightAngleRotation x⟫ = 0 := by
        rw [real_inner_smul_left, real_inner_smul_right,
          o.inner_rightAngleRotation_right]
        simp
      have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (a • x) (b • o.rightAngleRotation x) horth
      rw [← hdecomp, f.norm_map] at hpyth
      simp only [norm_smul, o.rightAngleRotation.norm_map, Real.norm_eq_abs] at hpyth
      have hnorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
      nlinarith [sq_abs a, sq_abs b]
    rw [hdecomp, map_add, map_smul, map_smul, hanti, hdecomp]
    simp only [map_add, map_smul, o.rightAngleRotation_rightAngleRotation,
      smul_add, smul_neg, smul_smul]
    calc
      _ = (a ^ 2 + b ^ 2) • x := by module
      _ = x := by rw [hab, one_smul]

end DeterminanteNegativo

section RotazioneOrdineAlmenoTre

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

omit [Fact (Module.finrank ℝ E = 2)] in
/-- The determinant of a linear isometric equivalence is nonzero. -/
theorem det_ne_zero_linearIsometryEquiv (f : E ≃ₗᵢ[ℝ] E) :
    LinearMap.det (f.toLinearEquiv : E →ₗ[ℝ] E) ≠ 0 := by
  intro hzero
  have hprod := f.toLinearEquiv.det_mul_det_symm
  rw [hzero, zero_mul] at hprod
  exact zero_ne_one hprod

/-- If an isometry is not an involution at one point, its determinant is positive. -/
theorem det_pos_of_exists_sq_ne (o : Orientation ℝ E (Fin 2)) (f : E ≃ₗᵢ[ℝ] E)
    (h : ∃ x : E, f (f x) ≠ x) :
    0 < LinearMap.det (f.toLinearEquiv : E →ₗ[ℝ] E) := by
  let d : ℝ := LinearMap.det (f.toLinearEquiv : E →ₗ[ℝ] E)
  have hdne : d ≠ 0 := det_ne_zero_linearIsometryEquiv f
  rcases lt_trichotomy d 0 with hneg | hzero | hpos
  · obtain ⟨x, hx⟩ := h
    exact (hx (involutive_of_det_neg o f hneg x)).elim
  · exact (hdne hzero).elim
  · simpa [d] using hpos

/-- A two-step orbit which does not return forces the isometry to be a rotation. -/
theorem exists_rotation_of_two_step_ne (o : Orientation ℝ E (Fin 2))
    (f : E ≃ₗᵢ[ℝ] E) {x y : E} (hxy : f x = y) (hyx : f y ≠ x) :
    ∃ θ : Real.Angle, f = o.rotation θ := by
  apply o.exists_linearIsometryEquiv_eq_of_det_pos
  apply det_pos_of_exists_sq_ne o f
  refine ⟨x, ?_⟩
  rw [hxy]
  exact hyx

/-- In dimension two, a linear isometry has determinant `1` or `-1`. -/
theorem det_eq_one_or_neg_one (o : Orientation ℝ E (Fin 2)) (f : E ≃ₗᵢ[ℝ] E) :
    LinearMap.det (f.toLinearEquiv : E →ₗ[ℝ] E) = 1 ∨
      LinearMap.det (f.toLinearEquiv : E →ₗ[ℝ] E) = -1 := by
  let d : ℝ := LinearMap.det (f.toLinearEquiv : E →ₗ[ℝ] E)
  have hdne : d ≠ 0 := det_ne_zero_linearIsometryEquiv f
  rcases lt_trichotomy d 0 with hneg | hzero | hpos
  · right
    have hff :
        (f.toLinearEquiv : E →ₗ[ℝ] E).comp (f.toLinearEquiv : E →ₗ[ℝ] E) =
          LinearMap.id := by
      ext z
      exact involutive_of_det_neg o f hneg z
    have hsq : d * d = 1 := by
      simpa only [d, LinearMap.det_comp, LinearMap.det_id] using congrArg LinearMap.det hff
    nlinarith
  · exact (hdne hzero).elim
  · left
    obtain ⟨θ, hθ⟩ := o.exists_linearIsometryEquiv_eq_of_det_pos hpos
    rw [hθ]
    exact o.det_rotation θ

/-- Absolute-value form of the preceding determinant dichotomy. -/
theorem abs_det_linearIsometryEquiv (o : Orientation ℝ E (Fin 2)) (f : E ≃ₗᵢ[ℝ] E) :
    |LinearMap.det (f.toLinearEquiv : E →ₗ[ℝ] E)| = 1 := by
  rcases det_eq_one_or_neg_one o f with hdet | hdet
  · rw [hdet, abs_one]
  · rw [hdet, abs_neg, abs_one]

end RotazioneOrdineAlmenoTre

section CostanzaOangle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- The oriented angle attached to consecutive indices is invariant under one cyclic step. -/
theorem oangle_finRotate_step {n : ℕ} (o : Orientation ℝ E (Fin 2))
    (θ : Real.Angle) (e : Fin (n + 1) → E)
    (hstep : ∀ i : Fin (n + 1), e (finRotate (n + 1) i) = o.rotation θ (e i))
    (i : Fin (n + 1)) :
    o.oangle (e (finRotate (n + 1) i))
        (e (finRotate (n + 1) (finRotate (n + 1) i))) =
      o.oangle (e i) (e (finRotate (n + 1) i)) := by
  calc
    o.oangle (e (finRotate (n + 1) i))
        (e (finRotate (n + 1) (finRotate (n + 1) i))) =
        o.oangle (o.rotation θ (e i))
          (o.rotation θ (e (finRotate (n + 1) i))) :=
      congrArg₂ o.oangle (hstep i) (hstep (finRotate (n + 1) i))
    _ = o.oangle (e i) (e (finRotate (n + 1) i)) :=
      o.oangle_rotation (e i) (e (finRotate (n + 1) i)) θ

/-- All oriented angles along a cyclic rotation orbit are equal. -/
theorem oangle_finRotate_const {n : ℕ} (o : Orientation ℝ E (Fin 2))
    (θ : Real.Angle) (e : Fin (n + 1) → E)
    (hstep : ∀ i : Fin (n + 1), e (finRotate (n + 1) i) = o.rotation θ (e i)) :
    ∀ i j : Fin (n + 1),
      o.oangle (e i) (e (finRotate (n + 1) i)) =
        o.oangle (e j) (e (finRotate (n + 1) j)) := by
  let r : Equiv.Perm (Fin (n + 1)) := finRotate (n + 1)
  let A : Fin (n + 1) → Real.Angle := fun i ↦ o.oangle (e i) (e (r i))
  have hA : ∀ i : Fin (n + 1), A (r i) = A i := by
    intro i
    exact oangle_finRotate_step o θ e hstep i
  have hbase : ∀ i : Fin (n + 1), A i = A 0 := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
        calc
          A i.succ = A (r i.castSucc) := by
            congr 1
            simp [r]
          _ = A i.castSucc := hA i.castSucc
          _ = A 0 := ih
  intro i j
  exact (hbase i).trans (hbase j).symm

end CostanzaOangle

section EstrazioneAngolo

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- The `m`-fold iterate of a rotation is rotation by the `m`-fold sum of its angle. -/
theorem rotation_iterate_apply (o : Orientation ℝ E (Fin 2)) (θ : Real.Angle)
    (m : ℕ) (x : E) :
    ((fun z : E ↦ o.rotation θ z)^[m]) x = o.rotation (m • θ) x := by
  have hpow : ∀ k : ℕ,
      (o.rotation θ).toLinearEquiv ^ k = (o.rotation (k • θ)).toLinearEquiv := by
    intro k
    induction k with
    | zero => ext z; simp
    | succ k ih =>
        rw [pow_succ, ih]
        ext z
        simp only [LinearEquiv.mul_apply, LinearIsometryEquiv.coe_toLinearEquiv]
        rw [o.rotation_rotation, succ_nsmul]
  calc
    ((fun z : E ↦ o.rotation θ z)^[m]) x =
        ((o.rotation θ).toLinearEquiv ^ m) x :=
      (LinearEquiv.pow_apply (o.rotation θ).toLinearEquiv m x).symm
    _ = o.rotation (m • θ) x := congrArg (fun g : E ≃ₗ[ℝ] E ↦ g x) (hpow m)

/-- A nonzero fixed vector for an iterated rotation forces the total angle to vanish. -/
theorem nsmul_angle_eq_zero_of_rotation_iterate_fixed
    (o : Orientation ℝ E (Fin 2)) (θ : Real.Angle) (q : ℕ) {x : E}
    (hx : x ≠ 0) (hfix : ((fun z : E ↦ o.rotation θ z)^[q]) x = x) :
    q • θ = 0 := by
  have hrot : o.rotation (q • θ) x = x := by
    rw [← rotation_iterate_apply o θ q x]
    exact hfix
  exact (o.rotation_eq_self_iff_angle_eq_zero hx (q • θ)).mp hrot

/-- A torsion angle is represented by an integral multiple of `2π/q`. -/
theorem angle_eq_two_pi_mul_int_div_of_nsmul_eq_zero
    (θ : Real.Angle) {q : ℕ} (hq : 1 ≤ q) (hzero : q • θ = 0) :
    ∃ k : ℤ,
      θ = ((2 * Real.pi * (k : ℝ) / (q : ℝ) : ℝ) : Real.Angle) := by
  have hcoe :
      (((q : ℝ) * θ.toReal : ℝ) : Real.Angle) = 0 := by
    rw [Real.Angle.natCast_mul_eq_nsmul]
    simpa only [Real.Angle.coe_toReal] using hzero
  obtain ⟨k, hk⟩ := Real.Angle.coe_eq_zero_iff.mp hcoe
  have hk' : (k : ℝ) * (2 * Real.pi) = (q : ℝ) * θ.toReal := by
    simpa only [zsmul_eq_mul] using hk
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  refine ⟨k, ?_⟩
  rw [← Real.Angle.coe_toReal θ]
  apply congrArg (fun t : ℝ ↦ (t : Real.Angle))
  apply (eq_div_iff hq0).2
  calc
    θ.toReal * (q : ℝ) = (q : ℝ) * θ.toReal := mul_comm _ _
    _ = (k : ℝ) * (2 * Real.pi) := hk'.symm
    _ = 2 * Real.pi * (k : ℝ) := by ring

/-- Combined extraction theorem from a fixed nonzero vector. -/
theorem exists_angle_eq_two_pi_mul_int_div_of_rotation_iterate_fixed
    (o : Orientation ℝ E (Fin 2)) (θ : Real.Angle) {q : ℕ} (hq : 1 ≤ q)
    {x : E} (hx : x ≠ 0) (hfix : ((fun z : E ↦ o.rotation θ z)^[q]) x = x) :
    q • θ = 0 ∧
      ∃ k : ℤ,
        θ = ((2 * Real.pi * (k : ℝ) / (q : ℝ) : ℝ) : Real.Angle) := by
  have hzero := nsmul_angle_eq_zero_of_rotation_iterate_fixed o θ q hx hfix
  exact ⟨hzero, angle_eq_two_pi_mul_int_div_of_nsmul_eq_zero θ hq hzero⟩

end EstrazioneAngolo

end CatenaAE
