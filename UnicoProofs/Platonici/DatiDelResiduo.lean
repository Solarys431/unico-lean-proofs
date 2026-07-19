import Mathlib
import UnicoProofs.Platonici.CollassoK

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Parte lineare del prodotto delle due riflessioni semplici adiacenti. -/
noncomputable def rhoLineare (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n) : E n ≃ₗᵢ[ℝ] E n :=
  ((((rhoSimple P hreg F i hi : symGroup P) : Isom n)).linearIsometryEquiv)

/-- Formula esplicita della parte lineare di `rhoSimple`. -/
theorem rhoLineare_formula (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    {αi pi αj pj : E n}
    (hri : ∀ x, simpleReflection P hreg F i x =
      x - (2 * ⟪αi, x - pi⟫ : ℝ) • αi)
    (hrj : ∀ x, simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ x =
      x - (2 * ⟪αj, x - pj⟫ : ℝ) • αj) (x : E n) :
    rhoLineare P hreg F i hi x =
      (x - (2 * ⟪αj, x⟫ : ℝ) • αj) -
        (2 * ⟪αi, x - (2 * ⟪αj, x⟫ : ℝ) • αj⟫ : ℝ) • αi := by
  have hmap := ((((rhoSimple P hreg F i hi : symGroup P) : Isom n)).map_vsub x 0)
  have heval : ∀ z : E n,
      (((rhoSimple P hreg F i hi : symGroup P) : Isom n) z) =
        simpleReflection P hreg F i
          (simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ z) := by
    intro z
    rfl
  have hmap' : rhoLineare P hreg F i hi x =
      simpleReflection P hreg F i
          (simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ x) -
        simpleReflection P hreg F i
          (simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ 0) := by
    rw [heval x, heval 0] at hmap
    simpa only [rhoLineare, vsub_eq_sub, sub_zero] using hmap
  rw [hrj x, hri, hrj 0, hri] at hmap'
  rw [hmap']
  simp only [zero_sub, inner_sub_right, inner_neg_right,
    real_inner_smul_right]
  match_scalars <;> ring

/-- Restrizione canonica della parte lineare di `rhoSimple` al piano
generato dai due normali, con la formula di compatibilità nel corpo ambiente. -/
theorem esiste_restrizione (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    {αi pi αj pj : E n} (hαi : ‖αi‖ = 1) (hαj : ‖αj‖ = 1)
    (hri : ∀ x, simpleReflection P hreg F i x =
      x - (2 * ⟪αi, x - pi⟫ : ℝ) • αi)
    (hrj : ∀ x, simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ x =
      x - (2 * ⟪αj, x - pj⟫ : ℝ) • αj)
    (V : Submodule ℝ (E n))
    (hVspan : V = Submodule.span ℝ ({αi, αj} : Set (E n))) :
    ∃ R : V ≃ₗᵢ[ℝ] V,
      orderOf R = coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ ∧
      ∀ y : V, ((R y : V) : E n) = rhoLineare P hreg F i hi (y : E n) := by
  let S : E n ≃ₗᵢ[ℝ] E n := rhoLineare P hreg F i hi
  have hαiV : αi ∈ V := by
    rw [hVspan]
    exact Submodule.subset_span (by simp)
  have hαjV : αj ∈ V := by
    rw [hVspan]
    exact Submodule.subset_span (by simp)
  have hSV : ∀ x ∈ V, S x ∈ V := by
    intro x hx
    rw [rhoLineare_formula P hreg F i hi hri hrj]
    exact V.sub_mem
      (V.sub_mem hx (V.smul_mem (2 * ⟪αj, x⟫ : ℝ) hαjV))
      (V.smul_mem
        (2 * ⟪αi, x - (2 * ⟪αj, x⟫ : ℝ) • αj⟫ : ℝ) hαiV)
  let SV : V →ₗ[ℝ] V := S.toLinearEquiv.toLinearMap.restrict hSV
  have hSVinj : Function.Injective SV := by
    intro x y hxy
    apply Subtype.ext
    apply S.injective
    exact congrArg Subtype.val hxy
  have hSVsurj : Function.Surjective SV :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hSVinj
  let eV : V ≃ₗ[ℝ] V := LinearEquiv.ofBijective SV ⟨hSVinj, hSVsurj⟩
  let R : V ≃ₗᵢ[ℝ] V := LinearIsometryEquiv.mk eV (fun x => by
    change ‖S (x : E n)‖ = ‖(x : E n)‖
    exact S.norm_map x)
  have hRcoe : ∀ y : V, ((R y : V) : E n) = S (y : E n) := by
    intro y
    rfl
  refine ⟨R, ?_, fun y => hRcoe y⟩
  let m : ℕ := coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩
  let a : symGroup P := rhoSimple P hreg F i hi
  have hRpow : ∀ q : ℕ, ∀ y : V,
      ((((R ^ q) y : V) : E n)) = (S ^ q) (y : E n) := by
    intro q
    induction q with
    | zero => intro y; simp
    | succ q ih =>
        intro y
        rw [pow_succ, pow_succ]
        change ((((R ^ q) (R y) : V) : E n)) =
          (S ^ q) (S (y : E n))
        rw [ih, hRcoe]
  have hlinpow : ∀ q : ℕ,
      ((((a ^ q : symGroup P) : Isom n)).linearIsometryEquiv) = S ^ q := by
    intro q
    induction q with
    | zero => rfl
    | succ q ih =>
        rw [pow_succ, pow_succ]
        change ((((a ^ q : symGroup P) : Isom n)).linearIsometryEquiv) *
            (((a : symGroup P) : Isom n)).linearIsometryEquiv = S ^ q * S
        rw [ih]
        rfl
  have ha_m : a ^ m = 1 := by
    dsimp only [a, m, rhoSimple, coxeterMatrix]
    exact pow_orderOf_eq_one _
  have hS_m : S ^ m = 1 := by
    have ha_m_isom : (((a ^ m : symGroup P) : Isom n)) = 1 :=
      congrArg Subtype.val ha_m
    have hlin := congrArg AffineIsometryEquiv.linearIsometryEquiv ha_m_isom
    rw [hlinpow] at hlin
    exact hlin
  have hR_m : R ^ m = 1 := by
    apply LinearIsometryEquiv.ext
    intro y
    apply Subtype.ext
    rw [hRpow]
    have hy := congrArg (fun T : E n ≃ₗᵢ[ℝ] E n => T (y : E n)) hS_m
    simpa using hy
  have hR_dvd_m : orderOf R ∣ m := orderOf_dvd_of_pow_eq_one hR_m
  let q : ℕ := orderOf R
  have hR_q : R ^ q = 1 := by
    dsimp only [q]
    exact pow_orderOf_eq_one R
  have hS_q : ∀ x : E n, (S ^ q) x = x := by
    intro x
    obtain ⟨y, hy, z, hz, rfl⟩ := V.exists_add_mem_mem_orthogonal x
    have hSy : (S ^ q) y = y := by
      let yV : V := ⟨y, hy⟩
      have hRq_y := congrArg (fun T : V ≃ₗᵢ[ℝ] V => T yV) hR_q
      have hRq_y' : (R ^ q) yV = yV := by simpa using hRq_y
      have hRq_y_coe := congrArg Subtype.val hRq_y'
      have hp := hRpow q yV
      exact hp.symm.trans hRq_y_coe
    have hαiz : ⟪αi, z⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal hαiV hz
    have hαjz : ⟪αj, z⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal hαjV hz
    have hSz : S z = z := by
      rw [rhoLineare_formula P hreg F i hi hri hrj]
      simp [hαiz, hαjz]
    have hS_pow_z : ∀ k : ℕ, (S ^ k) z = z := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ]
          change (S ^ k) (S z) = z
          rw [hSz, ih]
    rw [map_add, hSy, hS_pow_z]
  have hiter : ∀ k : ℕ, ∀ x : E n, (⇑S)^[k] x = (S ^ k) x := by
    intro k
    induction k with
    | zero => intro x; simp
      | succ k ih =>
          intro x
          rw [Function.iterate_succ_apply, pow_succ]
          change (⇑S)^[k] (S x) = (S ^ k) (S x)
          exact ih (S x)
  have hm_dvd_q : m ∣ q := by
    apply periodo_lineare_multiplo_coxeter P hreg F hri hrj q
    intro x
    rw [show (fun x : E n =>
        (x - (2 * ⟪αj, x⟫ : ℝ) • αj) -
          (2 * ⟪αi, x - (2 * ⟪αj, x⟫ : ℝ) • αj⟫ : ℝ) • αi) =
        (S : E n → E n) by
      funext y
      exact (rhoLineare_formula P hreg F i hi hri hrj y).symm]
    rw [hiter]
    exact hS_q x
  dsimp only [m, q] at hm_dvd_q hR_dvd_m ⊢
  exact Nat.dvd_antisymm hR_dvd_m hm_dvd_q

/-! ## Libertà dell'orbita ciclica sulla faccia di rango `i` -/

/-- Ogni potenza di `rhoSimple` fissa le facce della bandiera base di
rango diverso dai due ranghi adiacenti coinvolti. -/
theorem rhoSimple_pow_fissa_faccia (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (k : Fin n)
    (hki : k ≠ i) (hkj : k ≠ ⟨(i : ℕ) + 1, hi⟩) (t : ℕ) :
    (⇑((((rhoSimple P hreg F i hi) ^ t : symGroup P) : Isom n))) ''
        F.face k = F.face k := by
  let g : symGroup P := rhoSimple P hreg F i hi
  have hg : (⇑((g : symGroup P) : Isom n)) '' F.face k = F.face k := by
    calc
      (⇑((g : symGroup P) : Isom n)) '' F.face k =
          (⇑(simpleReflection P hreg F i)) ''
            ((⇑(simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩)) ''
              F.face k) := by
                rw [Set.image_image]
                rfl
      _ = F.face k := by
        rw [simpleReflection_fissa_facce P hreg F
          ⟨(i : ℕ) + 1, hi⟩ hkj,
          simpleReflection_fissa_facce P hreg F i hki]
  change (⇑((((g : symGroup P) ^ t : symGroup P) : Isom n))) ''
      F.face k = F.face k
  induction t with
  | zero => simp
  | succ t iht =>
      rw [pow_succ]
      calc
        (⇑((((g ^ t) * g : symGroup P) : Isom n))) '' F.face k =
            (⇑(((g ^ t : symGroup P) : Isom n))) ''
              ((⇑((g : symGroup P) : Isom n)) '' F.face k) := by
                rw [Set.image_image]
                rfl
        _ = F.face k := by rw [hg, iht]

/-- La stabilità della faccia di rango `i` lungo l'orbita ciclica implica
la divisibilità dell'esponente per l'ordine di Coxeter. -/
theorem rhoSimple_pow_stabilizza_faccia_dvd (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hn : 3 ≤ n) (t : ℕ)
    (hfix : (⇑((((rhoSimple P hreg F i hi) ^ t : symGroup P) : Isom n))) ''
      F.face i = F.face i) :
    coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ ∣ t := by
  let j : Fin n := ⟨(i : ℕ) + 1, hi⟩
  let a : symGroup P := simpleGen P hreg F i
  let b : symGroup P := simpleGen P hreg F j
  let g : symGroup P := a * b
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    dsimp only [j] at this
    omega
  have hg_rho : g = rhoSimple P hreg F i hi := by rfl
  have hgfix : (⇑(((g ^ t : symGroup P) : Isom n))) '' F.face i =
      F.face i := by simpa only [hg_rho] using hfix
  let φ : Isom n := ((g ^ t : symGroup P) : Isom n)
  have hφ : P.isSymmetry φ := (g ^ t).property
  let G : P.Flag := mapFlag P hφ F
  have hGface : ∀ k : Fin n, k ≠ j → G.face k = F.face k := by
    intro k hkj
    by_cases hki : k = i
    · subst k
      simpa only [G, mapFlag_face, φ] using hgfix
    · simpa only [G, mapFlag_face, φ, hg_rho] using
        rhoSimple_pow_fissa_faccia P hreg F i hi k hki hkj t
  have hGcases : G = F ∨ G = adjacentFlag P hreg.1 F j := by
    by_cases hGF : G = F
    · exact Or.inl hGF
    · refine Or.inr (adjacentFlag_eq_of_isAdjacent P hreg.1 j ?_)
      refine ⟨hGface, ?_⟩
      intro hjface
      apply hGF
      apply flag_ext
      funext k
      by_cases hkj : k = j
      · simpa only [hkj] using hjface
      · exact hGface k hkj
  rcases hGcases with hGF | hGadj
  · have hid : ∀ x : E n, φ x = x :=
      eq_id_of_mapFlag_eq P hreg.1 hφ F hGF
    have hgt : g ^ t = 1 := by
      apply Subtype.ext
      apply AffineIsometryEquiv.ext
      exact hid
    dsimp only [g, a, b, j, coxeterMatrix]
    exact orderOf_dvd_of_pow_eq_one hgt
  · have hmapb : mapFlag P b.property F = adjacentFlag P hreg.1 F j := by
      dsimp only [b]
      exact simpleReflection_mapFlag P hreg F j
    have hφb : ∀ x : E n, φ x = ((b : symGroup P) : Isom n) x :=
      symmetry_action_injective P hreg.1 F hφ b.property
        (hGadj.trans hmapb.symm)
    have hgtb : g ^ t = b := by
      apply Subtype.ext
      apply AffineIsometryEquiv.ext
      exact hφb
    have ha2 : a * a = 1 := by
      dsimp only [a]
      exact simpleGen_sq P hreg F i
    have hb2 : b * b = 1 := by
      dsimp only [b]
      exact simpleGen_sq P hreg F j
    have hgb : g * b = a := by
      dsimp only [g]
      rw [mul_assoc, hb2, mul_one]
    have ha_pow : a = g ^ (t + 1) := by
      calc
        a = g * b := hgb.symm
        _ = g * g ^ t := by rw [hgtb]
        _ = g ^ (t + 1) := (pow_succ' g t).symm
    have hab_comm : a * b = b * a := by
      have hp := (Commute.pow_pow (Commute.refl g) (t + 1) t).eq
      simpa only [← ha_pow, ← hgtb] using hp
    have hg2mul : g * g = 1 := by
      dsimp only [g]
      calc
        (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab_comm]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
    have hg2 : g ^ 2 = 1 := by simpa only [pow_two] using hg2mul
    have hord_le : orderOf g ≤ 2 :=
      Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one hg2)
    have hmge := coxeterMatrix_adiacente_ge_tre_ovunque P hreg F i hi hn
    change 3 ≤ orderOf g at hmge
    omega

/-- Un passo di `rhoSimple` manda la faccia di rango `i` nell'altra
faccia di rango `i` contenuta nello stesso lato di rango `i+1`. -/
theorem rhoSimple_manda_faccia (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) :
    (⇑(((rhoSimple P hreg F i hi : symGroup P) : Isom n))) '' F.face i =
      (adjacentFlag P hreg.1 F i).face i := by
  let j : Fin n := ⟨(i : ℕ) + 1, hi⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    dsimp only [j] at this
    omega
  calc
    (⇑(((rhoSimple P hreg F i hi : symGroup P) : Isom n))) '' F.face i =
        (⇑(simpleReflection P hreg F i)) ''
          ((⇑(simpleReflection P hreg F j)) '' F.face i) := by
            rw [Set.image_image]
            rfl
    _ = (⇑(simpleReflection P hreg F i)) '' F.face i := by
      rw [simpleReflection_fissa_facce P hreg F j hij]
    _ = (adjacentFlag P hreg.1 F i).face i := by
      have h := congrArg (fun G : P.Flag => G.face i)
        (simpleReflection_mapFlag P hreg F i)
      simpa only [mapFlag_face] using h

/-- Se una faccia dell'orbita di rango `i` resta contenuta nel lato base
di rango `i+1`, allora è una delle due facce incidenti a quel lato. -/
theorem faccia_orbita_nel_lato_e_una_delle_due (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (t : ℕ)
    (hsub : (⇑((((rhoSimple P hreg F i hi) ^ t : symGroup P) : Isom n))) ''
      F.face i ⊆ F.face ⟨(i : ℕ) + 1, hi⟩) :
    (⇑((((rhoSimple P hreg F i hi) ^ t : symGroup P) : Isom n))) ''
        F.face i = F.face i ∨
      (⇑((((rhoSimple P hreg F i hi) ^ t : symGroup P) : Isom n))) ''
        F.face i = (adjacentFlag P hreg.1 F i).face i := by
  let j : Fin n := ⟨(i : ℕ) + 1, hi⟩
  let g : symGroup P := rhoSimple P hreg F i hi
  let φ : Isom n := ((g ^ t : symGroup P) : Isom n)
  let C : Set (E n) := (⇑φ) '' F.face i
  let B : Set (E n) := F.face j
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    dsimp only [j] at this
    omega
  have hφ : P.isSymmetry φ := (g ^ t).property
  have hCface : P.IsFace C := isFace_image_isomN φ hφ (F.isFace i)
  have hdC : faceDim C = (i : ℕ) := by
    dsimp only [C]
    rw [faceDim_image_isomN]
    exact F.dim_eq i
  have hBface : P.IsFace B := F.isFace j
  have hdB : faceDim B = (i : ℕ) + 1 := by
    dsimp only [B, j]
    exact F.dim_eq _
  have hCB : C < B := by
    refine ⟨?_, ?_⟩
    · simpa only [C, B, φ, g, j] using hsub
    · intro hback
      have heq : C = B := Set.Subset.antisymm
        (by simpa only [C, B, φ, g, j] using hsub) hback
      have := congrArg faceDim heq
      rw [hdC, hdB] at this
      omega
  have hFiB : F.face i < B := by
    dsimp only [B]
    exact F.strict_mono i j (by
      rw [Fin.lt_def]
      dsimp only [j]
      omega)
  have hAdjFace : P.IsFace ((adjacentFlag P hreg.1 F i).face i) :=
    (adjacentFlag P hreg.1 F i).isFace i
  have hdAdj : faceDim ((adjacentFlag P hreg.1 F i).face i) = (i : ℕ) :=
    (adjacentFlag P hreg.1 F i).dim_eq i
  have hAdjNe : (adjacentFlag P hreg.1 F i).face i ≠ F.face i :=
    (adjacentFlag_isAdjacent P hreg.1 F i).2
  have hAdjB : (adjacentFlag P hreg.1 F i).face i < B := by
    have hs := (adjacentFlag P hreg.1 F i).strict_mono i j (by
      rw [Fin.lt_def]
      dsimp only [j]
      omega)
    have hjface := (adjacentFlag_isAdjacent P hreg.1 F i).1 j hij.symm
    dsimp only [B]
    rwa [hjface] at hs
  by_cases hCeq : C = F.face i
  · exact Or.inl (by simpa only [C, φ, g] using hCeq)
  · refine Or.inr ?_
    have hCAdj : C = (adjacentFlag P hreg.1 F i).face i := by
      by_cases hi0 : (i : ℕ) = 0
      · obtain ⟨W, hW, huniq⟩ := due_vertici_per_spigolo P hBface
          (by simpa only [B] using hdB.trans (by omega : (i : ℕ) + 1 = 1))
          (F.isFace i) (by simpa [hi0] using F.dim_eq i) hFiB
        have hCW : C = W := huniq C
          ⟨⟨hCface, by simpa [hi0] using hdC, hCB⟩, hCeq⟩
        have hAdjW : (adjacentFlag P hreg.1 F i).face i = W := huniq _
          ⟨⟨hAdjFace, by simpa [hi0] using hdAdj, hAdjB⟩, hAdjNe⟩
        exact hCW.trans hAdjW.symm
      · let im : Fin n := ⟨(i : ℕ) - 1, by omega⟩
        have himi : im < i := by
          rw [Fin.lt_def]
          dsimp only [im]
          omega
        have him_ne_i : im ≠ i := ne_of_lt himi
        have him_ne_j : im ≠ j := ne_of_lt (lt_trans himi (by
          rw [Fin.lt_def]
          dsimp only [j]
          omega))
        have hAim : (⇑φ) '' F.face im = F.face im := by
          simpa only [φ, g] using
            rhoSimple_pow_fissa_faccia P hreg F i hi im him_ne_i him_ne_j t
        have hAsubC : F.face im ⊆ C := by
          rw [← hAim]
          exact Set.image_mono (F.strict_mono im i himi).le
        have hAC : F.face im < C := by
          refine ⟨hAsubC, ?_⟩
          intro hback
          have heq : F.face im = C := Set.Subset.antisymm hAsubC hback
          have hdim := congrArg faceDim heq
          rw [F.dim_eq im, hdC] at hdim
          dsimp only [im] at hdim
          omega
        have hrank : faceDim B = faceDim (F.face im) + 2 := by
          rw [hdB, F.dim_eq im]
          dsimp only [im]
          omega
        have hAAdj : F.face im < (adjacentFlag P hreg.1 F i).face i := by
          have hs := (adjacentFlag P hreg.1 F i).strict_mono im i himi
          have hface := (adjacentFlag_isAdjacent P hreg.1 F i).1 im him_ne_i
          rwa [hface] at hs
        obtain ⟨W, hW, huniq⟩ := existsUnique_other_middle P
          (F.isFace im) hBface hrank (F.isFace i)
          (F.strict_mono im i himi) hFiB
        have hCW : C = W := huniq C ⟨⟨hCface, hAC, hCB⟩, hCeq⟩
        have hAdjW : (adjacentFlag P hreg.1 F i).face i = W :=
          huniq _ ⟨⟨hAdjFace, hAAdj, hAdjB⟩, hAdjNe⟩
        exact hCW.trans hAdjW.symm
    simpa only [C, φ, g] using hCAdj

/-- Se la potenza manda la faccia base nella faccia del primo passo,
l'esponente meno uno è multiplo dell'ordine di Coxeter. -/
theorem rhoSimple_pow_manda_faccia_dvd_pred (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hn : 3 ≤ n) (t : ℕ) (ht : 1 ≤ t)
    (hface : (⇑((((rhoSimple P hreg F i hi) ^ t : symGroup P) : Isom n))) ''
      F.face i = (adjacentFlag P hreg.1 F i).face i) :
    coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ ∣ t - 1 := by
  let g : symGroup P := rhoSimple P hreg F i hi
  have ht_eq : t = (t - 1) + 1 := by omega
  have hpow : g ^ t = g * g ^ (t - 1) := by
    calc
      g ^ t = g ^ ((t - 1) + 1) := congrArg (fun q : ℕ => g ^ q) ht_eq
      _ = g * g ^ (t - 1) := pow_succ' g (t - 1)
  have hleft :
      (⇑((g : symGroup P) : Isom n)) ''
          ((⇑(((g ^ (t - 1) : symGroup P) : Isom n))) '' F.face i) =
        (adjacentFlag P hreg.1 F i).face i := by
    calc
      (⇑((g : symGroup P) : Isom n)) ''
          ((⇑(((g ^ (t - 1) : symGroup P) : Isom n))) '' F.face i) =
          (⇑(((g ^ t : symGroup P) : Isom n))) '' F.face i := by
            rw [hpow, Set.image_image]
            rfl
      _ = (adjacentFlag P hreg.1 F i).face i := by
        simpa only [g] using hface
  have hright : (⇑((g : symGroup P) : Isom n)) '' F.face i =
      (adjacentFlag P hreg.1 F i).face i := by
    simpa only [g] using rhoSimple_manda_faccia P hreg F i hi
  have hfix :
      (⇑(((g ^ (t - 1) : symGroup P) : Isom n))) '' F.face i = F.face i :=
    (Set.image_injective.mpr (((g : symGroup P) : Isom n).injective))
      (hleft.trans hright.symm)
  apply rhoSimple_pow_stabilizza_faccia_dvd P hreg F i hi hn (t - 1)
  simpa only [g] using hfix

/-! ## Espositore separante dell'orbita -/

/-- L'espositore della faccia di rango `i+1` ha i primi due valori
uguali e separa strettamente tutti gli altri punti dell'orbita ciclica. -/
theorem esiste_espositore_separante (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hn : 3 ≤ n) :
    ∃ l : E n →L[ℝ] ℝ,
      l (centroideFaccia P (F.face i)) =
        l (centroideFaccia P ((adjacentFlag P hreg.1 F i).face i)) ∧
      ∀ t : ℕ, 2 ≤ t →
        t ≤ coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ - 1 →
        l (((((rhoSimple P hreg F i hi) ^ t : symGroup P) : Isom n)
            (centroideFaccia P (F.face i)))) <
          l (centroideFaccia P (F.face i)) := by
  let j : Fin n := ⟨(i : ℕ) + 1, hi⟩
  let B : Set (E n) := F.face j
  obtain ⟨l, hmem, hchar⟩ := espositore_di_faccia P (F.isFace j)
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    dsimp only [j] at this
    omega
  have hFiB : F.face i ⊆ B := by
    dsimp only [B]
    exact (F.strict_mono i j (by
      rw [Fin.lt_def]
      dsimp only [j]
      omega)).le
  have hAdjB : (adjacentFlag P hreg.1 F i).face i ⊆ B := by
    have hs := (adjacentFlag P hreg.1 F i).strict_mono i j (by
      rw [Fin.lt_def]
      dsimp only [j]
      omega)
    have hjface := (adjacentFlag_isAdjacent P hreg.1 F i).1 j hij.symm
    dsimp only [B]
    rw [hjface] at hs
    exact hs.le
  have hc₁mem : centroideFaccia P (F.face i) ∈ B :=
    hFiB (centroide_mem_faccia P (F.isFace i))
  have hc₂mem : centroideFaccia P
      ((adjacentFlag P hreg.1 F i).face i) ∈ B :=
    hAdjB (centroide_mem_faccia P
      ((adjacentFlag P hreg.1 F i).isFace i))
  have hconst : ∀ {x y : E n}, x ∈ B → y ∈ B → l x = l y := by
    intro x y hx hy
    exact le_antisymm ((hmem y hy).2 x (hmem x hx).1)
      ((hmem x hx).2 y (hmem y hy).1)
  refine ⟨l, hconst hc₁mem hc₂mem, ?_⟩
  intro t ht2 htupper
  let g : symGroup P := rhoSimple P hreg F i hi
  let φ : Isom n := ((g ^ t : symGroup P) : Isom n)
  let C : Set (E n) := (⇑φ) '' F.face i
  have hφ : P.isSymmetry φ := (g ^ t).property
  have hCface : P.IsFace C := isFace_image_isomN φ hφ (F.isFace i)
  have hnotSub : ¬ C ⊆ B := by
    intro hCB
    have hcases := faccia_orbita_nel_lato_e_una_delle_due
      P hreg F i hi t (by simpa only [C, B, φ, g, j] using hCB)
    rcases hcases with hbase | hnext
    · have hdvd := rhoSimple_pow_stabilizza_faccia_dvd
        P hreg F i hi hn t hbase
      have hmle : coxeterMatrix P hreg F i j ≤ t :=
        Nat.le_of_dvd (by omega) (by simpa only [j] using hdvd)
      dsimp only [j] at hmle
      omega
    · have hdvd := rhoSimple_pow_manda_faccia_dvd_pred
        P hreg F i hi hn t (by omega) hnext
      have hmle : coxeterMatrix P hreg F i j ≤ t - 1 :=
        Nat.le_of_dvd (by omega) (by simpa only [j] using hdvd)
      dsimp only [j] at hmle
      omega
  have hcCmem : centroideFaccia P C ∈ C := centroide_mem_faccia P hCface
  have hcCP : centroideFaccia P C ∈ P.toSet :=
    face_subset_toSet P hCface hcCmem
  have hmapc : φ (centroideFaccia P (F.face i)) = centroideFaccia P C := by
    exact centroide_di_faccia_mandato P hφ (F.isFace i) hCface rfl
  have hle : l (centroideFaccia P C) ≤ l (centroideFaccia P (F.face i)) :=
    (hmem (centroideFaccia P (F.face i)) hc₁mem).2 _ hcCP
  have hlt : l (centroideFaccia P C) < l (centroideFaccia P (F.face i)) := by
    rcases lt_or_eq_of_le hle with h | heq
    · exact h
    · exfalso
      have hcCB : centroideFaccia P C ∈ B := by
        apply hchar (centroideFaccia P C) hcCP
        intro z hz
        have hzle := (hmem (centroideFaccia P (F.face i)) hc₁mem).2 z hz
        rwa [← heq] at hzle
      have hDface : P.IsFace (C ∩ B) :=
        ⟨hCface.1.inter (F.isFace j).1, ⟨centroideFaccia P C, hcCmem, hcCB⟩⟩
      have hDC : C ∩ B < C := by
        refine ⟨Set.inter_subset_left, ?_⟩
        intro hback
        apply hnotSub
        intro x hx
        exact (hback hx).2
      have hout := centroide_fuori_da_span_sottofaccia P hDface hCface hDC
      exact hout (subset_affineSpan ℝ (C ∩ B) ⟨hcCmem, hcCB⟩)
  simpa only [φ, g] using hmapc.symm ▸ hlt

/-! ## Dal funzionale al vettore del residuo -/

/-- Vettore di Riesz della restrizione di un funzionale al sottospazio `V`. -/
noncomputable def rieszResiduo (V : Submodule ℝ (E n))
    (l : E n →L[ℝ] ℝ) : V :=
  (InnerProductSpace.toDual ℝ V).symm (l.comp V.subtypeL)

theorem rieszResiduo_spec (V : Submodule ℝ (E n))
    (l : E n →L[ℝ] ℝ) (z : V) :
    ⟪(rieszResiduo V l : E n), (z : E n)⟫ = l (z : E n) := by
  change ⟪rieszResiduo V l, z⟫ = l (z : E n)
  rw [rieszResiduo, InnerProductSpace.toDual_symm_apply]
  rfl

/-- Facce distinte della stessa dimensione hanno centroidi distinti. -/
theorem centroidi_facce_distinte (P : ConvexPolytope n)
    {f g : Set (E n)} (hf : P.IsFace f) (hg : P.IsFace g)
    (hdim : faceDim f = faceDim g) (hne : f ≠ g) :
    centroideFaccia P f ≠ centroideFaccia P g := by
  intro hc
  have hcf : centroideFaccia P f ∈ f := centroide_mem_faccia P hf
  have hcg : centroideFaccia P g ∈ g := centroide_mem_faccia P hg
  have hcfg : centroideFaccia P f ∈ f ∩ g := ⟨hcf, by simpa [hc] using hcg⟩
  have hDface : P.IsFace (f ∩ g) := ⟨hf.1.inter hg.1, ⟨_, hcfg⟩⟩
  have hDproper : f ∩ g < f := by
    refine ⟨Set.inter_subset_left, ?_⟩
    intro hback
    have hfg : f ⊆ g := fun x hx => (hback hx).2
    have hstrict : f < g :=
      ⟨hfg, fun hgf => hne (Set.Subset.antisymm hfg hgf)⟩
    have hlt := faceDim_lt_of_ssubset P hf hg hstrict
    omega
  have hout := centroide_fuori_da_span_sottofaccia P hDface hf hDproper
  exact hout (subset_affineSpan ℝ (f ∩ g) hcfg)

/-- L'ortogonalità richiesta dal mezzo passo è la forma bilineare
dell'uguaglianza dei primi due valori. -/
theorem perp_del_lato (V : Submodule ℝ (E n)) (O c₁ cnext : E n)
    (R : V ≃ₗᵢ[ℝ] V)
    (heq : ⟪(vettoreProiettato V O cnext : E n),
        ((R (vettoreProiettato V O c₁) : V) : E n)⟫ =
      ⟪(vettoreProiettato V O cnext : E n),
        (vettoreProiettato V O c₁ : E n)⟫) :
    ⟪(vettoreProiettato V O cnext : E n),
      (vettoreProiettato V O c₁ : E n) -
        ((R (vettoreProiettato V O c₁) : V) : E n)⟫ = 0 := by
  rw [inner_sub_right, heq]
  ring

/-- Trasferimento dei valori di un espositore affine all'orbita della
restrizione lineare sul piano dei due normali. -/
theorem trasferisci_espositore_al_residuo (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n)
    {αi pi αj pj : E n}
    (hri : ∀ x, simpleReflection P hreg F i x =
      x - (2 * ⟪αi, x - pi⟫ : ℝ) • αi)
    (hrj : ∀ x, simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ x =
      x - (2 * ⟪αj, x - pj⟫ : ℝ) • αj)
    (V : Submodule ℝ (E n))
    (hVspan : V = Submodule.span ℝ ({αi, αj} : Set (E n)))
    (R : V ≃ₗᵢ[ℝ] V)
    (hR : ∀ y : V, ((R y : V) : E n) =
      rhoLineare P hreg F i hi (y : E n))
    (l : E n →L[ℝ] ℝ)
    (horbitEq : l ((((rhoSimple P hreg F i hi : symGroup P) : Isom n)
        (centroideFaccia P (F.face i)))) =
      l (centroideFaccia P (F.face i)))
    (horbitLt : ∀ t : ℕ, 2 ≤ t →
      t ≤ coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ - 1 →
      l (((((rhoSimple P hreg F i hi) ^ t : symGroup P) : Isom n)
          (centroideFaccia P (F.face i)))) <
        l (centroideFaccia P (F.face i))) :
    let v := vettoreProiettato V (centroGlobale P)
      (centroideFaccia P (F.face i))
    let w := rieszResiduo V l
    ⟪(w : E n), ((R v : V) : E n)⟫ = ⟪(w : E n), (v : E n)⟫ ∧
      ∀ t : ℕ, 2 ≤ t →
        t ≤ coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ - 1 →
        ⟪(w : E n), (((R ^ t) v : V) : E n)⟫ <
          ⟪(w : E n), (v : E n)⟫ := by
  dsimp only
  let O : E n := centroGlobale P
  let c : E n := centroideFaccia P (F.face i)
  let v : V := vettoreProiettato V O c
  let w : V := rieszResiduo V l
  let S : E n ≃ₗᵢ[ℝ] E n := rhoLineare P hreg F i hi
  let g : symGroup P := rhoSimple P hreg F i hi
  have hαiV : αi ∈ V := by
    rw [hVspan]
    exact Submodule.subset_span (by simp)
  have hαjV : αj ∈ V := by
    rw [hVspan]
    exact Submodule.subset_span (by simp)
  let z : E n := (c - O) - (v : E n)
  have hz : z ∈ Vᗮ := by
    dsimp only [z, v, vettoreProiettato]
    exact V.sub_starProjection_mem_orthogonal (c - O)
  have hαiz : ⟪αi, z⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hαiV hz
  have hαjz : ⟪αj, z⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hαjV hz
  have hSz : S z = z := by
    rw [rhoLineare_formula P hreg F i hi hri hrj]
    simp [hαiz, hαjz]
  have hSpowz : ∀ t : ℕ, (S ^ t) z = z := by
    intro t
    induction t with
    | zero => simp
    | succ t iht =>
        rw [pow_succ]
        change (S ^ t) (S z) = z
        rw [hSz, iht]
  have hRpow : ∀ t : ℕ, ∀ y : V,
      ((((R ^ t) y : V) : E n)) = (S ^ t) (y : E n) := by
    intro t
    induction t with
    | zero => intro y; simp
    | succ t iht =>
        intro y
        rw [pow_succ, pow_succ]
        change ((((R ^ t) (R y) : V) : E n)) = (S ^ t) (S (y : E n))
        rw [iht, hR]
  have hlinpow : ∀ t : ℕ,
      ((((g ^ t : symGroup P) : Isom n)).linearIsometryEquiv) = S ^ t := by
    intro t
    induction t with
    | zero => rfl
    | succ t iht =>
        rw [pow_succ, pow_succ]
        change ((((g ^ t : symGroup P) : Isom n)).linearIsometryEquiv) *
            (((g : symGroup P) : Isom n)).linearIsometryEquiv = S ^ t * S
        rw [iht]
        rfl
  have hOi : simpleReflection P hreg F i O = O := by
    exact centro_fisso P hreg (simpleReflection_isSymmetry P hreg F i)
  have hOj : simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ O = O := by
    exact centro_fisso P hreg
      (simpleReflection_isSymmetry P hreg F ⟨(i : ℕ) + 1, hi⟩)
  have hgO : ((g : symGroup P) : Isom n) O = O := by
    change simpleReflection P hreg F i
      (simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ O) = O
    rw [hOj, hOi]
  have hgpO : ∀ t : ℕ, (((g ^ t : symGroup P) : Isom n) O) = O := by
    intro t
    induction t with
    | zero => simp
    | succ t iht =>
        rw [pow_succ]
        change (((g ^ t : symGroup P) : Isom n)
          (((g : symGroup P) : Isom n) O)) = O
        rw [hgO, iht]
  have horbit : ∀ t : ℕ,
      (((g ^ t : symGroup P) : Isom n) c) - O = (S ^ t) (c - O) := by
    intro t
    have hmv := (((g ^ t : symGroup P) : Isom n)).map_vsub c O
    rw [hlinpow, hgpO] at hmv
    simpa only [vsub_eq_sub] using hmv.symm
  have hdecomp : c - O = (v : E n) + z := by
    dsimp only [z]
    abel
  have hdiff : ∀ t : ℕ,
      (((g ^ t : symGroup P) : Isom n) c) - c =
        (S ^ t) (v : E n) - (v : E n) := by
    intro t
    have ht := horbit t
    rw [hdecomp, map_add, hSpowz] at ht
    calc
      (((g ^ t : symGroup P) : Isom n) c) - c =
          ((((g ^ t : symGroup P) : Isom n) c) - O) - (c - O) := by abel
      _ = ((S ^ t) (v : E n) + z) - ((v : E n) + z) := by
        rw [ht, hdecomp]
      _ = (S ^ t) (v : E n) - (v : E n) := by abel
  have hvalue : ∀ t : ℕ,
      l (((g ^ t : symGroup P) : Isom n) c) - l c =
        l ((S ^ t) (v : E n)) - l (v : E n) := by
    intro t
    rw [← map_sub, ← map_sub, hdiff]
  have hinner : ∀ t : ℕ,
      ⟪(w : E n), (((R ^ t) v : V) : E n)⟫ =
        l ((S ^ t) (v : E n)) := by
    intro t
    rw [rieszResiduo_spec V l ((R ^ t) v), hRpow]
  have hinner0 : ⟪(w : E n), (v : E n)⟫ = l (v : E n) :=
    rieszResiduo_spec V l v
  constructor
  · have hv1 := hvalue 1
    have heq : l ((S ^ 1) (v : E n)) = l (v : E n) := by
      have horbitEq' : l (((g ^ 1 : symGroup P) : Isom n) c) = l c := by
        simpa only [pow_one, g, c] using horbitEq
      linarith
    rw [hinner0, rieszResiduo_spec V l (R v), hR]
    simpa only [pow_one] using heq
  · intro t ht2 htupper
    have hv := hvalue t
    have hlt := horbitLt t ht2 htupper
    have hlt' : l (((g ^ t : symGroup P) : Isom n) c) < l c := by
      simpa only [g, c] using hlt
    rw [hinner t, hinner0]
    linarith

/-! ## Assemblaggio -/

/-- Tutti i dati del mezzo passo, costruiti dalla restrizione canonica e
dal vettore di Riesz dell'espositore del lato di rango `i+1`. -/
theorem esiste_dati_mezzo_passo (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hn : 3 ≤ n)
    {αi pi αj pj : E n} (hαi : ‖αi‖ = 1) (hαj : ‖αj‖ = 1)
    (hri : ∀ x, simpleReflection P hreg F i x =
      x - (2 * ⟪αi, x - pi⟫ : ℝ) • αi)
    (hrj : ∀ x, simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ x =
      x - (2 * ⟪αj, x - pj⟫ : ℝ) • αj) :
    Nonempty (DatiMezzoPasso P hreg F i hi αi αj) := by
  let j : Fin n := ⟨(i : ℕ) + 1, hi⟩
  let O : E n := centroGlobale P
  let c : E n := centroideFaccia P (F.face i)
  let c₂ : E n := centroideFaccia P ((adjacentFlag P hreg.1 F i).face i)
  let V : Submodule ℝ (E n) := Submodule.span ℝ ({αi, αj} : Set (E n))
  have hVspan : V = Submodule.span ℝ ({αi, αj} : Set (E n)) := rfl
  have hαiV : αi ∈ V := Submodule.subset_span (by simp)
  have hαjV : αj ∈ V := Submodule.subset_span (by simp)
  have hOi : simpleReflection P hreg F i O = O := by
    exact centro_fisso P hreg (simpleReflection_isSymmetry P hreg F i)
  have hOj : simpleReflection P hreg F j O = O := by
    exact centro_fisso P hreg (simpleReflection_isSymmetry P hreg F j)
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    dsimp only [j] at this
    omega
  have hcfixj : simpleReflection P hreg F j c = c := by
    dsimp only [c]
    exact centroide_di_faccia_fissato P
      (simpleReflection_isSymmetry P hreg F j) (F.isFace i)
      (simpleReflection_fissa_facce P hreg F j hij)
  have hc₂ne : c₂ ≠ c := by
    dsimp only [c₂, c]
    exact (centroidi_facce_distinte P
      ((adjacentFlag P hreg.1 F i).isFace i) (F.isFace i)
      (by rw [(adjacentFlag P hreg.1 F i).dim_eq, F.dim_eq])
      (adjacentFlag_isAdjacent P hreg.1 F i).2)
  have hric : simpleReflection P hreg F i c = c₂ := by
    have h := orbita_passo_combinatorio P hreg F i hi
    change simpleReflection P hreg F i
        (simpleReflection P hreg F j c) = c₂ at h
    rwa [hcfixj] at h
  have hcmovei : simpleReflection P hreg F i c ≠ c := by
    rw [hric]
    exact hc₂ne
  obtain ⟨R, hord, hR⟩ :=
    esiste_restrizione P hreg F i hi hαi hαj hri hrj V hVspan
  obtain ⟨l, heql, hltl⟩ :=
    esiste_espositore_separante P hreg F i hi hn
  have horbitEq : l (((rhoSimple P hreg F i hi : symGroup P) : Isom n) c) =
      l c := by
    have hstep := orbita_passo_combinatorio P hreg F i hi
    change (((rhoSimple P hreg F i hi : symGroup P) : Isom n) c) = c₂ at hstep
    rw [hstep]
    exact heql.symm
  have horbitLt : ∀ t : ℕ, 2 ≤ t →
      t ≤ coxeterMatrix P hreg F i j - 1 →
      l ((((rhoSimple P hreg F i hi) ^ t : symGroup P) : Isom n) c) < l c := by
    intro t ht2 htupper
    exact hltl t ht2 (by simpa only [j] using htupper)
  have hlαi : l αi = 0 := by
    have hlri := congrArg l (hri c)
    have hleq : l (simpleReflection P hreg F i c) = l c := by
      rw [hric]
      exact heql.symm
    simp only [map_sub, map_smul, smul_eq_mul] at hlri
    have hcoeff : (2 * ⟪αi, c - pi⟫ : ℝ) ≠ 0 := by
      intro hz
      apply hcmovei
      rw [hri c, hz, zero_smul, sub_zero]
    have hprod : (2 * ⟪αi, c - pi⟫ : ℝ) * l αi = 0 := by
      linarith
    exact (mul_eq_zero.mp hprod).resolve_left hcoeff
  have hlαj : l αj ≠ 0 := by
    intro hzj
    have hlinvi : ∀ x : E n, l (simpleReflection P hreg F i x) = l x := by
      intro x
      rw [hri x, map_sub, map_smul, hlαi, smul_eq_mul, mul_zero, sub_zero]
    have hlinvj : ∀ x : E n, l (simpleReflection P hreg F j x) = l x := by
      intro x
      rw [hrj x, map_sub, map_smul, hzj, smul_eq_mul, mul_zero, sub_zero]
    have hm := coxeterMatrix_adiacente_ge_tre_ovunque P hreg F i hi hn
    have h2 := horbitLt 2 (by omega) (by
      dsimp only [j]
      omega)
    change l (simpleReflection P hreg F i
      (simpleReflection P hreg F j
        (simpleReflection P hreg F i
          (simpleReflection P hreg F j c)))) < l c at h2
    rw [hlinvi, hlinvj, hlinvi, hlinvj] at h2
    exact (lt_irrefl _ h2)
  let v : V := vettoreProiettato V O c
  let w : V := rieszResiduo V l
  let c₁ : E n := O + (v : E n)
  let cnext : E n := O + (w : E n)
  have hc₁fixj : simpleReflection P hreg F j c₁ = c₁ := by
    dsimp only [c₁, v, O, c, j]
    exact proiettato_fissato_da_formula hαj hrj hαjV hOj hcfixj
  have hc₁movei : simpleReflection P hreg F i c₁ ≠ c₁ := by
    dsimp only [c₁, v, O, c]
    exact proiettato_non_fissato_da_formula hαi hri hαiV hOi hcmovei
  have hOinneri : ⟪αi, O - pi⟫ = 0 := by
    have h := hOi
    rw [hri O] at h
    have hs : (2 * ⟪αi, O - pi⟫ : ℝ) • αi = 0 := sub_eq_self.mp h
    have hαine : αi ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hαi
      norm_num at hαi
    have : (2 * ⟪αi, O - pi⟫ : ℝ) = 0 :=
      (smul_eq_zero.mp hs).resolve_right hαine
    linarith
  have hOinnerj : ⟪αj, O - pj⟫ = 0 := by
    have h := hOj
    rw [hrj O] at h
    have hs : (2 * ⟪αj, O - pj⟫ : ℝ) • αj = 0 := sub_eq_self.mp h
    have hαjne : αj ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hαj
      norm_num at hαj
    have : (2 * ⟪αj, O - pj⟫ : ℝ) = 0 :=
      (smul_eq_zero.mp hs).resolve_right hαjne
    linarith
  have hinneriw : ⟪αi, (w : E n)⟫ = 0 := by
    rw [real_inner_comm]
    simpa only [w, hlαi] using rieszResiduo_spec V l ⟨αi, hαiV⟩
  have hinnerjw : ⟪αj, (w : E n)⟫ ≠ 0 := by
    rw [real_inner_comm]
    change ⟪(rieszResiduo V l : E n), αj⟫ ≠ 0
    rw [show ⟪(rieszResiduo V l : E n), αj⟫ = l αj from
      rieszResiduo_spec V l ⟨αj, hαjV⟩]
    exact hlαj
  have hcnextfixi : simpleReflection P hreg F i cnext = cnext := by
    rw [hri]
    have hz : ⟪αi, cnext - pi⟫ = 0 := by
      dsimp only [cnext]
      rw [show O + (w : E n) - pi = (O - pi) + (w : E n) by abel,
        inner_add_right, hOinneri, hinneriw, zero_add]
    rw [hz, mul_zero, zero_smul, sub_zero]
  have hcnextmovej : simpleReflection P hreg F j cnext ≠ cnext := by
    intro hfix
    rw [hrj] at hfix
    have hs : (2 * ⟪αj, cnext - pj⟫ : ℝ) • αj = 0 := sub_eq_self.mp hfix
    have hαjne : αj ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hαj
      norm_num at hαj
    have hscalar : (2 * ⟪αj, cnext - pj⟫ : ℝ) = 0 :=
      (smul_eq_zero.mp hs).resolve_right hαjne
    apply hinnerjw
    have htotal : ⟪αj, cnext - pj⟫ = ⟪αj, (w : E n)⟫ := by
      dsimp only [cnext]
      rw [show O + (w : E n) - pj = (O - pj) + (w : E n) by abel,
        inner_add_right, hOinnerj, zero_add]
    rw [← htotal]
    linarith
  have htrans := trasferisci_espositore_al_residuo P hreg F i hi hri hrj
    V hVspan R hR l horbitEq (by
      intro t ht2 htupper
      exact horbitLt t ht2 (by simpa only [j] using htupper))
  change ⟪(w : E n), ((R v : V) : E n)⟫ = ⟪(w : E n), (v : E n)⟫ ∧
      (∀ t : ℕ, 2 ≤ t →
        t ≤ coxeterMatrix P hreg F i j - 1 →
        ⟪(w : E n), (((R ^ t) v : V) : E n)⟫ <
          ⟪(w : E n), (v : E n)⟫) at htrans
  obtain ⟨heq, hlt⟩ := htrans
  have hproj₁ : vettoreProiettato V O c₁ = v := by
    dsimp only [c₁, vettoreProiettato]
    rw [add_sub_cancel_left]
    exact V.orthogonalProjectionOnto_mem_subspace_eq_self v
  have hprojnext : vettoreProiettato V O cnext = w := by
    dsimp only [cnext, vettoreProiettato]
    rw [add_sub_cancel_left]
    exact V.orthogonalProjectionOnto_mem_subspace_eq_self w
  have hperp := perp_del_lato V O c₁ cnext R (by
    rw [hproj₁, hprojnext]
    exact heq)
  exact ⟨{
    c₁ := c₁
    cnext := cnext
    V := V
    hVspan := hVspan
    hc₁_fisso_j := by simpa only [j] using hc₁fixj
    hc₁_mosso_i := hc₁movei
    hcnext_fisso_i := hcnextfixi
    hcnext_mosso_j := by simpa only [j] using hcnextmovej
    R := R
    hord := hord
    heq := by simpa only [O, hproj₁, hprojnext] using heq
    hlt := by
      intro t ht2 htupper
      rw [hproj₁, hprojnext]
      exact hlt t ht2 (by simpa only [j] using htupper)
    hperp := by simpa only [O] using hperp
  }⟩

/-- Versione incondizionata del collasso elementare: il pacchetto
`DatiMezzoPasso` è ora costruito internamente. -/
theorem rotazione_elementare_incondizionata (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hn : 3 ≤ n)
    {αi pi αj pj : E n} (hαi : ‖αi‖ = 1) (hαj : ‖αj‖ = 1)
    (hri : ∀ x, simpleReflection P hreg F i x =
      x - (2 * ⟪αi, x - pi⟫ : ℝ) • αi)
    (hrj : ∀ x, simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ x =
      x - (2 * ⟪αj, x - pj⟫ : ℝ) • αj) :
    |(⟪αi, αj⟫ : ℝ)| =
      Real.cos (Real.pi /
        (coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ : ℝ)) := by
  obtain ⟨d⟩ := esiste_dati_mezzo_passo P hreg F i hi hn
    hαi hαj hri hrj
  exact rotazione_elementare P hreg F i hi hn hαi hαj hri hrj d

/-- Versione incondizionata della voce sottodiagonale della matrice di
Gram, con orientazione coerente dei due normali. -/
theorem gram_sottodiagonale_incondizionata (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hn : 3 ≤ n) :
    ∃ αi αj : E n, ‖αi‖ = 1 ∧ ‖αj‖ = 1 ∧
      ⟪αi, αj⟫ = -Real.cos (Real.pi /
        (coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ : ℝ)) := by
  apply gram_sottodiagonale P hreg F i hi hn
  intro αi pi αj pj hαi hαj hri hrj
  exact (esiste_dati_mezzo_passo P hreg F i hi hn
    hαi hαj hri hrj).some

end LeanEval.Geometry.PlatonicClassification
