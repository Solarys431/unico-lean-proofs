import Mathlib
import Solution.GramDalFan
import Solution.Balinski
import Solution.BandieraSpigolo
import Solution.LatoSemipiano

open Set Real InnerProductGeometry
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope PlatoniciA13

theorem relazioni_trasportate_da_gram
    {m : ℕ} {u w : Fin m → E 3}
    (hgram : ∀ i j, ⟪u i, u j⟫ = ⟪w i, w j⟫)
    (a : Fin m → ℝ) (h : ∑ i, a i • u i = 0) :
    ∑ i, a i • w i = 0 := by
  classical
  have hinter :
      ⟪∑ i, a i • w i, ∑ j, a j • w j⟫ =
        ⟪∑ i, a i • u i, ∑ j, a j • u j⟫ := by
    simp_rw [sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right, ← hgram]
  have hnorm : ‖∑ i, a i • w i‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, hinter, h]
    simp
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

theorem inner_somme_da_gram
    {m : ℕ} {u w : Fin m → E 3}
    (hgram : ∀ i j, ⟪u i, u j⟫ = ⟪w i, w j⟫)
    (a b : Fin m → ℝ) :
    ⟪∑ i, a i • w i, ∑ j, b j • w j⟫ =
      ⟪∑ i, a i • u i, ∑ j, b j • u j⟫ := by
  classical
  simp_rw [sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, ← hgram]

theorem span_trasportato_da_gram
    {m : ℕ} {u w : Fin m → E 3}
    (hspanU : Submodule.span ℝ (Set.range u) = ⊤)
    (hgram : ∀ i j, ⟪u i, u j⟫ = ⟪w i, w j⟫) :
    Submodule.span ℝ (Set.range w) = ⊤ := by
  classical
  let lu : (Fin m → ℝ) →ₗ[ℝ] E 3 := Fintype.linearCombination ℝ u
  let lw : (Fin m → ℝ) →ₗ[ℝ] E 3 := Fintype.linearCombination ℝ w
  have hker : LinearMap.ker lu = LinearMap.ker lw := by
    ext a
    simp only [LinearMap.mem_ker]
    constructor
    · intro ha
      apply relazioni_trasportate_da_gram hgram a
      simpa only [lu, Fintype.linearCombination_apply] using ha
    · intro ha
      apply relazioni_trasportate_da_gram (fun i j => (hgram i j).symm) a
      simpa only [lw, Fintype.linearCombination_apply] using ha
  have hru := lu.finrank_range_add_finrank_ker
  have hrw := lw.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ lu.range = Module.finrank ℝ lw.range := by
    rw [hker] at hru
    omega
  have htopU : LinearMap.range lu = ⊤ := by
    simpa only [lu, Fintype.range_linearCombination] using hspanU
  have hfinW : Module.finrank ℝ lw.range = Module.finrank ℝ (E 3) := by
    rw [← hrange, htopU]
    simp
  have htopW : LinearMap.range lw = ⊤ :=
    Submodule.eq_top_of_finrank_eq hfinW
  simpa only [lw, Fintype.range_linearCombination] using htopW

theorem isometria_da_gram
    {m : ℕ} {u w : Fin m → E 3}
    (hspanU : Submodule.span ℝ (Set.range u) = ⊤)
    (hspanW : Submodule.span ℝ (Set.range w) = ⊤)
    (hgram : ∀ i j, ⟪u i, u j⟫ = ⟪w i, w j⟫) :
    ∃ L : E 3 ≃ₗᵢ[ℝ] E 3, ∀ i, L (u i) = w i := by
  classical
  let lu : (Fin m → ℝ) →ₗ[ℝ] E 3 := Fintype.linearCombination ℝ u
  let lw : (Fin m → ℝ) →ₗ[ℝ] E 3 := Fintype.linearCombination ℝ w
  have hker : LinearMap.ker lu = LinearMap.ker lw := by
    ext a
    simp only [LinearMap.mem_ker]
    constructor
    · intro ha
      apply relazioni_trasportate_da_gram hgram a
      simpa only [lu, Fintype.linearCombination_apply] using ha
    · intro ha
      apply relazioni_trasportate_da_gram (fun i j => (hgram i j).symm) a
      simpa only [lw, Fintype.linearCombination_apply] using ha
  have hsurjU : Function.Surjective lu := by
    exact (span_range_eq_top_iff_surjective_fintypeLinearCombination ℝ u).mp hspanU
  have hsurjW : Function.Surjective lw := by
    exact (span_range_eq_top_iff_surjective_fintypeLinearCombination ℝ w).mp hspanW
  let eu := LinearMap.quotKerEquivOfSurjective lu hsurjU
  let ew := LinearMap.quotKerEquivOfSurjective lw hsurjW
  let eqker := Submodule.quotEquivOfEq (LinearMap.ker lu) (LinearMap.ker lw) hker
  let e : E 3 ≃ₗ[ℝ] E 3 := eu.symm.trans (eqker.trans ew)
  have he_total : ∀ a : Fin m → ℝ, e (lu a) = lw a := by
    intro a
    simp [e, eu, ew, eqker]
  have he_inner : ∀ x y : E 3, ⟪e x, e y⟫ = ⟪x, y⟫ := by
    intro x y
    obtain ⟨a, rfl⟩ := hsurjU x
    obtain ⟨b, rfl⟩ := hsurjU y
    rw [he_total, he_total]
    exact inner_somme_da_gram hgram a b
  let L : E 3 ≃ₗᵢ[ℝ] E 3 := e.isometryOfInner he_inner
  refine ⟨L, ?_⟩
  intro i
  let a : Fin m → ℝ := Pi.single i 1
  have hua : lu a = u i := by
    simp [lu, a, Fintype.linearCombination_apply]
  have hwa : lw a = w i := by
    simp [lw, a, Fintype.linearCombination_apply]
  change e (u i) = w i
  rw [← hua, he_total, hwa]

theorem isometria_al_vertice
    {m : ℕ} {v v' : E 3} {u w : Fin m → E 3}
    (hspanU : Submodule.span ℝ (Set.range u) = ⊤)
    (hgram : ∀ i j, ⟪u i, u j⟫ = ⟪w i, w j⟫) :
    ∃ g : Isom 3, g v = v' ∧ ∀ (i : Fin m) (c : ℝ),
      g (v + c • u i) = v' + c • w i := by
  classical
  have hspanW := span_trasportato_da_gram hspanU hgram
  obtain ⟨L, hL⟩ := isometria_da_gram hspanU hspanW hgram
  refine ⟨AffineIsometryEquiv.mk'
    (fun x => L (x - v) + v') L v (by
      intro x
      show L (x - v) + v' = L (x - v) + (L (v - v) + v')
      simp), ?_, ?_⟩
  · show L (v - v) + v' = v'
    simp
  · intro i c
    show L (v + c • u i - v) + v' = v' + c • w i
    have hsub : v + c • u i - v = c • u i := by abel
    rw [hsub, map_smul, hL]
    abel

theorem registro_del_fan (P Q : ConvexPolytope 3) {p q : ℕ}
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (hQ : Q.asFinite.IsCyclicallyRegularOfType p q)
    {v v' : E 3} (hvP : v ∈ P.vertices) (hvQ : v' ∈ Q.vertices)
    (DP : P.asFinite.CyclicVertexData v q)
    (DQ : Q.asFinite.CyclicVertexData v' q)
    (hspan : Submodule.span ℝ (Set.range (dir P.asFinite v DP)) = ⊤) :
    ∃ g : Isom 3, g v = v' ∧
      ∀ i, g (v + dir P.asFinite v DP i) =
        v' + dir Q.asFinite v' DQ i := by
  haveI : NeZero q := ⟨by
    have hq : 3 ≤ q := hP.2.2.1
    omega⟩
  have hgram : ∀ i j,
      ⟪dir P.asFinite v DP i, dir P.asFinite v DP j⟫ =
        ⟪dir Q.asFinite v' DQ i, dir Q.asFinite v' DQ j⟫ := by
    intro i j
    rw [gram_direzioni_dal_fan P.asFinite hP hvP DP i j,
      gram_direzioni_dal_fan Q.asFinite hQ hvQ DQ i j]
  obtain ⟨g, hgv, hg⟩ := isometria_al_vertice hspan hgram
  refine ⟨g, hgv, ?_⟩
  intro i
  simpa using hg i 1

theorem full_dim_da_cyclic_data (P : ConvexPolytope 3)
    {v : E 3} {q : ℕ} (hq : 3 ≤ q)
    (D : P.asFinite.CyclicVertexData v q) : P.IsFullDim := by
  let i0 : Fin q := ⟨0, by omega⟩
  let i1 : Fin q := ⟨1, by omega⟩
  have hF0 := (P.asFinite_isFacet_iff (D.faccetta i0)).mp (D.isFacet i0)
  have hF1 := (P.asFinite_isFacet_iff (D.faccetta i1)).mp (D.isFacet i1)
  have h01 : D.faccetta i0 ≠ D.faccetta i1 := by
    exact fun heq => (by
      have hij : i0 = i1 := D.distinte heq
      have hv := congrArg Fin.val hij
      simp [i0, i1] at hv)
  have hF0proper : D.faccetta i0 ⊂ P.toSet := by
    refine ⟨face_subset_toSet P hF0.1, ?_⟩
    intro hback
    have htop : D.faccetta i0 = P.toSet :=
      Set.Subset.antisymm (face_subset_toSet P hF0.1) hback
    have hsub10 : D.faccetta i1 ⊂ D.faccetta i0 := by
      refine ⟨?_, ?_⟩
      · rw [htop]
        exact face_subset_toSet P hF1.1
      · intro hback10
        exact h01 (Set.Subset.antisymm hback10 (by
          rw [htop]
          exact face_subset_toSet P hF1.1))
    have hlt := faceDim_lt_of_ssubset P hF1.1 hF0.1 hsub10
    have hd0 : Module.finrank ℝ (vectorSpan ℝ (D.faccetta i0)) = 2 := hF0.2
    have hd1 : Module.finrank ℝ (vectorSpan ℝ (D.faccetta i1)) = 2 := hF1.2
    omega
  have hlt := faceDim_lt_of_ssubset P hF0.1 (toSet_isFace P) hF0proper
  have hlt' : Module.finrank ℝ (vectorSpan ℝ (D.faccetta i0)) <
      Module.finrank ℝ (vectorSpan ℝ P.toSet) := hlt
  have hdim0 : Module.finrank ℝ (vectorSpan ℝ (D.faccetta i0)) = 2 := hF0.2
  have hupper : Module.finrank ℝ (vectorSpan ℝ P.toSet) ≤ 3 := by
    calc
      Module.finrank ℝ (vectorSpan ℝ P.toSet) ≤ Module.finrank ℝ (E 3) :=
        Submodule.finrank_le _
      _ = 3 := by simp [finrank_euclideanSpace]
  show P.dim = 3
  unfold ConvexPolytope.dim
  omega

theorem spigolo_adiacente_suriettiva (P : ConvexPolytope 3)
    {v : E 3} {q : ℕ} (hq : 3 ≤ q)
    (D : P.asFinite.CyclicVertexData v q) (e : SpigoloPer P v) :
    ∃ i : Fin q, e = spigolo_adiacente P hq D i := by
  classical
  have hfull : P.IsFullDim := full_dim_da_cyclic_data P hq D
  obtain ⟨A, hA, hdA, heA⟩ :=
    faccetta_sopra_spigolo P hfull e.property.1 e.property.2.1
  obtain ⟨i, hi⟩ := D.complete A
    ((P.asFinite_isFacet_iff A).mpr ⟨hA, hdA⟩) (heA.subset e.property.2.2)
  have heFi : e.val ⊆ D.faccetta i := by
    rw [← hi]
    exact heA.subset
  rcases spigoli_in_v_della_faccetta_esatti P hq D i
      e.property.1 e.property.2.1 e.property.2.2 heFi with hprev | hnext
  · let j : Fin q := (finRotate q).symm i
    refine ⟨j, Subtype.ext ?_⟩
    have hji : finRotate q j = i := (finRotate q).apply_symm_apply i
    change e.val = D.faccetta j ∩ D.faccetta (finRotate q j)
    rw [hji]
    simpa only [j] using hprev
  · refine ⟨i, Subtype.ext ?_⟩
    simpa [spigolo_adiacente_val] using hnext

theorem span_raggi_top (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {p q : ℕ} (h : P.asFinite.IsCyclicallyRegularOfType p q)
    {v : E 3} (hv : v ∈ P.vertices)
    (D : P.asFinite.CyclicVertexData v q) :
    Submodule.span ℝ (Set.range (dir P.asFinite v D)) = ⊤ := by
  classical
  let S : Submodule ℝ (E 3) :=
    Submodule.span ℝ (Set.range (dir P.asFinite v D))
  by_contra hStop
  have hperp : Sᗮ ≠ ⊥ := by
    intro hbot
    exact hStop (Submodule.orthogonal_eq_bot_iff.mp hbot)
  obtain ⟨y, hyS, hyne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
  let phi : E 3 →L[ℝ] ℝ := innerSL ℝ y
  have hphi_dir : ∀ i : Fin q, phi (dir P.asFinite v D i) = 0 := by
    intro i
    have hdirS : dir P.asFinite v D i ∈ S := by
      exact Submodule.subset_span (Set.mem_range_self i)
    have hyorth := (Submodule.mem_orthogonal S y).mp hyS _ hdirS
    simpa [phi, real_inner_comm] using hyorth
  have hlocal_eq : ∀ e : SpigoloPer P v,
      phi (SpigoloPer.altro P v hv e) = phi v := by
    intro e
    obtain ⟨i, rfl⟩ := spigolo_adiacente_suriettiva P h.2.2.1 D e
    obtain ⟨t, ht, hray⟩ := altro_estremo_sul_raggio P h hv D i
    rw [hray]
    simp only [map_add, map_smul, hphi_dir, smul_eq_mul, mul_zero, add_zero]
  have hle : ∀ z ∈ P.toSet, phi z ≤ phi v :=
    locale_globale_vertice P hfull hv phi (fun e => (hlocal_eq e).le)
  have hle_neg : ∀ z ∈ P.toSet, (-phi) z ≤ (-phi) v :=
    locale_globale_vertice P hfull hv (-phi) (fun e => by
      simp only [neg_apply]
      rw [hlocal_eq e])
  have hconst : ∀ z ∈ P.toSet, phi z = phi v := by
    intro z hz
    apply le_antisymm (hle z hz)
    have hn := hle_neg z hz
    simp only [neg_apply] at hn
    linarith
  let f : Module.Dual ℝ (E 3) := phi.toLinearMap
  have hfne : f ≠ 0 := by
    intro hf
    have hfy := LinearMap.congr_fun hf y
    have hnormpos : 0 < ‖y‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hyne)
    change innerSL ℝ y y = 0 at hfy
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq] at hfy
    linarith
  have hvT : v ∈ P.toSet := subset_convexHull ℝ _ hv
  have hspan_ker : vectorSpan ℝ P.toSet ≤ LinearMap.ker f := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ hvT]
    apply Submodule.span_le.mpr
    intro d hd
    obtain ⟨z, hz, rfl⟩ := hd
    change phi (z - v) = 0
    rw [map_sub, hconst z hz, sub_self]
  have hkerdim := Module.Dual.finrank_ker_add_one_of_ne_zero hfne
  have hEdim : Module.finrank ℝ (E 3) = 3 := by
    simp [finrank_euclideanSpace]
  have hkerle : Module.finrank ℝ (LinearMap.ker f) ≤ 2 := by
    omega
  have hmono := Submodule.finrank_mono hspan_ker
  have hPdim : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
  omega

end LeanEval.Geometry.PlatonicClassification
