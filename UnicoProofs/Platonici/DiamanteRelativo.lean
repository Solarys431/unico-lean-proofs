import Mathlib
import UnicoProofs.Platonici.Diamante2D
import UnicoProofs.Platonici.SottoPolitopo

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : Nat}

theorem affineSpan_eq_of_subset_of_faceDim_eq {f g : Set (E n)}
    (hf : f.Nonempty) (hfg : f ⊆ g) (hdim : faceDim f = faceDim g) :
    affineSpan Real f = affineSpan Real g := by
  obtain ⟨a, ha⟩ := hf
  have hspan_le : vectorSpan Real f ≤ vectorSpan Real g :=
    vectorSpan_mono Real hfg
  have hspan_eq : vectorSpan Real f = vectorSpan Real g := by
    apply Submodule.eq_of_le_of_finrank_le hspan_le
    show faceDim g ≤ faceDim f
    exact le_of_eq hdim.symm
  have haff_le : affineSpan Real f ≤ affineSpan Real g :=
    affineSpan_mono Real hfg
  apply le_antisymm haff_le
  intro y hy
  have haff : a ∈ affineSpan Real f := subset_affineSpan Real f ha
  have hdir : (affineSpan Real f).direction =
      (affineSpan Real g).direction := by
    rw [direction_affineSpan, direction_affineSpan, hspan_eq]
  have hy_dir : y -ᵥ a ∈ (affineSpan Real g).direction :=
    AffineSubspace.vsub_mem_direction hy (haff_le haff)
  rw [← hdir] at hy_dir
  have := AffineSubspace.vadd_mem_of_mem_direction hy_dir haff
  simpa using this

theorem exists_point_outside_affineSpan_of_faceDim_lt {f g : Set (E n)}
    (hlt : faceDim f < faceDim g) :
    ∃ p ∈ g, p ∉ affineSpan Real f := by
  by_contra hall
  push Not at hall
  have haff_le : affineSpan Real g ≤ affineSpan Real f :=
    affineSpan_le.mpr hall
  have hdir_le : (affineSpan Real g).direction ≤
      (affineSpan Real f).direction := AffineSubspace.direction_le haff_le
  have hrank := Submodule.finrank_mono hdir_le
  rw [direction_affineSpan, direction_affineSpan] at hrank
  have hlt' : Module.finrank Real (vectorSpan Real f) <
      Module.finrank Real (vectorSpan Real g) := hlt
  exact (not_lt_of_ge hrank) hlt'

theorem fuori_dalla_terza_relativo (P : ConvexPolytope n)
    {A Ci Cj : Set (E n)}
    (hA : P.IsFace A) (hCi : P.IsFace Ci) (hCj : P.IsFace Cj)
    (hAi : A ⊂ Ci) (hAj : A ⊂ Cj)
    (hdCi : faceDim Ci = faceDim A + 1)
    (hdCj : faceDim Cj = faceDim A + 1) (hne : Ci ≠ Cj)
    {p : E n} (hpj : p ∈ Cj) (hpout : p ∉ affineSpan Real A) :
    p ∉ Ci := by
  intro hpi
  obtain ⟨a, ha⟩ := hA.2
  have hint : P.IsFace (Ci ∩ Cj) :=
    ⟨hCi.1.inter hCj.1, ⟨a, hAi.1 ha, hAj.1 ha⟩⟩
  have hinter_strict : Ci ∩ Cj ⊂ Ci := by
    refine ⟨Set.inter_subset_left, fun hsup => ?_⟩
    have hij : Ci ⊆ Cj := fun z hz => (hsup hz).2
    have hstrict : Ci ⊂ Cj :=
      ⟨hij, fun hji => hne (Set.Subset.antisymm hij hji)⟩
    have hlt := faceDim_lt_of_ssubset P hCi hCj hstrict
    omega
  have hinter_lt := faceDim_lt_of_ssubset P hint hCi hinter_strict
  have hAinter : A ⊆ Ci ∩ Cj := fun z hz => ⟨hAi.1 hz, hAj.1 hz⟩
  have hdim_le : faceDim A ≤ faceDim (Ci ∩ Cj) := by
    exact Submodule.finrank_mono (vectorSpan_mono Real hAinter)
  have hdim_eq : faceDim A = faceDim (Ci ∩ Cj) := by
    omega
  have haff_eq : affineSpan Real A = affineSpan Real (Ci ∩ Cj) :=
    affineSpan_eq_of_subset_of_faceDim_eq hA.2 hAinter hdim_eq
  apply hpout
  rw [haff_eq]
  exact subset_affineSpan Real (Ci ∩ Cj) ⟨hpi, hpj⟩

theorem proiezione_tre_vettori
    {U W : Submodule Real (E n)} (hUW : U ≤ W)
    (hdim : Module.finrank Real W = Module.finrank Real U + 2)
    {v1 v2 v3 : E n}
    (hv1W : v1 ∈ W) (hv2W : v2 ∈ W) (hv3W : v3 ∈ W)
    (hv1U : v1 ∉ U) (hv2U : v2 ∉ U) (hv3U : v3 ∉ U) :
    ∃ q1 q2 q3 : E n,
      q1 ∈ U.orthogonal ⊓ W ∧
      q2 ∈ U.orthogonal ⊓ W ∧
      q3 ∈ U.orthogonal ⊓ W ∧
      q1 ≠ 0 ∧ q2 ≠ 0 ∧ q3 ≠ 0 ∧
      v1 - q1 ∈ U ∧ v2 - q2 ∈ U ∧ v3 - q3 ∈ U ∧
      Module.finrank Real (U.orthogonal ⊓ W : Submodule Real (E n)) = 2 := by
  let q1 : E n := U.orthogonal.starProjection v1
  let q2 : E n := U.orthogonal.starProjection v2
  let q3 : E n := U.orthogonal.starProjection v3
  have difference : ∀ v : E n,
      v - U.orthogonal.starProjection v ∈ U := by
    intro v
    rw [Submodule.starProjection_orthogonal_val]
    simp
  have hq1d : v1 - q1 ∈ U := difference v1
  have hq2d : v2 - q2 ∈ U := difference v2
  have hq3d : v3 - q3 ∈ U := difference v3
  have hq1perp : q1 ∈ U.orthogonal :=
    U.orthogonal.starProjection_apply_mem v1
  have hq2perp : q2 ∈ U.orthogonal :=
    U.orthogonal.starProjection_apply_mem v2
  have hq3perp : q3 ∈ U.orthogonal :=
    U.orthogonal.starProjection_apply_mem v3
  have hq1W : q1 ∈ W := by
    have : q1 = v1 - (v1 - q1) := by abel
    rw [this]
    exact W.sub_mem hv1W (hUW hq1d)
  have hq2W : q2 ∈ W := by
    have : q2 = v2 - (v2 - q2) := by abel
    rw [this]
    exact W.sub_mem hv2W (hUW hq2d)
  have hq3W : q3 ∈ W := by
    have : q3 = v3 - (v3 - q3) := by abel
    rw [this]
    exact W.sub_mem hv3W (hUW hq3d)
  have hq1ne : q1 ≠ 0 := by
    intro hq
    apply hv1U
    simpa [hq] using hq1d
  have hq2ne : q2 ≠ 0 := by
    intro hq
    apply hv2U
    simpa [hq] using hq2d
  have hq3ne : q3 ≠ 0 := by
    intro hq
    apply hv3U
    simpa [hq] using hq3d
  have hdimV : Module.finrank Real
      (U.orthogonal ⊓ W : Submodule Real (E n)) = 2 := by
    have hadd := Submodule.finrank_add_inf_finrank_orthogonal hUW
    omega
  exact ⟨q1, q2, q3, ⟨hq1perp, hq1W⟩, ⟨hq2perp, hq2W⟩,
    ⟨hq3perp, hq3W⟩, hq1ne, hq2ne, hq3ne, hq1d, hq2d, hq3d, hdimV⟩

theorem conteggio_dimensionale {V : Submodule Real (E n)}
    (hdim : Module.finrank Real V = 2) {q1 q2 q3 : E n}
    (hq1 : q1 ∈ V) (hq2 : q2 ∈ V) (hq3 : q3 ∈ V) :
    ¬ LinearIndependent Real (fun i : Fin 3 =>
      if i.val = 0 then q1 else if i.val = 1 then q2 else q3) := by
  intro hli
  have hspan : Submodule.span Real (Set.range (fun i : Fin 3 =>
      if i.val = 0 then q1 else if i.val = 1 then q2 else q3)) ≤ V := by
    rw [Submodule.span_le]
    rintro z ⟨i, rfl⟩
    rcases i with ⟨iv, hi⟩
    interval_cases iv
    · exact hq1
    · exact hq2
    · exact hq3
  have hrank_span : Module.finrank Real (Submodule.span Real
      (Set.range (fun i : Fin 3 =>
        if i.val = 0 then q1 else if i.val = 1 then q2 else q3))) = 3 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hle := Submodule.finrank_mono hspan
  omega

theorem atMostTwo_middle_faces (P : ConvexPolytope n) {A B : Set (E n)}
    (hA : P.IsFace A) (hB : P.IsFace B)
    (hrank : faceDim B = faceDim A + 2)
    {C1 C2 C3 : Set (E n)}
    (hC1 : P.IsFace C1) (hA1 : A ⊂ C1) (h1B : C1 ⊂ B)
    (hC2 : P.IsFace C2) (hA2 : A ⊂ C2) (h2B : C2 ⊂ B)
    (hC3 : P.IsFace C3) (hA3 : A ⊂ C3) (h3B : C3 ⊂ B) :
    C1 = C2 ∨ C1 = C3 ∨ C2 = C3 := by
  classical
  by_contra hall
  push Not at hall
  rcases hall with ⟨h12, h13, h23⟩
  have hdC1lo := faceDim_lt_of_ssubset P hA hC1 hA1
  have hdC1hi := faceDim_lt_of_ssubset P hC1 hB h1B
  have hdC2lo := faceDim_lt_of_ssubset P hA hC2 hA2
  have hdC2hi := faceDim_lt_of_ssubset P hC2 hB h2B
  have hdC3lo := faceDim_lt_of_ssubset P hA hC3 hA3
  have hdC3hi := faceDim_lt_of_ssubset P hC3 hB h3B
  have hdC1 : faceDim C1 = faceDim A + 1 := by omega
  have hdC2 : faceDim C2 = faceDim A + 1 := by omega
  have hdC3 : faceDim C3 = faceDim A + 1 := by omega
  let Q := facePolytope P hB
  have hC1Q : Q.IsFace C1 := facePolytope_isFace_of P hB hC1 h1B.1
  have hC2Q : Q.IsFace C2 := facePolytope_isFace_of P hB hC2 h2B.1
  have hC3Q : Q.IsFace C3 := facePolytope_isFace_of P hB hC3 h3B.1
  obtain ⟨a, haA⟩ := hA.2
  obtain ⟨p1, hp1C, hp1out⟩ :=
    exists_point_outside_affineSpan_of_faceDim_lt hdC1lo
  obtain ⟨p2, hp2C, hp2out⟩ :=
    exists_point_outside_affineSpan_of_faceDim_lt hdC2lo
  obtain ⟨p3, hp3C, hp3out⟩ :=
    exists_point_outside_affineSpan_of_faceDim_lt hdC3lo
  have hp12 : p2 ∉ C1 := fuori_dalla_terza_relativo P hA hC1 hC2
    hA1 hA2 hdC1 hdC2 h12 hp2C hp2out
  have hp13 : p3 ∉ C1 := fuori_dalla_terza_relativo P hA hC1 hC3
    hA1 hA3 hdC1 hdC3 h13 hp3C hp3out
  have hp21 : p1 ∉ C2 := fuori_dalla_terza_relativo P hA hC2 hC1
    hA2 hA1 hdC2 hdC1 h12.symm hp1C hp1out
  have hp23 : p3 ∉ C2 := fuori_dalla_terza_relativo P hA hC2 hC3
    hA2 hA3 hdC2 hdC3 h23 hp3C hp3out
  have hp31 : p1 ∉ C3 := fuori_dalla_terza_relativo P hA hC3 hC1
    hA3 hA1 hdC3 hdC1 h13.symm hp1C hp1out
  have hp32 : p2 ∉ C3 := fuori_dalla_terza_relativo P hA hC3 hC2
    hA3 hA2 hdC3 hdC2 h23.symm hp2C hp2out
  obtain ⟨l1, hmem1, hmax1⟩ := espositore_di_faccia Q hC1Q
  obtain ⟨l2, hmem2, hmax2⟩ := espositore_di_faccia Q hC2Q
  obtain ⟨l3, hmem3, hmax3⟩ := espositore_di_faccia Q hC3Q
  have costanza : ∀ {D : Set (E n)} {lD : E n →L[Real] Real},
      (∀ y ∈ D, y ∈ Q.toSet ∧ ∀ z ∈ Q.toSet, lD z ≤ lD y) →
      ∀ {y y' : E n}, y ∈ D → y' ∈ D → lD y = lD y' := by
    intro D lD hmem y y' hy hy'
    exact le_antisymm ((hmem y' hy').2 y (hmem y hy).1)
      ((hmem y hy).2 y' (hmem y' hy').1)
  have strict : ∀ {Ci Cj : Set (E n)} {li : E n →L[Real] Real},
      Q.IsFace Ci → Q.IsFace Cj →
      (∀ y ∈ Ci, y ∈ Q.toSet ∧ ∀ z ∈ Q.toSet, li z ≤ li y) →
      (∀ q ∈ Q.toSet, (∀ z ∈ Q.toSet, li z ≤ li q) → q ∈ Ci) →
      a ∈ Ci → ∀ {p : E n}, p ∈ Cj → p ∉ Ci → li p < li a := by
    intro Ci Cj li hi hj hmem hmax ha p hpj hpnot
    have hpQ : p ∈ Q.toSet := face_subset_toSet Q hj hpj
    have hle : li p ≤ li a := (hmem a ha).2 p hpQ
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      apply hpnot
      exact hmax p hpQ
        (fun z hz => le_trans ((hmem a ha).2 z hz) (le_of_eq heq.symm))
  have s12 := strict hC1Q hC2Q hmem1 hmax1 (hA1.1 haA) hp2C hp12
  have s13 := strict hC1Q hC3Q hmem1 hmax1 (hA1.1 haA) hp3C hp13
  have s21 := strict hC2Q hC1Q hmem2 hmax2 (hA2.1 haA) hp1C hp21
  have s23 := strict hC2Q hC3Q hmem2 hmax2 (hA2.1 haA) hp3C hp23
  have s31 := strict hC3Q hC1Q hmem3 hmax3 (hA3.1 haA) hp1C hp31
  have s32 := strict hC3Q hC2Q hmem3 hmax3 (hA3.1 haA) hp2C hp32
  let U : Submodule Real (E n) := vectorSpan Real A
  let W : Submodule Real (E n) := vectorSpan Real B
  let v1 : E n := p1 - a
  let v2 : E n := p2 - a
  let v3 : E n := p3 - a
  have hUW : U ≤ W := vectorSpan_mono Real (hA1.1.trans h1B.1)
  have hv1W : v1 ∈ W := vsub_mem_vectorSpan Real (h1B.1 hp1C)
    (h1B.1 (hA1.1 haA))
  have hv2W : v2 ∈ W := vsub_mem_vectorSpan Real (h2B.1 hp2C)
    (h2B.1 (hA2.1 haA))
  have hv3W : v3 ∈ W := vsub_mem_vectorSpan Real (h3B.1 hp3C)
    (h3B.1 (hA3.1 haA))
  have hv1U : v1 ∉ U := by
    intro hv
    apply hp1out
    have hvdir : p1 - a ∈ (affineSpan Real A).direction := by
      rw [direction_affineSpan]
      simpa [U, v1] using hv
    simpa using AffineSubspace.vadd_mem_of_mem_direction hvdir
      (subset_affineSpan Real A haA)
  have hv2U : v2 ∉ U := by
    intro hv
    apply hp2out
    have hvdir : p2 - a ∈ (affineSpan Real A).direction := by
      rw [direction_affineSpan]
      simpa [U, v2] using hv
    simpa using AffineSubspace.vadd_mem_of_mem_direction hvdir
      (subset_affineSpan Real A haA)
  have hv3U : v3 ∉ U := by
    intro hv
    apply hp3out
    have hvdir : p3 - a ∈ (affineSpan Real A).direction := by
      rw [direction_affineSpan]
      simpa [U, v3] using hv
    simpa using AffineSubspace.vadd_mem_of_mem_direction hvdir
      (subset_affineSpan Real A haA)
  have hdimW : Module.finrank Real W = Module.finrank Real U + 2 := by
    change faceDim B = faceDim A + 2
    exact hrank
  obtain ⟨q1, q2, q3, hq1V, hq2V, hq3V, hq1ne, hq2ne, hq3ne,
      hv1q, hv2q, hv3q, hdimV⟩ :=
    proiezione_tre_vettori hUW hdimW hv1W hv2W hv3W hv1U hv2U hv3U
  have hdep := conteggio_dimensionale hdimV hq1V hq2V hq3V
  obtain ⟨gc, hgsum, i0, hgne⟩ := Fintype.not_linearIndependent_iff.mp hdep
  rw [Fin.sum_univ_three] at hgsum
  have hgsum3 : gc 0 • q1 + gc 1 • q2 + gc 2 • q3 = 0 := hgsum
  have hnz3 : gc 0 ≠ 0 ∨ gc 1 ≠ 0 ∨ gc 2 ≠ 0 := by
    rcases i0 with ⟨iv, hi⟩
    interval_cases iv
    · exact Or.inl hgne
    · exact Or.inr (Or.inl hgne)
    · exact Or.inr (Or.inr hgne)
  have kills : ∀ {Ci : Set (E n)} {li : E n →L[Real] Real},
      (∀ y ∈ Ci, y ∈ Q.toSet ∧ ∀ z ∈ Q.toSet, li z ≤ li y) →
      A ⊆ Ci → U ≤ LinearMap.ker li.toLinearMap := by
    intro Ci li hmem hAC
    change vectorSpan Real A ≤ LinearMap.ker li.toLinearMap
    rw [vectorSpan_eq_span_vsub_set_right Real haA, Submodule.span_le]
    rintro z ⟨x, hx, rfl⟩
    change li (x - a) = 0
    rw [map_sub]
    have heq := costanza hmem (hAC hx) (hAC haA)
    linarith
  have hkill1 := kills hmem1 hA1.1
  have hkill2 := kills hmem2 hA2.1
  have hkill3 := kills hmem3 hA3.1
  have eval_projection : ∀ (li : E n →L[Real] Real),
      U ≤ LinearMap.ker li.toLinearMap →
      ∀ (v q : E n), v - q ∈ U → li q = li v := by
    intro li hkill v q hvq
    have hz : li (v - q) = 0 := hkill hvq
    rw [map_sub] at hz
    linarith
  have hM1 := congrArg (fun w => l1 w) hgsum3
  have hM2 := congrArg (fun w => l2 w) hgsum3
  have hM3 := congrArg (fun w => l3 w) hgsum3
  simp only [map_add, map_smul, map_zero, smul_eq_mul] at hM1 hM2 hM3
  have e11 : l1 q1 = 0 := by
    rw [eval_projection l1 hkill1 v1 q1 hv1q]
    change l1 (p1 - a) = 0
    rw [map_sub]
    have heq := costanza hmem1 hp1C (hA1.1 haA)
    linarith
  have e22 : l2 q2 = 0 := by
    rw [eval_projection l2 hkill2 v2 q2 hv2q]
    change l2 (p2 - a) = 0
    rw [map_sub]
    have heq := costanza hmem2 hp2C (hA2.1 haA)
    linarith
  have e33 : l3 q3 = 0 := by
    rw [eval_projection l3 hkill3 v3 q3 hv3q]
    change l3 (p3 - a) = 0
    rw [map_sub]
    have heq := costanza hmem3 hp3C (hA3.1 haA)
    linarith
  have rel1 : gc 1 * l1 q2 + gc 2 * l1 q3 = 0 := by
    rw [e11] at hM1
    linarith
  have rel2 : gc 0 * l2 q1 + gc 2 * l2 q3 = 0 := by
    rw [e22] at hM2
    linarith
  have rel3 : gc 0 * l3 q1 + gc 1 * l3 q2 = 0 := by
    rw [e33] at hM3
    linarith
  have n12 : l1 q2 < 0 := by
    rw [eval_projection l1 hkill1 v2 q2 hv2q]
    change l1 (p2 - a) < 0
    rw [map_sub]
    linarith
  have n13 : l1 q3 < 0 := by
    rw [eval_projection l1 hkill1 v3 q3 hv3q]
    change l1 (p3 - a) < 0
    rw [map_sub]
    linarith
  have n21 : l2 q1 < 0 := by
    rw [eval_projection l2 hkill2 v1 q1 hv1q]
    change l2 (p1 - a) < 0
    rw [map_sub]
    linarith
  have n23 : l2 q3 < 0 := by
    rw [eval_projection l2 hkill2 v3 q3 hv3q]
    change l2 (p3 - a) < 0
    rw [map_sub]
    linarith
  have n31 : l3 q1 < 0 := by
    rw [eval_projection l3 hkill3 v1 q1 hv1q]
    change l3 (p1 - a) < 0
    rw [map_sub]
    linarith
  have n32 : l3 q2 < 0 := by
    rw [eval_projection l3 hkill3 v2 q2 hv2q]
    change l3 (p2 - a) < 0
    rw [map_sub]
    linarith
  have hc0 : gc 0 ≠ 0 := by
    intro h0
    have h2 : gc 2 = 0 := by
      have hz : gc 2 * l2 q3 = 0 := by rw [h0] at rel2; linarith
      exact (mul_eq_zero.mp hz).resolve_right (ne_of_lt n23)
    have h1 : gc 1 = 0 := by
      have hz : gc 1 * l3 q2 = 0 := by rw [h0] at rel3; linarith
      exact (mul_eq_zero.mp hz).resolve_right (ne_of_lt n32)
    rcases hnz3 with h | h | h
    · exact h h0
    · exact h h1
    · exact h h2
  have hc1 : gc 1 ≠ 0 := by
    intro h1
    have h2 : gc 2 = 0 := by
      have hz : gc 2 * l1 q3 = 0 := by rw [h1] at rel1; linarith
      exact (mul_eq_zero.mp hz).resolve_right (ne_of_lt n13)
    have h0 : gc 0 = 0 := by
      have hz : gc 0 * l3 q1 = 0 := by rw [h1] at rel3; linarith
      exact (mul_eq_zero.mp hz).resolve_right (ne_of_lt n31)
    rcases hnz3 with h | h | h
    · exact h h0
    · exact h h1
    · exact h h2
  have hc2 : gc 2 ≠ 0 := by
    intro h2
    have h1 : gc 1 = 0 := by
      have hz : gc 1 * l1 q2 = 0 := by rw [h2] at rel1; linarith
      exact (mul_eq_zero.mp hz).resolve_right (ne_of_lt n12)
    have h0 : gc 0 = 0 := by
      have hz : gc 0 * l2 q1 = 0 := by rw [h2] at rel2; linarith
      exact (mul_eq_zero.mp hz).resolve_right (ne_of_lt n21)
    rcases hnz3 with h | h | h
    · exact h h0
    · exact h h1
    · exact h h2
  have h12s : gc 1 * gc 2 < 0 := segno_opposto rel1 n12 n13 hc1 hc2
  have h02s : gc 0 * gc 2 < 0 := segno_opposto rel2 n21 n23 hc0 hc2
  have h01s : gc 0 * gc 1 < 0 := segno_opposto rel3 n31 n32 hc0 hc1
  have hpos : 0 < (gc 0 * gc 1) * (gc 0 * gc 2) :=
    mul_pos_of_neg_of_neg h01s h02s
  nlinarith [hpos, h12s, sq_nonneg (gc 0)]

end LeanEval.Geometry.PlatonicClassification
