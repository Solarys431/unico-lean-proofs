import Mathlib
import UnicoProofs.Platonici.ConnessioneVentaglio
import UnicoProofs.Platonici.DiamanteRelativo
import UnicoProofs.Platonici.FacciaIntermedia
import UnicoProofs.Platonici.PerturbazioneFinita
import UnicoProofs.Platonici.MossaInvolutiva
import UnicoProofs.Platonici.PoligonoConnesso

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n m : ℕ}

/-! The convex hull of the image of a finite polytope, with the redundant
image points removed.  This is deliberately stated for a continuous linear
map: the quotient used below is not injective. -/
noncomputable def linearImagePolytope (P : ConvexPolytope n)
    (f : E n →L[ℝ] E m) : ConvexPolytope m := by
  classical
  let S : Finset (E m) := P.vertices.image f
  let K : Set (E m) := convexHull ℝ (S : Set (E m))
  let V : Finset (E m) := S.filter (fun x => x ∈ K.extremePoints ℝ)
  have hSne : S.Nonempty := P.vertices_nonempty.image f
  have hKne : K.Nonempty := by
    obtain ⟨x, hx⟩ := hSne
    exact ⟨x, subset_convexHull ℝ _ (by exact_mod_cast hx)⟩
  have hKcompact : IsCompact K := S.finite_toSet.isCompact_convexHull ℝ
  have hVne : V.Nonempty := by
    obtain ⟨x, hx⟩ := hKcompact.extremePoints_nonempty hKne
    have hxS : x ∈ (S : Set (E m)) := extremePoints_convexHull_subset hx
    exact ⟨x, Finset.mem_filter.mpr ⟨by exact_mod_cast hxS, hx⟩⟩
  have hVset : (V : Set (E m)) = K.extremePoints ℝ := by
    ext x
    simp only [V, Finset.mem_coe, Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro hx
      exact ⟨by exact_mod_cast (extremePoints_convexHull_subset hx), hx⟩
  have hKV : convexHull ℝ (V : Set (E m)) = K := by
    have hKM := closure_convexHull_extremePoints hKcompact (convex_convexHull ℝ _)
    rw [← hVset] at hKM
    rw [← hKM]
    exact (V.finite_toSet.isClosed_convexHull ℝ).closure_eq.symm
  exact
    { vertices := V
      vertices_nonempty := hVne
      vertices_eq_extremePoints := by
        rw [hKV, hVset] }

theorem linearImagePolytope_toSet (P : ConvexPolytope n)
    (f : E n →L[ℝ] E m) :
    (linearImagePolytope P f).toSet = f '' P.toSet := by
  classical
  let S : Finset (E m) := P.vertices.image f
  let K : Set (E m) := convexHull ℝ (S : Set (E m))
  let V : Finset (E m) := S.filter (fun x => x ∈ K.extremePoints ℝ)
  have hKcompact : IsCompact K := S.finite_toSet.isCompact_convexHull ℝ
  have hVset : (V : Set (E m)) = K.extremePoints ℝ := by
    ext x
    simp only [V, Finset.mem_coe, Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro hx
      exact ⟨by exact_mod_cast (extremePoints_convexHull_subset hx), hx⟩
  have hKV : convexHull ℝ (V : Set (E m)) = K := by
    have hKM := closure_convexHull_extremePoints hKcompact (convex_convexHull ℝ _)
    rw [← hVset] at hKM
    rw [← hKM]
    exact (V.finite_toSet.isClosed_convexHull ℝ).closure_eq.symm
  change convexHull ℝ
      (((linearImagePolytope P f).vertices : Finset (E m)) : Set (E m)) = _
  change convexHull ℝ (V : Set (E m)) = _
  rw [hKV]
  have hS : (S : Set (E m)) = f '' (P.vertices : Set (E n)) := by
    ext x
    simp [S]
  rw [show K = convexHull ℝ (S : Set (E m)) from rfl, hS]
  exact (f.toLinearMap.toAffineMap.image_convexHull
    (P.vertices : Set (E n))).symm

/-! Orthogonal projection to `Uᵌ ∩ W` is the concrete quotient of `W`
by `U`.  The point of the next lemma is the exact fibre statement; no
ambient full-dimensionality is used. -/
theorem relative_starProjection_fiber
    {U W : Submodule ℝ (E n)} (hUW : U ≤ W) {x y : E n}
    (hxyW : x - y ∈ W) :
    (U.orthogonal ⊓ W).starProjection x =
        (U.orthogonal ⊓ W).starProjection y ↔
      x - y ∈ U := by
  let V : Submodule ℝ (E n) := U.orthogonal ⊓ W
  constructor
  · intro hproj
    have hzero : V.starProjection (x - y) = 0 := by
      rw [map_sub, hproj, sub_self]
    have hperp : x - y ∈ V.orthogonal := by
      rw [← V.ker_starProjection]
      exact hzero
    let p : E n := U.orthogonal.starProjection (x - y)
    have hpUperp : p ∈ U.orthogonal :=
      U.orthogonal.starProjection_apply_mem (x - y)
    have hdiffU : x - y - p ∈ U := by
      dsimp [p]
      rw [Submodule.starProjection_orthogonal_val]
      simpa only [sub_sub_cancel] using U.starProjection_apply_mem (x - y)
    have hpW : p ∈ W := by
      have hpform : p = (x - y) - (x - y - p) := by abel
      rw [hpform]
      exact W.sub_mem hxyW (hUW hdiffU)
    have hpV : p ∈ V := ⟨hpUperp, hpW⟩
    have hdp : inner ℝ (x - y) p = 0 := by
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal V (x - y)).mp hperp p hpV
    have hdiffp : inner ℝ (x - y - p) p = 0 := by
      exact (Submodule.mem_orthogonal U p).mp hpUperp (x - y - p) hdiffU
    have hpp : inner ℝ p p = 0 := by
      rw [inner_sub_left] at hdiffp
      linarith
    have hpzero : p = 0 := inner_self_eq_zero.mp hpp
    simpa [hpzero] using hdiffU
  · intro hxyU
    have hxyVperp : x - y ∈ V.orthogonal := by
      intro z hz
      rw [real_inner_comm]
      exact hz.1 (x - y) hxyU
    have hzero : V.starProjection (x - y) = 0 := by
      exact V.starProjection_apply_eq_zero_iff.mpr hxyVperp
    rw [map_sub] at hzero
    exact sub_eq_zero.mp hzero

theorem relative_sub_starProjection_mem
    {U W : Submodule ℝ (E n)} (hUW : U ≤ W) {z : E n} (hzW : z ∈ W) :
    z - (U.orthogonal ⊓ W).starProjection z ∈ U := by
  let V : Submodule ℝ (E n) := U.orthogonal ⊓ W
  have hpV : V.starProjection z ∈ V := V.starProjection_apply_mem z
  have hdiffW : z - V.starProjection z ∈ W :=
    W.sub_mem hzW hpV.2
  apply (relative_starProjection_fiber hUW hdiffW).mp
  exact (V.starProjection_eq_self_iff.mpr hpV).symm

theorem relative_image_isFace (P : ConvexPolytope n)
    {A B C : Set (E n)} (hA : P.IsFace A) (hB : P.IsFace B)
    (hC : P.IsFace C) (hAB : A ⊆ B) (hAC : A ⊆ C) (hCB : C ⊆ B)
    (e : ↥((vectorSpan ℝ A).orthogonal ⊓ vectorSpan ℝ B) ≃L[ℝ] E 3) :
    let V := (vectorSpan ℝ A).orthogonal ⊓ vectorSpan ℝ B
    let q : E n →L[ℝ] E 3 :=
      e.toContinuousLinearMap.comp V.orthogonalProjectionOnto
    let Q := linearImagePolytope (facePolytope P hB) q
    Q.IsFace (q '' C) := by
  classical
  dsimp only
  let U : Submodule ℝ (E n) := vectorSpan ℝ A
  let W : Submodule ℝ (E n) := vectorSpan ℝ B
  let V : Submodule ℝ (E n) := U.orthogonal ⊓ W
  let q : E n →L[ℝ] E 3 :=
    e.toContinuousLinearMap.comp V.orthogonalProjectionOnto
  let Q := linearImagePolytope (facePolytope P hB) q
  let QB := facePolytope P hB
  have hCQB : QB.IsFace C := facePolytope_isFace_of P hB hC hCB
  obtain ⟨l, hmem, hchar⟩ := espositore_di_faccia QB hCQB
  obtain ⟨a, haA⟩ := hA.2
  have hUW : U ≤ W := vectorSpan_mono ℝ hAB
  have hkill : U ≤ LinearMap.ker l.toLinearMap := by
    change vectorSpan ℝ A ≤ LinearMap.ker l.toLinearMap
    rw [vectorSpan_eq_span_vsub_set_right ℝ haA, Submodule.span_le]
    rintro z ⟨x, hxA, rfl⟩
    change l (x - a) = 0
    rw [map_sub]
    have hxC : x ∈ C := hAC hxA
    have haC : a ∈ C := hAC haA
    have heq : l x = l a := by
      exact le_antisymm ((hmem a haC).2 x (hmem x hxC).1)
        ((hmem x hxC).2 a (hmem a haC).1)
    linarith
  let pull : E 3 →L[ℝ] E n :=
    V.subtypeL.comp e.symm.toContinuousLinearMap
  let l3 : E 3 →L[ℝ] ℝ := l.comp pull
  have hlinear : ∀ z ∈ W, l3 (q z) = l z := by
    intro z hzW
    have hdiff : z - V.starProjection z ∈ U :=
      relative_sub_starProjection_mem hUW hzW
    have hzero : l (z - V.starProjection z) = 0 := hkill hdiff
    rw [map_sub] at hzero
    have heval : (pull (q z) : E n) = V.starProjection z := by
      dsimp only [pull, q, ContinuousLinearMap.comp_apply]
      have heq := e.symm_apply_apply (V.orthogonalProjectionOnto z)
      change ((e.symm (e (V.orthogonalProjectionOnto z)) : V) : E n) =
        V.starProjection z
      rw [heq]
      rfl
    change l (pull (q z)) = l z
    rw [heval]
    linarith
  let κ : ℝ := l3 (q a) - l a
  have hfactor : ∀ z ∈ B, l3 (q z) = l z + κ := by
    intro z hzB
    have haB : a ∈ B := hAB haA
    have hzaW : z - a ∈ W := vsub_mem_vectorSpan ℝ hzB haB
    have hlin := hlinear (z - a) hzaW
    simp only [map_sub] at hlin
    dsimp [κ]
    linarith
  have hQT : Q.toSet = q '' B := by
    rw [linearImagePolytope_toSet, facePolytope_toSet P hB]
  refine ⟨?_, hC.2.image q⟩
  intro _hne
  refine ⟨l3, Set.ext ?_⟩
  intro y
  constructor
  · rintro ⟨x, hxC, rfl⟩
    have hxB : x ∈ B := hCB hxC
    refine ⟨?_, ?_⟩
    · rw [hQT]
      exact ⟨x, hxB, rfl⟩
    · intro y' hy'
      rw [hQT] at hy'
      obtain ⟨z, hzB, rfl⟩ := hy'
      rw [hfactor x hxB, hfactor z hzB]
      have hzQB : z ∈ QB.toSet := by
        change z ∈ (facePolytope P hB).toSet
        rwa [facePolytope_toSet P hB]
      simpa [add_comm] using add_le_add_right ((hmem x hxC).2 z hzQB) κ
  · rintro ⟨hyQ, hymax⟩
    rw [hQT] at hyQ
    obtain ⟨x, hxB, rfl⟩ := hyQ
    refine ⟨x, ?_, rfl⟩
    have hxQB : x ∈ QB.toSet := by
      change x ∈ (facePolytope P hB).toSet
      rwa [facePolytope_toSet P hB]
    apply hchar x hxQB
    intro z hzQB
    have hzB : z ∈ B := by
      change z ∈ (facePolytope P hB).toSet at hzQB
      rwa [facePolytope_toSet P hB] at hzQB
    have hle := hymax (q z) (by rw [hQT]; exact ⟨z, hzB, rfl⟩)
    rw [hfactor x hxB, hfactor z hzB] at hle
    linarith

theorem relative_image_saturated (P : ConvexPolytope n)
    {A B C : Set (E n)} (hA : P.IsFace A) (hB : P.IsFace B)
    (hC : P.IsFace C) (hAB : A ⊆ B) (hAC : A ⊆ C) (hCB : C ⊆ B)
    (e : ↥((vectorSpan ℝ A).orthogonal ⊓ vectorSpan ℝ B) ≃L[ℝ] E 3) :
    let V := (vectorSpan ℝ A).orthogonal ⊓ vectorSpan ℝ B
    let q : E n →L[ℝ] E 3 :=
      e.toContinuousLinearMap.comp V.orthogonalProjectionOnto
    ∀ x ∈ B, x ∈ q ⁻¹' (q '' C) → x ∈ C := by
  classical
  dsimp only
  let U : Submodule ℝ (E n) := vectorSpan ℝ A
  let W : Submodule ℝ (E n) := vectorSpan ℝ B
  let V : Submodule ℝ (E n) := U.orthogonal ⊓ W
  let q : E n →L[ℝ] E 3 :=
    e.toContinuousLinearMap.comp V.orthogonalProjectionOnto
  let QB := facePolytope P hB
  have hCQB : QB.IsFace C := facePolytope_isFace_of P hB hC hCB
  obtain ⟨l, hmem, hchar⟩ := espositore_di_faccia QB hCQB
  obtain ⟨a, haA⟩ := hA.2
  have hUW : U ≤ W := vectorSpan_mono ℝ hAB
  have hkill : U ≤ LinearMap.ker l.toLinearMap := by
    change vectorSpan ℝ A ≤ LinearMap.ker l.toLinearMap
    rw [vectorSpan_eq_span_vsub_set_right ℝ haA, Submodule.span_le]
    rintro z ⟨y, hyA, rfl⟩
    change l (y - a) = 0
    rw [map_sub]
    have hyC : y ∈ C := hAC hyA
    have haC : a ∈ C := hAC haA
    have heq : l y = l a := by
      exact le_antisymm ((hmem a haC).2 y (hmem y hyC).1)
        ((hmem y hyC).2 a (hmem a haC).1)
    linarith
  intro x hxB hximage
  obtain ⟨c, hcC, hqc⟩ := hximage
  have hxcW : x - c ∈ W :=
    vsub_mem_vectorSpan ℝ hxB (hCB hcC)
  have hprojSubtype : V.orthogonalProjectionOnto x =
      V.orthogonalProjectionOnto c := by
    apply e.injective
    exact hqc.symm
  have hproj : V.starProjection x = V.starProjection c := by
    exact congrArg (fun z : V => (z : E n)) hprojSubtype
  have hxcU : x - c ∈ U :=
    (relative_starProjection_fiber hUW hxcW).mp hproj
  have hzero : l (x - c) = 0 := hkill hxcU
  rw [map_sub] at hzero
  have hxQB : x ∈ QB.toSet := by
    change x ∈ (facePolytope P hB).toSet
    rwa [facePolytope_toSet P hB]
  apply hchar x hxQB
  intro z hzQB
  have hle := (hmem c hcC).2 z hzQB
  linarith

theorem relative_lift_isFace (P : ConvexPolytope n)
    {A B : Set (E n)} (_hA : P.IsFace A) (hB : P.IsFace B)
    (e : ↥((vectorSpan ℝ A).orthogonal ⊓ vectorSpan ℝ B) ≃L[ℝ] E 3)
    {Y : Set (E 3)} :
    let V := (vectorSpan ℝ A).orthogonal ⊓ vectorSpan ℝ B
    let q : E n →L[ℝ] E 3 :=
      e.toContinuousLinearMap.comp V.orthogonalProjectionOnto
    let Q := linearImagePolytope (facePolytope P hB) q
    Q.IsFace Y → P.IsFace (B ∩ q ⁻¹' Y) := by
  classical
  dsimp only
  let V := (vectorSpan ℝ A).orthogonal ⊓ vectorSpan ℝ B
  let q : E n →L[ℝ] E 3 :=
    e.toContinuousLinearMap.comp V.orthogonalProjectionOnto
  let QB := facePolytope P hB
  let Q := linearImagePolytope QB q
  intro hY
  obtain ⟨l3, hmem, hchar⟩ := espositore_di_faccia Q hY
  let l : E n →L[ℝ] ℝ := l3.comp q
  have hQT : Q.toSet = q '' B := by
    rw [linearImagePolytope_toSet, facePolytope_toSet P hB]
  have hLiftNe : (B ∩ q ⁻¹' Y).Nonempty := by
    obtain ⟨y, hyY⟩ := hY.2
    have hyQ : y ∈ Q.toSet := face_subset_toSet Q hY hyY
    rw [hQT] at hyQ
    obtain ⟨x, hxB, rfl⟩ := hyQ
    exact ⟨x, hxB, hyY⟩
  have hLiftQB : QB.IsFace (B ∩ q ⁻¹' Y) := by
    refine ⟨?_, hLiftNe⟩
    intro _hne
    refine ⟨l, Set.ext ?_⟩
    intro x
    constructor
    · rintro ⟨hxB, hqxY⟩
      have hqxQ : q x ∈ Q.toSet := by
        rw [hQT]
        exact ⟨x, hxB, rfl⟩
      refine ⟨?_, ?_⟩
      · change x ∈ (facePolytope P hB).toSet
        rwa [facePolytope_toSet P hB]
      · intro z hzQB
        have hzB : z ∈ B := by
          change z ∈ (facePolytope P hB).toSet at hzQB
          rwa [facePolytope_toSet P hB] at hzQB
        change l3 (q z) ≤ l3 (q x)
        exact (hmem (q x) hqxY).2 (q z) (by
          rw [hQT]
          exact ⟨z, hzB, rfl⟩)
    · rintro ⟨hxQB, hxmax⟩
      have hxB : x ∈ B := by
        change x ∈ (facePolytope P hB).toSet at hxQB
        rwa [facePolytope_toSet P hB] at hxQB
      refine ⟨hxB, ?_⟩
      apply hchar (q x) (by rw [hQT]; exact ⟨x, hxB, rfl⟩)
      intro y hyQ
      rw [hQT] at hyQ
      obtain ⟨z, hzB, rfl⟩ := hyQ
      apply hxmax z
      change z ∈ (facePolytope P hB).toSet
      rwa [facePolytope_toSet P hB]
  exact isFace_of_facePolytope P hB hLiftQB

theorem residuo_passo_sinistro (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (H K : P.Flag) (i ip : Fin n)
    (hHK : ∀ j : Fin n, j ≠ i → K.face j = H.face j) :
    Relation.ReflTransGen
      (fun S T : P.Flag =>
        T = adjacentFlag P hfull S i ∨ T = adjacentFlag P hfull S ip)
      H K := by
  by_cases heq : K.face i = H.face i
  · have hflag : K = H := by
      apply flag_ext
      funext j
      by_cases hji : j = i
      · simpa [hji] using heq
      · exact hHK j hji
    rw [hflag]
  · have hadj : FlagAdjacentAt P H K i := ⟨hHK, heq⟩
    exact Relation.ReflTransGen.single
      (Or.inl (adjacentFlag_eq_of_isAdjacent P hfull i hadj))

theorem residuo_passo_destro (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (H K : P.Flag) (i ip : Fin n)
    (hHK : ∀ j : Fin n, j ≠ ip → K.face j = H.face j) :
    Relation.ReflTransGen
      (fun S T : P.Flag =>
        T = adjacentFlag P hfull S i ∨ T = adjacentFlag P hfull S ip)
      H K := by
  by_cases heq : K.face ip = H.face ip
  · have hflag : K = H := by
      apply flag_ext
      funext j
      by_cases hjip : j = ip
      · simpa [hjip] using heq
      · exact hHK j hjip
    rw [hflag]
  · have hadj : FlagAdjacentAt P H K ip := ⟨hHK, heq⟩
    exact Relation.ReflTransGen.single
      (Or.inr (adjacentFlag_eq_of_isAdjacent P hfull ip hadj))

theorem residuo_salto_tre_connesso (P : ConvexPolytope n)
    {A B : Set (E n)} (hA : P.IsFace A) (hB : P.IsFace B) (hAB : A ⊂ B)
    (hrank : faceDim B = faceDim A + 3)
    {X X' : Set (E n)} (hX : P.IsFace X) (hX' : P.IsFace X')
    (hAX : A ⊂ X) (hXB : X ⊂ B) (hAX' : A ⊂ X') (hX'B : X' ⊂ B)
    (hdX : faceDim X = faceDim A + 2) (hdX' : faceDim X' = faceDim A + 2) :
    Relation.ReflTransGen
      (fun Y Z : Set (E n) =>
        P.IsFace Y ∧ P.IsFace Z ∧ A ⊂ Y ∧ A ⊂ Z ∧ Y ⊂ B ∧ Z ⊂ B ∧
          faceDim Y = faceDim A + 2 ∧ faceDim Z = faceDim A + 2 ∧
          ∃ R : Set (E n), P.IsFace R ∧ A ⊂ R ∧ R ⊂ Y ∧ R ⊂ Z ∧
            faceDim R = faceDim A + 1)
      X X' := by
  classical
  let U : Submodule ℝ (E n) := vectorSpan ℝ A
  let W : Submodule ℝ (E n) := vectorSpan ℝ B
  let V : Submodule ℝ (E n) := U.orthogonal ⊓ W
  have hUW : U ≤ W := vectorSpan_mono ℝ hAB.1
  have hdimV : Module.finrank ℝ V = 3 := by
    have hadd := Submodule.finrank_add_inf_finrank_orthogonal hUW
    change Module.finrank ℝ U + Module.finrank ℝ V =
      Module.finrank ℝ W at hadd
    change Module.finrank ℝ W = Module.finrank ℝ U + 3 at hrank
    omega
  let e : V ≃L[ℝ] E 3 := ContinuousLinearEquiv.ofFinrankEq (by
    rw [hdimV, finrank_euclideanSpace]
    simp)
  let q : E n →L[ℝ] E 3 :=
    e.toContinuousLinearMap.comp V.orthogonalProjectionOnto
  let QB := facePolytope P hB
  let Q := linearImagePolytope QB q
  have hQT : Q.toSet = q '' B := by
    rw [linearImagePolytope_toSet, facePolytope_toSet P hB]
  have himage_face : ∀ {C : Set (E n)}, P.IsFace C → A ⊆ C → C ⊆ B →
      Q.IsFace (q '' C) := by
    intro C hC hAC hCB
    simpa [U, W, V, q, QB, Q] using
      (relative_image_isFace P hA hB hC hAB.1 hAC hCB e)
  have hsaturated : ∀ {C : Set (E n)}, P.IsFace C → A ⊆ C → C ⊆ B →
      ∀ x ∈ B, x ∈ q ⁻¹' (q '' C) → x ∈ C := by
    intro C hC hAC hCB
    simpa [U, W, V, q] using
      (relative_image_saturated P hA hB hC hAB.1 hAC hCB e)
  have hstrict_image : ∀ {C D : Set (E n)}, P.IsFace C →
      A ⊆ C → C ⊂ D → D ⊆ B → q '' C ⊂ q '' D := by
    intro C D hC hAC hCD hDB
    refine ⟨Set.image_mono hCD.1, ?_⟩
    intro hback
    obtain ⟨d, hdD, hdC⟩ := Set.exists_of_ssubset hCD
    apply hdC
    apply hsaturated hC hAC (hCD.1.trans hDB) d (hDB hdD)
    exact hback ⟨d, hdD, rfl⟩
  obtain ⟨a, haA⟩ := hA.2
  have hqA : ∀ z ∈ A, q z = q a := by
    intro z hzA
    have hzaU : z - a ∈ U := vsub_mem_vectorSpan ℝ hzA haA
    have hzaW : z - a ∈ W := hUW hzaU
    have hproj : V.starProjection z = V.starProjection a :=
      (relative_starProjection_fiber hUW hzaW).mpr hzaU
    change e (V.orthogonalProjectionOnto z) =
      e (V.orthogonalProjectionOnto a)
    apply congrArg e
    exact Subtype.ext hproj
  have hAimage : q '' A = ({q a} : Set (E 3)) := by
    ext y
    constructor
    · rintro ⟨z, hzA, rfl⟩
      exact Set.mem_singleton_iff.mpr (hqA z hzA)
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      exact ⟨a, haA, hy.symm⟩
  obtain ⟨C, hC, hAC, hCX, hdC⟩ :=
    faccia_intermedia P hA hX hAX (by exact hdX)
  obtain ⟨C', hC', hAC', hC'X', hdC'⟩ :=
    faccia_intermedia P hA hX' hAX' (by exact hdX')
  have hAq := himage_face hA (Subset.rfl) hAB.1
  have hCq := himage_face hC hAC.1 (hCX.1.trans hXB.1)
  have hC'q := himage_face hC' hAC'.1 (hC'X'.1.trans hX'B.1)
  have hXq := himage_face hX hAX.1 hXB.1
  have hX'q := himage_face hX' hAX'.1 hX'B.1
  have hqAC : q '' A ⊂ q '' C :=
    hstrict_image hA (Subset.rfl) hAC (hCX.1.trans hXB.1)
  have hqCX : q '' C ⊂ q '' X :=
    hstrict_image hC hAC.1 hCX hXB.1
  have hqXB : q '' X ⊂ Q.toSet := by
    rw [hQT]
    exact hstrict_image hX hAX.1 hXB (Subset.rfl)
  have hqAC' : q '' A ⊂ q '' C' :=
    hstrict_image hA (Subset.rfl) hAC' (hC'X'.1.trans hX'B.1)
  have hqC'X' : q '' C' ⊂ q '' X' :=
    hstrict_image hC' hAC'.1 hC'X' hX'B.1
  have hqX'B : q '' X' ⊂ Q.toSet := by
    rw [hQT]
    exact hstrict_image hX' hAX'.1 hX'B (Subset.rfl)
  have hdAq : faceDim (q '' A) = 0 := by
    rw [hAimage, faceDim_singleton]
  have hdCq_lt := faceDim_lt_of_ssubset Q hAq hCq hqAC
  have hdXq_lt := faceDim_lt_of_ssubset Q hCq hXq hqCX
  have hdQ_lt := faceDim_lt_of_ssubset Q hXq (toSet_isFace Q) hqXB
  have hdQ_le : faceDim Q.toSet ≤ 3 := by
    unfold faceDim
    calc
      Module.finrank ℝ (vectorSpan ℝ Q.toSet) ≤
          Module.finrank ℝ (E 3) := (vectorSpan ℝ Q.toSet).finrank_le
      _ = 3 := by rw [finrank_euclideanSpace]; simp
  have hdQT : faceDim Q.toSet = 3 := by omega
  have hfullQ : Q.IsFullDim := hdQT
  have hdXq : faceDim (q '' X) = 2 := by omega
  have hdC'q_lt := faceDim_lt_of_ssubset Q hAq hC'q hqAC'
  have hdX'q_lt := faceDim_lt_of_ssubset Q hC'q hX'q hqC'X'
  have hdQ'_lt := faceDim_lt_of_ssubset Q hX'q (toSet_isFace Q) hqX'B
  have hdX'q : faceDim (q '' X') = 2 := by omega
  have hqaX : q a ∈ q '' X := ⟨a, hAX.1 haA, rfl⟩
  have hqaX' : q a ∈ q '' X' := ⟨a, hAX'.1 haA, rfl⟩
  have hqaV : q a ∈ Q.vertices := by
    obtain ⟨v, hv⟩ := (facePolytope Q hAq).vertices_nonempty
    have hv' := Finset.mem_filter.mp hv
    have hvA : v ∈ q '' A := hv'.2
    rw [hAimage, Set.mem_singleton_iff] at hvA
    rw [hvA] at hv'
    exact hv'.1
  have hcam := ventaglio_connesso Q hfullQ hqaV
    hXq hdXq hqaX hX'q hdX'q hqaX'
  let lift : Set (E 3) → Set (E n) := fun Y => B ∩ q ⁻¹' Y
  have hlift_face : ∀ {Y : Set (E 3)}, Q.IsFace Y → P.IsFace (lift Y) := by
    intro Y hY
    simpa [U, W, V, q, QB, Q, lift] using
      (relative_lift_isFace P hA hB e hY)
  have hlift_image : ∀ {Y : Set (E 3)}, Y ⊆ Q.toSet → q '' lift Y = Y := by
    intro Y hYQ
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hyY
      have hyQ : y ∈ Q.toSet := hYQ hyY
      rw [hQT] at hyQ
      obtain ⟨x, hxB, rfl⟩ := hyQ
      exact ⟨x, ⟨hxB, hyY⟩, rfl⟩
  have hlift_mono : ∀ {Y Z : Set (E 3)}, Y ⊆ Z → lift Y ⊆ lift Z := by
    intro Y Z hYZ x hx
    exact ⟨hx.1, hYZ hx.2⟩
  have hlift_strict : ∀ {Y Z : Set (E 3)}, Y ⊆ Q.toSet → Z ⊆ Q.toSet →
      Y ⊂ Z → lift Y ⊂ lift Z := by
    intro Y Z hYQ hZQ hYZ
    refine ⟨hlift_mono hYZ.1, ?_⟩
    intro hback
    have himageBack : q '' lift Z ⊆ q '' lift Y := Set.image_mono hback
    rw [hlift_image hZQ, hlift_image hYQ] at himageBack
    exact hYZ.2 himageBack
  have hlift_original : ∀ {D : Set (E n)}, P.IsFace D → A ⊆ D → D ⊆ B →
      lift (q '' D) = D := by
    intro D hD hAD hDB
    apply Set.Subset.antisymm
    · intro x hx
      exact hsaturated hD hAD hDB x hx.1 hx.2
    · intro x hxD
      exact ⟨hDB hxD, ⟨x, hxD, rfl⟩⟩
  have hlift_top : lift Q.toSet = B := by
    apply Set.Subset.antisymm
    · exact fun _ hx => hx.1
    · intro x hxB
      refine ⟨hxB, ?_⟩
      rw [hQT]
      exact ⟨x, hxB, rfl⟩
  let Valid : Set (E 3) → Prop := fun Y =>
    Q.IsFace Y ∧ faceDim Y = 2 ∧ q a ∈ Y
  have hstartValid : Valid (q '' X) := ⟨hXq, hdXq, hqaX⟩
  have hend_valid : ∀ {Y : Set (E 3)},
      Relation.ReflTransGen
        (fun S T => (Q.IsFace T ∧ faceDim T = 2 ∧ q a ∈ T) ∧
          SpigoloComune Q (q a) S T)
        (q '' X) Y → Valid Y := by
    intro Y hpath
    induction hpath with
    | refl => exact hstartValid
    | tail _ hstep _ => exact hstep.1
  let Rel : Set (E n) → Set (E n) → Prop := fun Y Z =>
    P.IsFace Y ∧ P.IsFace Z ∧ A ⊂ Y ∧ A ⊂ Z ∧
      Y ⊂ B ∧ Z ⊂ B ∧
      faceDim Y = faceDim A + 2 ∧ faceDim Z = faceDim A + 2 ∧
      ∃ R : Set (E n), P.IsFace R ∧ A ⊂ R ∧ R ⊂ Y ∧ R ⊂ Z ∧
        faceDim R = faceDim A + 1
  have hlift_step : ∀ {Y Z : Set (E 3)}, Valid Y →
      ((Q.IsFace Z ∧ faceDim Z = 2 ∧ q a ∈ Z) ∧
        SpigoloComune Q (q a) Y Z) →
      Rel (lift Y) (lift Z) := by
    intro Y Z hY hstep
    change Q.IsFace Y ∧ faceDim Y = 2 ∧ q a ∈ Y at hY
    obtain ⟨hZ, hsp⟩ := hstep
    obtain ⟨δ, hδ, hdδ, hqaδ, hδY, hδZ⟩ := hsp
    have hYsub : Y ⊆ Q.toSet := face_subset_toSet Q hY.1
    have hZsub : Z ⊆ Q.toSet := face_subset_toSet Q hZ.1
    have hδsub : δ ⊆ Q.toSet := face_subset_toSet Q hδ
    have hAqsubδ : q '' A ⊆ δ := by
      rw [hAimage]
      exact Set.singleton_subset_iff.mpr hqaδ
    have hAqδ : q '' A ⊂ δ := by
      refine ⟨hAqsubδ, ?_⟩
      intro hback
      have heq : δ = q '' A := Set.Subset.antisymm hback hAqsubδ
      rw [heq, hdAq] at hdδ
      omega
    have hδYstrict : δ ⊂ Y := by
      refine ⟨hδY, ?_⟩
      intro hYδ
      have heq : Y = δ := Set.Subset.antisymm hYδ hδY
      have hdY := hY.2.1
      rw [heq, hdδ] at hdY
      omega
    have hδZstrict : δ ⊂ Z := by
      refine ⟨hδZ, ?_⟩
      intro hZδ
      have heq : Z = δ := Set.Subset.antisymm hZδ hδZ
      have hdZ := hZ.2.1
      rw [heq, hdδ] at hdZ
      omega
    have hYtop : Y ⊂ Q.toSet := by
      refine ⟨hYsub, ?_⟩
      intro htopY
      have heq : Y = Q.toSet := Set.Subset.antisymm hYsub htopY
      have hdY := hY.2.1
      rw [heq, hdQT] at hdY
      omega
    have hZtop : Z ⊂ Q.toSet := by
      refine ⟨hZsub, ?_⟩
      intro htopZ
      have heq : Z = Q.toSet := Set.Subset.antisymm hZsub htopZ
      have hdZ := hZ.2.1
      rw [heq, hdQT] at hdZ
      omega
    have hLAδ : A ⊂ lift δ := by
      rw [← hlift_original hA (Subset.rfl) hAB.1]
      exact hlift_strict (face_subset_toSet Q hAq) hδsub hAqδ
    have hLδY : lift δ ⊂ lift Y :=
      hlift_strict hδsub hYsub hδYstrict
    have hLδZ : lift δ ⊂ lift Z :=
      hlift_strict hδsub hZsub hδZstrict
    have hLYB : lift Y ⊂ B := by
      rw [← hlift_top]
      exact hlift_strict hYsub (Subset.rfl) hYtop
    have hLZB : lift Z ⊂ B := by
      rw [← hlift_top]
      exact hlift_strict hZsub (Subset.rfl) hZtop
    have hLδ := hlift_face hδ
    have hLY := hlift_face hY.1
    have hLZ := hlift_face hZ.1
    have hdAδ := faceDim_lt_of_ssubset P hA hLδ hLAδ
    have hdδY := faceDim_lt_of_ssubset P hLδ hLY hLδY
    have hdYB := faceDim_lt_of_ssubset P hLY hB hLYB
    have hdδZ := faceDim_lt_of_ssubset P hLδ hLZ hLδZ
    have hdZB := faceDim_lt_of_ssubset P hLZ hB hLZB
    have hdLδ : faceDim (lift δ) = faceDim A + 1 := by omega
    have hdLY : faceDim (lift Y) = faceDim A + 2 := by omega
    have hdLZ : faceDim (lift Z) = faceDim A + 2 := by omega
    exact ⟨hLY, hLZ, hLAδ.trans hLδY, hLAδ.trans hLδZ,
      hLYB, hLZB, hdLY, hdLZ,
      lift δ, hLδ, hLAδ, hLδY, hLδZ, hdLδ⟩
  have valid_path : ∀ {Y Z : Set (E 3)}, Valid Y →
      Relation.ReflTransGen
        (fun S T => (Q.IsFace T ∧ faceDim T = 2 ∧ q a ∈ T) ∧
          SpigoloComune Q (q a) S T) Y Z → Valid Z := by
    intro Y Z hY hpath
    induction hpath with
    | refl => exact hY
    | tail _ hstep _ => exact hstep.1
  have transfer_path : ∀ {Y Z : Set (E 3)}, Valid Y →
      (hpath : Relation.ReflTransGen
        (fun S T => (Q.IsFace T ∧ faceDim T = 2 ∧ q a ∈ T) ∧
          SpigoloComune Q (q a) S T) Y Z) →
      Relation.ReflTransGen Rel (lift Y) (lift Z) := by
    intro Y Z hY hpath
    induction hpath with
    | refl => exact Relation.ReflTransGen.refl
    | @tail D E hprev hstep ih =>
        exact Relation.ReflTransGen.tail ih
          (hlift_step (valid_path hY hprev) hstep)
  have hlift_cam : Relation.ReflTransGen Rel (lift (q '' X)) (lift (q '' X')) :=
    transfer_path hstartValid hcam
  change Relation.ReflTransGen Rel X X'
  rw [← hlift_original hX hAX.1 hXB.1,
    ← hlift_original hX' hAX'.1 hX'B.1]
  exact hlift_cam

theorem residuo_rango_tre_connesso (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (F G : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    (houtside : ∀ k : Fin n, k ≠ i → (k : ℕ) ≠ (i : ℕ) + 1 →
      F.face k = G.face k) :
    Relation.ReflTransGen
      (fun X Y : P.Flag =>
        Y = adjacentFlag P hfull X i ∨
        Y = adjacentFlag P hfull X ⟨(i : ℕ) + 1, hi⟩)
      F G := by
  classical
  let ip : Fin n := ⟨(i : ℕ) + 1, hi⟩
  have hipval : (ip : ℕ) = (i : ℕ) + 1 := rfl
  by_cases hi0 : (i : ℕ) = 0
  · have hiplt : i < ip := by
      rw [Fin.lt_def]
      omega
    obtain ⟨B, hB, hdB, hFipB, hBsub, hDB⟩ :=
      faccia_sopra P hfull F ip
    have hGipB : G.face ip ⊂ B := by
      apply hDB (G.face ip) (G.isFace ip) (G.dim_eq ip)
      intro j hj
      have hji : j ≠ i := ne_of_gt (lt_trans hiplt hj)
      have hjipval : (j : ℕ) ≠ (i : ℕ) + 1 := by
        intro hval
        have hjip : j = ip := Fin.ext hval
        rw [hjip] at hj
        exact (lt_irrefl ip) hj
      rw [houtside j hji hjipval]
      exact G.strict_mono ip j hj
    obtain ⟨v, hFv⟩ := faccia_dim0_singoletto (F.isFace i).2 (by
      rw [F.dim_eq, hi0])
    obtain ⟨w, hGw⟩ := faccia_dim0_singoletto (G.isFace i).2 (by
      rw [G.dim_eq, hi0])
    have hvP : v ∈ P.vertices := by
      obtain ⟨u, hu⟩ := (facePolytope P (F.isFace i)).vertices_nonempty
      have hu' : u ∈ P.vertices ∧ u ∈ F.face i := Finset.mem_filter.mp hu
      have huv : u = v := by
        rw [hFv] at hu'
        exact Set.mem_singleton_iff.mp hu'.2
      exact huv ▸ hu'.1
    have hwP : w ∈ P.vertices := by
      obtain ⟨u, hu⟩ := (facePolytope P (G.isFace i)).vertices_nonempty
      have hu' : u ∈ P.vertices ∧ u ∈ G.face i := Finset.mem_filter.mp hu
      have huw : u = w := by
        rw [hGw] at hu'
        exact Set.mem_singleton_iff.mp hu'.2
      exact huw ▸ hu'.1
    have hvB : v ∈ B := by
      apply hFipB.1
      apply (F.strict_mono i ip hiplt).1
      rw [hFv]
      exact Set.mem_singleton v
    have hwB : w ∈ B := by
      apply hGipB.1
      apply (G.strict_mono i ip hiplt).1
      rw [hGw]
      exact Set.mem_singleton w
    let Q := facePolytope P hB
    have hvQ : v ∈ Q.vertices := by
      change v ∈ P.vertices.filter (· ∈ B)
      exact Finset.mem_filter.mpr ⟨hvP, hvB⟩
    have hwQ : w ∈ Q.vertices := by
      change w ∈ P.vertices.filter (· ∈ B)
      exact Finset.mem_filter.mpr ⟨hwP, hwB⟩
    have hQdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = 2 := by
      change faceDim Q.toSet = 2
      rw [facePolytope_toSet P hB, hdB]
      omega
    have hverts := poligono_connesso Q hQdim hvQ hwQ
    let VertRel : E n → E n → Prop := fun p q =>
      q ∈ Q.vertices ∧ p ≠ q ∧
        ∃ e : Set (E n), Q.IsFace e ∧ faceDim e = 1 ∧ p ∈ e ∧ q ∈ e
    let MoveRel : P.Flag → P.Flag → Prop := fun H K =>
      K = adjacentFlag P hfull H i ∨ K = adjacentFlag P hfull H ip
    change Relation.ReflTransGen VertRel v w at hverts
    have transfer : ∀ {q : E n}, Relation.ReflTransGen VertRel v q →
        ∃ H : P.Flag, Relation.ReflTransGen MoveRel F H ∧
          H.face i = {q} ∧
          ∀ k : Fin n, k ≠ i → k ≠ ip → H.face k = F.face k := by
      intro q hpath
      induction hpath with
      | refl =>
          exact ⟨F, Relation.ReflTransGen.refl, hFv, fun _ _ _ => rfl⟩
      | @tail p q hprev hstep ih =>
          obtain ⟨H, hFH, hHi, hHout⟩ := ih
          obtain ⟨hqQ, _hpq, e, heQ, hde, hpe, hqe⟩ := hstep
          have heP : P.IsFace e := isFace_of_facePolytope P hB heQ
          have heBsub : e ⊆ B := by
            rw [← facePolytope_toSet P hB]
            exact face_subset_toSet Q heQ
          have heB : e ⊂ B := by
            refine ⟨heBsub, ?_⟩
            intro hBe
            have heq : e = B := Set.Subset.antisymm heBsub hBe
            rw [heq, hdB] at hde
            omega
          have hpE : H.face i ⊂ e := by
            rw [hHi]
            refine (Set.singleton_subset_iff.mpr hpe).ssubset_of_ne ?_
            intro heq
            have hdim := congrArg faceDim heq
            rw [faceDim_singleton, hde] at hdim
            omega
          have hdeip : faceDim e = (ip : ℕ) := by
            rw [hde]
            omega
          have hsottoE : ∀ j : Fin n, j < ip → H.face j ⊂ e := by
            apply catena_sotto P H (i := ip) (im := i) (by omega)
            exact hpE
          have hsopraE : ∀ j : Fin n, ip < j → e ⊂ H.face j := by
            intro j hj
            have hji : j ≠ i := ne_of_gt (lt_trans hiplt hj)
            have hjip : j ≠ ip := ne_of_gt hj
            rw [hHout j hji hjip]
            exact ssubset_of_ssubset_of_subset heB (hBsub j hj)
          let H₁ : P.Flag := sostituisci P H ip e heP hdeip hsottoE hsopraE
          have hHH₁ : Relation.ReflTransGen MoveRel H H₁ := by
            apply residuo_passo_destro P hfull H H₁ i ip
            intro j hjip
            exact sostituisci_face_ne P H ip e heP hdeip hsottoE hsopraE hjip
          have hH₁e : H₁.face ip = e := sostituisci_face_self ..
          have hqQ' := hqQ
          change q ∈ P.vertices.filter (· ∈ B) at hqQ'
          have hqP : q ∈ P.vertices := (Finset.mem_filter.mp hqQ').1
          have hqFace : P.IsFace ({q} : Set (E n)) := vertex_isFace P hqP
          have hqdim : faceDim ({q} : Set (E n)) = (i : ℕ) := by
            rw [faceDim_singleton, hi0]
          have hqE : ({q} : Set (E n)) ⊂ e := by
            refine (Set.singleton_subset_iff.mpr hqe).ssubset_of_ne ?_
            intro heq
            have hdim := congrArg faceDim heq
            rw [faceDim_singleton, hde] at hdim
            omega
          have hsottoQ : ∀ j : Fin n, j < i → H₁.face j ⊂ ({q} : Set (E n)) := by
            intro j hj
            rw [Fin.lt_def] at hj
            omega
          have hsopraQ : ∀ j : Fin n, i < j → ({q} : Set (E n)) ⊂ H₁.face j := by
            apply catena_sopra P H₁ (i := i) (ip := ip) (by omega)
            rw [hH₁e]
            exact hqE
          let H₂ : P.Flag := sostituisci P H₁ i ({q} : Set (E n)) hqFace
            hqdim hsottoQ hsopraQ
          have hH₁H₂ : Relation.ReflTransGen MoveRel H₁ H₂ := by
            apply residuo_passo_sinistro P hfull H₁ H₂ i ip
            intro j hji
            exact sostituisci_face_ne P H₁ i ({q} : Set (E n)) hqFace
              hqdim hsottoQ hsopraQ hji
          refine ⟨H₂, hFH.trans (hHH₁.trans hH₁H₂), ?_, ?_⟩
          · exact sostituisci_face_self ..
          · intro k hki hkip
            rw [sostituisci_face_ne P H₁ i ({q} : Set (E n)) hqFace
                hqdim hsottoQ hsopraQ hki,
              sostituisci_face_ne P H ip e heP hdeip hsottoE hsopraE hkip]
            exact hHout k hki hkip
    obtain ⟨H, hFH, hHi, hHout⟩ := transfer hverts
    have hHG : Relation.ReflTransGen MoveRel H G := by
      apply residuo_passo_destro P hfull H G i ip
      intro k hkip
      by_cases hki : k = i
      · rw [hki, hHi, hGw]
      · rw [hHout k hki hkip]
        exact (houtside k hki (by
          intro hkval
          exact hkip (Fin.ext hkval))).symm
    exact hFH.trans hHG
  · obtain ⟨iv, hiv⟩ : ∃ iv : ℕ, (i : ℕ) = iv + 1 :=
      ⟨(i : ℕ) - 1, by omega⟩
    have hivn : iv < n := by omega
    let im : Fin n := ⟨iv, hivn⟩
    have him : (im : ℕ) + 1 = (i : ℕ) := by
      change iv + 1 = (i : ℕ)
      omega
    have himlt : im < i := by rw [Fin.lt_def]; omega
    have hiplt : i < ip := by rw [Fin.lt_def]; omega
    let A : Set (E n) := F.face im
    obtain ⟨B, hB, hdB, hFipB, hBsub, hDB⟩ :=
      faccia_sopra P hfull F ip
    have hFGim : F.face im = G.face im := by
      apply houtside im
      · intro h
        have := congrArg Fin.val h
        omega
      · omega
    have hGipB : G.face ip ⊂ B := by
      apply hDB (G.face ip) (G.isFace ip) (G.dim_eq ip)
      intro j hj
      have hji : j ≠ i := by
        intro h
        rw [h] at hj
        exact (not_lt_of_ge (le_of_lt hiplt)) hj
      have hjipval : (j : ℕ) ≠ (i : ℕ) + 1 := by
        intro hval
        have hjip : j = ip := Fin.ext hval
        rw [hjip] at hj
        exact (lt_irrefl ip) hj
      rw [houtside j hji hjipval]
      exact G.strict_mono ip j hj
    have hAGip : A ⊂ G.face ip := by
      change F.face im ⊂ G.face ip
      rw [hFGim]
      exact G.strict_mono im ip (lt_trans himlt hiplt)
    have hAFip : A ⊂ F.face ip := F.strict_mono im ip (lt_trans himlt hiplt)
    have hAB : A ⊂ B := hAFip.trans hFipB
    have hrankAB : faceDim B = faceDim A + 3 := by
      rw [hdB, F.dim_eq]
      omega
    have hdFip : faceDim (F.face ip) = faceDim A + 2 := by
      rw [F.dim_eq, F.dim_eq]
      omega
    have hdGip : faceDim (G.face ip) = faceDim A + 2 := by
      rw [G.dim_eq, F.dim_eq]
      omega
    have hfaces := residuo_salto_tre_connesso P (F.isFace im) hB hAB
      hrankAB (F.isFace ip) (G.isFace ip) hAFip hFipB hAGip hGipB
      hdFip hdGip
    let FaceRel : Set (E n) → Set (E n) → Prop := fun Y Z =>
      P.IsFace Y ∧ P.IsFace Z ∧ A ⊂ Y ∧ A ⊂ Z ∧
        Y ⊂ B ∧ Z ⊂ B ∧
        faceDim Y = faceDim A + 2 ∧ faceDim Z = faceDim A + 2 ∧
        ∃ R : Set (E n), P.IsFace R ∧ A ⊂ R ∧ R ⊂ Y ∧ R ⊂ Z ∧
          faceDim R = faceDim A + 1
    let MoveRel : P.Flag → P.Flag → Prop := fun H K =>
      K = adjacentFlag P hfull H i ∨ K = adjacentFlag P hfull H ip
    change Relation.ReflTransGen FaceRel (F.face ip) (G.face ip) at hfaces
    have transfer : ∀ {Y : Set (E n)},
        Relation.ReflTransGen FaceRel (F.face ip) Y →
        ∃ H : P.Flag, Relation.ReflTransGen MoveRel F H ∧
          H.face ip = Y ∧
          ∀ k : Fin n, k ≠ i → k ≠ ip → H.face k = F.face k := by
      intro Y hpath
      induction hpath with
      | refl =>
          exact ⟨F, Relation.ReflTransGen.refl, rfl, fun _ _ _ => rfl⟩
      | @tail Y Z hprev hstep ih =>
          obtain ⟨H, hFH, hHip, hHout⟩ := ih
          obtain ⟨_hY, hZ, _hAY, _hAZ, _hYB, hZB, _hdY, hdZ,
            R, hR, hAR, hRY, hRZ, hdR⟩ := hstep
          have hHim : H.face im = A := by
            rw [hHout im (ne_of_lt himlt) (by
              intro h
              have := congrArg Fin.val h
              omega)]
          have hdRi : faceDim R = (i : ℕ) := by
            rw [hdR, F.dim_eq]
            omega
          have hsottoR : ∀ j : Fin n, j < i → H.face j ⊂ R := by
            apply catena_sotto P H him
            rw [hHim]
            exact hAR
          have hsopraR : ∀ j : Fin n, i < j → R ⊂ H.face j := by
            apply catena_sopra P H (ip := ip) (by omega)
            rw [hHip]
            exact hRY
          let H₁ : P.Flag := sostituisci P H i R hR hdRi hsottoR hsopraR
          have hHH₁ : Relation.ReflTransGen MoveRel H H₁ := by
            apply residuo_passo_sinistro P hfull H H₁ i ip
            intro j hji
            exact sostituisci_face_ne P H i R hR hdRi hsottoR hsopraR hji
          have hH₁R : H₁.face i = R := sostituisci_face_self ..
          have hdZi : faceDim Z = (ip : ℕ) := by
            rw [hdZ, F.dim_eq]
            omega
          have hsottoZ : ∀ j : Fin n, j < ip → H₁.face j ⊂ Z := by
            apply catena_sotto P H₁ (im := i) (by omega)
            rw [hH₁R]
            exact hRZ
          have hsopraZ : ∀ j : Fin n, ip < j → Z ⊂ H₁.face j := by
            intro j hj
            have hji : j ≠ i := ne_of_gt (lt_trans hiplt hj)
            have hjip : j ≠ ip := ne_of_gt hj
            rw [sostituisci_face_ne P H i R hR hdRi hsottoR hsopraR hji,
              hHout j hji hjip]
            exact ssubset_of_ssubset_of_subset hZB (hBsub j hj)
          let H₂ : P.Flag := sostituisci P H₁ ip Z hZ hdZi hsottoZ hsopraZ
          have hH₁H₂ : Relation.ReflTransGen MoveRel H₁ H₂ := by
            apply residuo_passo_destro P hfull H₁ H₂ i ip
            intro j hjip
            exact sostituisci_face_ne P H₁ ip Z hZ hdZi hsottoZ hsopraZ hjip
          refine ⟨H₂, hFH.trans (hHH₁.trans hH₁H₂), ?_, ?_⟩
          · exact sostituisci_face_self ..
          · intro k hki hkip
            rw [sostituisci_face_ne P H₁ ip Z hZ hdZi hsottoZ hsopraZ hkip,
              sostituisci_face_ne P H i R hR hdRi hsottoR hsopraR hki]
            exact hHout k hki hkip
    obtain ⟨H, hFH, hHip, hHout⟩ := transfer hfaces
    have hHG : Relation.ReflTransGen MoveRel H G := by
      apply residuo_passo_sinistro P hfull H G i ip
      intro k hki
      by_cases hkip : k = ip
      · rw [hkip, hHip]
      · rw [hHout k hki hkip]
        exact (houtside k hki (by
          intro hkval
          exact hkip (Fin.ext hkval))).symm
    exact hFH.trans hHG

end LeanEval.Geometry.PlatonicClassification
