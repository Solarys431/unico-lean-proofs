import UnicoProofs.Platonici.Ortoplesse
import UnicoProofs.Platonici.Diamante
import UnicoProofs.Platonici.PerturbazioneFinita

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- The two vertices over one coordinate are opposites. -/
theorem vertOrto_not_eq_neg {d : ℕ} (i : Fin d) (b : Bool) :
    vertOrto (i, !b) = -vertOrto (i, b) := by
  ext k
  by_cases h : k = i <;> cases b <;> simp [vertOrto_apply, h]

open Classical in
/-- A proper face of the cross-polytope contains at most one of the two
vertices over each coordinate. -/
theorem ortoplesse_face_no_antipodi (d : ℕ) (hd : 1 ≤ d)
    {f : Set (E d)} (hf : (ortoplesse d hd).IsFace f) (hproper : faceDim f < d)
    {i : Fin d} {b c : Bool}
    (hb : vertOrto (i, b) ∈ (ortoplesse d hd).vertices.filter (· ∈ f))
    (hc : vertOrto (i, c) ∈ (ortoplesse d hd).vertices.filter (· ∈ f)) :
    b = c := by
  by_contra hbc
  let P := ortoplesse d hd
  have hbF : vertOrto (i, b) ∈ f := (Finset.mem_filter.mp hb).2
  have hcF : vertOrto (i, c) ∈ f := (Finset.mem_filter.mp hc).2
  obtain ⟨l, hmem, hchar⟩ := espositore_di_faccia P hf
  have hbdata := hmem (vertOrto (i, b)) hbF
  have hcdata := hmem (vertOrto (i, c)) hcF
  have hsame : l (vertOrto (i, b)) = l (vertOrto (i, c)) :=
    le_antisymm (hcdata.2 _ hbdata.1) (hbdata.2 _ hcdata.1)
  have hopp : vertOrto (i, c) = -vertOrto (i, b) := by
    have hcnot : c = !b := by cases b <;> cases c <;> simp_all
    rw [hcnot, vertOrto_not_eq_neg]
  have hneg : l (vertOrto (i, c)) = -l (vertOrto (i, b)) := by
    rw [hopp, map_neg]
  have hbzero : l (vertOrto (i, b)) = 0 := by linarith
  have hall : ∀ v ∈ P.vertices, v ∈ f := by
    intro v hv
    have hv' : v ∈ verticiOrto d := hv
    rw [mem_verticiOrto] at hv'
    obtain ⟨⟨j, s⟩, rfl⟩ := hv'
    have hvP : vertOrto (j, s) ∈ P.toSet :=
      subset_convexHull ℝ _ (by
        exact_mod_cast (mem_verticiOrto.mpr ⟨(j, s), rfl⟩))
    have hopV : vertOrto (j, !s) ∈ P.vertices := by
      exact mem_verticiOrto.mpr ⟨(j, !s), rfl⟩
    have hopP : vertOrto (j, !s) ∈ P.toSet :=
      subset_convexHull ℝ _ (by exact_mod_cast hopV)
    have hvle : l (vertOrto (j, s)) ≤ 0 := by
      simpa [hbzero] using hbdata.2 (vertOrto (j, s)) hvP
    have hople : l (vertOrto (j, !s)) ≤ 0 := by
      simpa [hbzero] using hbdata.2 (vertOrto (j, !s)) hopP
    have hopval : l (vertOrto (j, !s)) = -l (vertOrto (j, s)) := by
      rw [vertOrto_not_eq_neg, map_neg]
    have hvzero : l (vertOrto (j, s)) = 0 := by linarith
    apply hchar (vertOrto (j, s)) hvP
    intro z hz
    calc
      l z ≤ l (vertOrto (i, b)) := hbdata.2 z hz
      _ = l (vertOrto (j, s)) := by rw [hbzero, hvzero]
  have hfP : f ⊆ P.toSet := fun y hy => (hmem y hy).1
  have hPf : P.toSet ⊆ f := by
    apply convexHull_min
    · intro v hv
      exact hall v (by exact_mod_cast hv)
    · exact hf.1.convex (convex_convexHull ℝ _)
  have heq : f = P.toSet := Set.Subset.antisymm hfP hPf
  have hdim : faceDim f = d := by
    rw [heq]
    exact ortoplesse_isFullDim d hd
  omega

open Classical in
/-- The vertices contained in a proper face of the cross-polytope are
linearly, hence affinely, independent. -/
theorem ortoplesse_face_affineIndependent (d : ℕ) (hd : 1 ≤ d)
    {f : Set (E d)} (hf : (ortoplesse d hd).IsFace f) (hproper : faceDim f < d) :
    AffineIndependent ℝ
      ((↑) : {x // x ∈
        (((ortoplesse d hd).vertices.filter (· ∈ f) : Finset (E d)) : Set (E d))} →
        E d) := by
  let S : Finset (E d) := (ortoplesse d hd).vertices.filter (· ∈ f)
  apply LinearIndependent.affineIndependent
  rw [Fintype.linearIndependent_iff]
  intro g hsum x
  have hxvert : (x : E d) ∈ verticiOrto d := (Finset.mem_filter.mp x.property).1
  rw [mem_verticiOrto] at hxvert
  obtain ⟨⟨i, b⟩, hxeq⟩ := hxvert
  have hyzero : ∀ y : {x // x ∈ (S : Set (E d))}, y ≠ x → (y : E d) i = 0 := by
    intro y hyx
    have hyvert : (y : E d) ∈ verticiOrto d := (Finset.mem_filter.mp y.property).1
    rw [mem_verticiOrto] at hyvert
    obtain ⟨⟨j, c⟩, hyeq⟩ := hyvert
    rw [← hyeq]
    by_cases hij : i = j
    · subst j
      have hxbmem : vertOrto (i, b) ∈
          (ortoplesse d hd).vertices.filter (· ∈ f) := by
        rw [hxeq]
        exact x.property
      have hycmem : vertOrto (i, c) ∈
          (ortoplesse d hd).vertices.filter (· ∈ f) := by
        rw [hyeq]
        exact y.property
      have hbc : b = c := ortoplesse_face_no_antipodi d hd hf hproper
        (i := i) (b := b) (c := c) hxbmem hycmem
      exfalso
      apply hyx
      apply Subtype.ext
      calc
        (y : E d) = vertOrto (i, c) := hyeq.symm
        _ = vertOrto (i, b) := by rw [hbc]
        _ = (x : E d) := hxeq
    · simp [vertOrto_apply, hij]
  have hcoord := congrArg (fun z : E d => z i) hsum
  have hsum' : ∑ y, g y * (y : E d) i = 0 := by
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hcoord
  have hsingle : (∑ y, g y * (y : E d) i) = g x * (x : E d) i := by
    apply Finset.sum_eq_single x
    · intro y _ hyx
      rw [hyzero y hyx, mul_zero]
    · simp
  rw [hsingle] at hsum'
  have hxnonzero : (x : E d) i ≠ 0 := by
    rw [← hxeq]
    rw [vertOrto_self (i, b)]
    cases b <;> norm_num
  exact (mul_eq_zero.mp hsum').resolve_right hxnonzero

open Classical in
/-- Every proper face of the cross-polytope is a simplex. -/
theorem ortoplesse_face_card (d : ℕ) (hd : 1 ≤ d)
    {f : Set (E d)} (hf : (ortoplesse d hd).IsFace f) (hproper : faceDim f < d) :
    ((ortoplesse d hd).vertices.filter (· ∈ f)).card = faceDim f + 1 := by
  let S : Finset (E d) := (ortoplesse d hd).vertices.filter (· ∈ f)
  have hFS : f = convexHull ℝ (S : Set (E d)) := face_eq_hull_vertices _ hf
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hne := hf.2
    rw [hFS, h] at hne
    simp at hne
  have hSind : AffineIndependent ℝ
      ((↑) : {x // x ∈ (S : Set (E d))} → E d) := by
    simpa only [S] using ortoplesse_face_affineIndependent d hd hf hproper
  letI : Nonempty {x // x ∈ (S : Set (E d))} :=
    ⟨⟨hSne.choose, hSne.choose_spec⟩⟩
  have hdim := hSind.finrank_vectorSpan_add_one
  have hrange : Set.range ((↑) : {x // x ∈ (S : Set (E d))} → E d) =
      (S : Set (E d)) := Subtype.range_coe_subtype
  rw [hrange] at hdim
  have hdim' : Module.finrank ℝ (vectorSpan ℝ (S : Set (E d))) = faceDim f := by
    symm
    unfold faceDim
    rw [hFS, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
  rw [hdim'] at hdim
  change S.card = faceDim f + 1
  simpa using hdim.symm

def finPredSame {d : ℕ} (k : Fin d) (_hk : k.val ≠ 0) : Fin d :=
  ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩

@[simp] theorem finPredSame_val {d : ℕ} (k : Fin d) (hk : k.val ≠ 0) :
    (finPredSame k hk).val = k.val - 1 := rfl

open Classical in
noncomputable def ortoplesseFlagVertices (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) : Finset (E d) :=
  (ortoplesse d hd).vertices.filter (· ∈ F.face k)

open Classical in
noncomputable def ortoplesseFlagPrev (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) : Finset (E d) :=
  if hk : k.val = 0 then ∅ else
    ortoplesseFlagVertices d hd F (finPredSame k hk)

open Classical in
theorem ortoplesseFlagVertices_card (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) :
    (ortoplesseFlagVertices d hd F k).card = k.val + 1 := by
  have hproper : faceDim (F.face k) < d := by
    rw [F.dim_eq]
    exact k.isLt
  simpa [ortoplesseFlagVertices, F.dim_eq] using
    ortoplesse_face_card d hd (F.isFace k) hproper

open Classical in
theorem ortoplesseFlagVertices_mono (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) {i j : Fin d} (hij : i ≤ j) :
    ortoplesseFlagVertices d hd F i ⊆ ortoplesseFlagVertices d hd F j := by
  intro v hv
  rw [ortoplesseFlagVertices, Finset.mem_filter] at hv ⊢
  refine ⟨hv.1, ?_⟩
  rcases hij.eq_or_lt with rfl | hij
  · exact hv.2
  · exact (F.strict_mono i j hij).1 hv.2

open Classical in
theorem ortoplesseFlagStep_nonempty (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) :
    (ortoplesseFlagVertices d hd F k \ ortoplesseFlagPrev d hd F k).Nonempty := by
  by_cases hk : k.val = 0
  · have hc := ortoplesseFlagVertices_card d hd F k
    simpa [ortoplesseFlagPrev, hk] using
      (Finset.card_pos.mp (by omega : 0 < (ortoplesseFlagVertices d hd F k).card))
  · let p : Fin d := finPredSame k hk
    have hpk : p < k := by
      apply Fin.mk_lt_mk.mpr
      simp
      omega
    have hsub : ortoplesseFlagVertices d hd F p ⊆
        ortoplesseFlagVertices d hd F k :=
      ortoplesseFlagVertices_mono d hd F hpk.le
    have hcp := ortoplesseFlagVertices_card d hd F p
    have hck := ortoplesseFlagVertices_card d hd F k
    have hcdiff :
        (ortoplesseFlagVertices d hd F k \
          ortoplesseFlagVertices d hd F p).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, hcp, hck]
      simp [p]
      omega
    have hne : (ortoplesseFlagVertices d hd F k \
        ortoplesseFlagVertices d hd F p).Nonempty :=
      Finset.card_pos.mp (by omega)
    simpa [ortoplesseFlagPrev, hk, p] using hne

open Classical in
noncomputable def ortoplesseFlagNew (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) : E d :=
  (ortoplesseFlagStep_nonempty d hd F k).choose

open Classical in
theorem ortoplesseFlagNew_mem (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) :
    ortoplesseFlagNew d hd F k ∈ ortoplesseFlagVertices d hd F k :=
  (Finset.mem_sdiff.mp
    (ortoplesseFlagStep_nonempty d hd F k).choose_spec).1

open Classical in
theorem ortoplesseFlagNew_not_prev (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) :
    ortoplesseFlagNew d hd F k ∉ ortoplesseFlagPrev d hd F k :=
  (Finset.mem_sdiff.mp
    (ortoplesseFlagStep_nonempty d hd F k).choose_spec).2

open Classical in
theorem ortoplesseFlagNew_injective (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) :
    Function.Injective (ortoplesseFlagNew d hd F) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · have hj0 : j.val ≠ 0 := by omega
    let p : Fin d := finPredSame j hj0
    have hip : i ≤ p := by
      apply Fin.mk_le_mk.mpr
      omega
    have himem : ortoplesseFlagNew d hd F i ∈
        ortoplesseFlagVertices d hd F p :=
      ortoplesseFlagVertices_mono d hd F hip
        (ortoplesseFlagNew_mem d hd F i)
    have hjnot : ortoplesseFlagNew d hd F j ∉
        ortoplesseFlagVertices d hd F p := by
      simpa [ortoplesseFlagPrev, hj0, p] using
        ortoplesseFlagNew_not_prev d hd F j
    exact hjnot (hij ▸ himem)
  · have hi0 : i.val ≠ 0 := by omega
    let p : Fin d := finPredSame i hi0
    have hjp : j ≤ p := by
      apply Fin.mk_le_mk.mpr
      omega
    have hjmem : ortoplesseFlagNew d hd F j ∈
        ortoplesseFlagVertices d hd F p :=
      ortoplesseFlagVertices_mono d hd F hjp
        (ortoplesseFlagNew_mem d hd F j)
    have hinot : ortoplesseFlagNew d hd F i ∉
        ortoplesseFlagVertices d hd F p := by
      simpa [ortoplesseFlagPrev, hi0, p] using
        ortoplesseFlagNew_not_prev d hd F i
    exact hinot (hij.symm ▸ hjmem)

open Classical in
theorem ortoplesseFlagVertices_eq_image_Iic (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) :
    ortoplesseFlagVertices d hd F k =
      (Finset.Iic k).image (ortoplesseFlagNew d hd F) := by
  symm
  apply (Finset.eq_of_subset_of_card_le ?_ ?_)
  · intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    exact ortoplesseFlagVertices_mono d hd F (Finset.mem_Iic.mp hj)
      (ortoplesseFlagNew_mem d hd F j)
  · rw [Finset.card_image_of_injective _ (ortoplesseFlagNew_injective d hd F),
      ortoplesseFlagVertices_card d hd F k]
    simp

open Classical in
noncomputable def ortoplesseFlagCode (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) : Fin d × Bool :=
  (mem_verticiOrto.mp
    (show ortoplesseFlagNew d hd F k ∈ verticiOrto d from
      (Finset.mem_filter.mp (ortoplesseFlagNew_mem d hd F k)).1)).choose

open Classical in
theorem ortoplesseFlagCode_spec (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) :
    vertOrto (ortoplesseFlagCode d hd F k) = ortoplesseFlagNew d hd F k :=
  (mem_verticiOrto.mp
    (show ortoplesseFlagNew d hd F k ∈ verticiOrto d from
      (Finset.mem_filter.mp (ortoplesseFlagNew_mem d hd F k)).1)).choose_spec

open Classical in
theorem ortoplesseFlagCode_fst_injective (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) :
    Function.Injective (fun k => (ortoplesseFlagCode d hd F k).1) := by
  intro i j hij
  let k : Fin d := max i j
  have himem : vertOrto (ortoplesseFlagCode d hd F i) ∈
      (ortoplesse d hd).vertices.filter (· ∈ F.face k) := by
    rw [ortoplesseFlagCode_spec]
    have hmono := ortoplesseFlagVertices_mono d hd F (show i ≤ k from le_max_left _ _)
    exact hmono (ortoplesseFlagNew_mem d hd F i)
  have hjmem : vertOrto (ortoplesseFlagCode d hd F j) ∈
      (ortoplesse d hd).vertices.filter (· ∈ F.face k) := by
    rw [ortoplesseFlagCode_spec]
    have hmono := ortoplesseFlagVertices_mono d hd F (show j ≤ k from le_max_right _ _)
    exact hmono (ortoplesseFlagNew_mem d hd F j)
  have hproper : faceDim (F.face k) < d := by
    rw [F.dim_eq]
    exact k.isLt
  have hbool : (ortoplesseFlagCode d hd F i).2 =
      (ortoplesseFlagCode d hd F j).2 :=
    ortoplesse_face_no_antipodi d hd (F.isFace k) hproper
      (i := (ortoplesseFlagCode d hd F i).1)
      (b := (ortoplesseFlagCode d hd F i).2)
      (c := (ortoplesseFlagCode d hd F j).2) himem (by simpa [hij] using hjmem)
  apply ortoplesseFlagNew_injective d hd F
  rw [← ortoplesseFlagCode_spec d hd F i,
    ← ortoplesseFlagCode_spec d hd F j]
  exact congrArg vertOrto (Prod.ext hij hbool)

open Classical in
noncomputable def ortoplesseFlagIndexEquiv (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) : Equiv.Perm (Fin d) :=
  Equiv.ofBijective (fun k => (ortoplesseFlagCode d hd F k).1)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨ortoplesseFlagCode_fst_injective d hd F, rfl⟩)

@[simp] theorem ortoplesseFlagIndexEquiv_apply (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) :
    ortoplesseFlagIndexEquiv d hd F k = (ortoplesseFlagCode d hd F k).1 := rfl

open Classical in
noncomputable def ortoplesseFlagPerm (d : ℕ) (hd : 1 ≤ d)
    (F G : (ortoplesse d hd).Flag) : Equiv.Perm (Fin d) :=
  (ortoplesseFlagIndexEquiv d hd F).symm.trans
    (ortoplesseFlagIndexEquiv d hd G)

open Classical in
noncomputable def ortoplesseFlagSign (d : ℕ) (hd : 1 ≤ d)
    (F G : (ortoplesse d hd).Flag) (i : Fin d) : ({-1, 1} : Set ℝ) :=
  let k := (ortoplesseFlagIndexEquiv d hd F).symm i
  if (ortoplesseFlagCode d hd F k).2 = (ortoplesseFlagCode d hd G k).2 then
    ⟨1, by simp⟩ else ⟨-1, by simp⟩

open Classical in
theorem ortoplesseFlagIsom_new (d : ℕ) (hd : 1 ≤ d)
    (F G : (ortoplesse d hd).Flag) (k : Fin d) :
    segnoPerm d (ortoplesseFlagPerm d hd F G) (ortoplesseFlagSign d hd F G)
        (ortoplesseFlagNew d hd F k) =
      ortoplesseFlagNew d hd G k := by
  rw [← ortoplesseFlagCode_spec d hd F k,
    ← ortoplesseFlagCode_spec d hd G k]
  rcases hF : ortoplesseFlagCode d hd F k with ⟨i, b⟩
  rcases hG : ortoplesseFlagCode d hd G k with ⟨j, c⟩
  simp only [vertOrto, segnoPerm_apply, segnoLinear_single]
  have hi : ortoplesseFlagIndexEquiv d hd F k = i := by
    rw [ortoplesseFlagIndexEquiv_apply, hF]
  have hj : ortoplesseFlagIndexEquiv d hd G k = j := by
    rw [ortoplesseFlagIndexEquiv_apply, hG]
  have hperm : ortoplesseFlagPerm d hd F G i = j := by
    change ortoplesseFlagIndexEquiv d hd G
      ((ortoplesseFlagIndexEquiv d hd F).symm i) = j
    have hirank : (ortoplesseFlagIndexEquiv d hd F).symm i = k := by
      rw [← hi]
      exact (ortoplesseFlagIndexEquiv d hd F).symm_apply_apply k
    rw [hirank, hj]
  rw [hperm]
  apply congrArg (EuclideanSpace.single j)
  have hirank : (ortoplesseFlagIndexEquiv d hd F).symm i = k := by
    rw [← hi]
    exact (ortoplesseFlagIndexEquiv d hd F).symm_apply_apply k
  unfold ortoplesseFlagSign
  dsimp only
  rw [hirank, hF, hG]
  cases b <;> cases c <;> norm_num

open Classical in
theorem ortoplesseFlagIsom_image_vertices (d : ℕ) (hd : 1 ≤ d)
    (F G : (ortoplesse d hd).Flag) (k : Fin d) :
    Finset.image
        (segnoPerm d (ortoplesseFlagPerm d hd F G) (ortoplesseFlagSign d hd F G))
        (ortoplesseFlagVertices d hd F k) =
      ortoplesseFlagVertices d hd G k := by
  rw [ortoplesseFlagVertices_eq_image_Iic d hd F k,
    ortoplesseFlagVertices_eq_image_Iic d hd G k]
  ext x
  simp only [Finset.mem_image, Finset.mem_Iic]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, (ortoplesseFlagIsom_new d hd F G j).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨ortoplesseFlagNew d hd F j, ⟨j, hj, rfl⟩,
      ortoplesseFlagIsom_new d hd F G j⟩

open Classical in
theorem ortoplesseFlagIsom_image_face (d : ℕ) (hd : 1 ≤ d)
    (F G : (ortoplesse d hd).Flag) (k : Fin d) :
    (segnoPerm d (ortoplesseFlagPerm d hd F G) (ortoplesseFlagSign d hd F G) :
        E d → E d) '' F.face k = G.face k := by
  let φ := segnoPerm d (ortoplesseFlagPerm d hd F G) (ortoplesseFlagSign d hd F G)
  calc
    (φ : E d → E d) '' F.face k =
        (φ : E d → E d) '' convexHull ℝ
          ((ortoplesseFlagVertices d hd F k : Finset (E d)) : Set (E d)) := by
      rw [face_eq_hull_vertices (ortoplesse d hd) (F.isFace k)]
      rfl
    _ = convexHull ℝ ((φ : E d → E d) ''
          ((ortoplesseFlagVertices d hd F k : Finset (E d)) : Set (E d))) := by
      exact φ.toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ
          ((ortoplesseFlagVertices d hd G k : Finset (E d)) : Set (E d)) := by
      rw [← Finset.coe_image, ortoplesseFlagIsom_image_vertices d hd F G k]
    _ = G.face k := by
      rw [face_eq_hull_vertices (ortoplesse d hd) (G.isFace k)]
      rfl

open Classical in
theorem ortoplesse_isRegular (d : ℕ) (hd : 1 ≤ d) : (ortoplesse d hd).IsRegular := by
  refine ⟨ortoplesse_isFullDim d hd, ?_⟩
  intro F G
  refine ⟨segnoPerm d (ortoplesseFlagPerm d hd F G) (ortoplesseFlagSign d hd F G),
    segnoPerm_isSymmetry d hd _ _, ?_⟩
  exact ortoplesseFlagIsom_image_face d hd F G

/-- The cross-polytope is one of the regular polytopes counted in dimension `d`. -/
theorem ortoplesse_mem_regularPolytopes (d : ℕ) (hd : 1 ≤ d) :
    ortoplesse d hd ∈ regularPolytopes d :=
  ortoplesse_isRegular d hd

end LeanEval.Geometry.PlatonicClassification
