import Mathlib
import UnicoProofs.Platonici.Fondamenta

open Set Metric
open scoped RealInnerProductSpace

noncomputable section



/-! ## Copia di `Platonici_Tetraedro.lean` -/

abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem cosferico_extremePoints {A : Type*} [NormedAddCommGroup A]
    [InnerProductSpace ℝ A] [Nontrivial A]
    (x : A) (r : ℝ) (V : Set A) (hV : V ⊆ sphere x r) :
    (convexHull ℝ V).extremePoints ℝ = V := by
  refine le_antisymm extremePoints_convexHull_subset ?_
  have hball : convexHull ℝ V ⊆ closedBall x r :=
    convexHull_min (hV.trans sphere_subset_closedBall) (convex_closedBall x r)
  intro v hv
  have hsfera : v ∈ (closedBall x r).extremePoints ℝ := by
    rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
    exact hV hv
  exact inter_extremePoints_subset_extremePoints_of_subset hball
    ⟨subset_convexHull ℝ V hv, hsfera⟩

def w0 : E3 := WithLp.toLp 2 ![1, 1, 1]
def w1 : E3 := WithLp.toLp 2 ![1, -1, -1]
def w2 : E3 := WithLp.toLp 2 ![-1, 1, -1]
def w3 : E3 := WithLp.toLp 2 ![-1, -1, 1]

open Classical in
def verticiTetra : Finset E3 := {w0, w1, w2, w3}

theorem norma_toLp (a b c : ℝ) :
    ‖(WithLp.toLp 2 ![a, b, c] : E3)‖ = Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  norm_num [show (![a, b, c] : Fin 3 → ℝ) 0 = a from rfl,
    show (![a, b, c] : Fin 3 → ℝ) 1 = b from rfl,
    show (![a, b, c] : Fin 3 → ℝ) 2 = c from rfl]

theorem norm_vertici : ∀ v ∈ verticiTetra, ‖v‖ = Real.sqrt 3 := by
  intro v hv
  have hcasi : v = w0 ∨ v = w1 ∨ v = w2 ∨ v = w3 := by
    simpa [verticiTetra] using hv
  rcases hcasi with h | h | h | h
  · subst h
    show ‖(WithLp.toLp 2 ![(1:ℝ), 1, 1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · subst h
    show ‖(WithLp.toLp 2 ![(1:ℝ), -1, -1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · subst h
    show ‖(WithLp.toLp 2 ![(-1:ℝ), 1, -1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · subst h
    show ‖(WithLp.toLp 2 ![(-1:ℝ), -1, 1] : E3)‖ = _
    rw [norma_toLp]; norm_num

def tetraedro : FiniteConvexPolytope E3 where
  vertices := verticiTetra
  nonempty := ⟨w0, by simp [verticiTetra]⟩
  vertices_eq_extremePoints := by
    have hV : (verticiTetra : Set E3) ⊆ sphere 0 (Real.sqrt 3) := by
      intro v hv
      rw [mem_sphere_zero_iff_norm]
      exact norm_vertici v (by exact_mod_cast hv)
    exact (cosferico_extremePoints 0 (Real.sqrt 3) _ hV).symm

theorem testimone_esiste : ∃ _P : FiniteConvexPolytope E3, True :=
  ⟨tetraedro, trivial⟩

/-! ## Coordinate finite e indipendenza affine -/

def w : Fin 4 → E3 := ![w0, w1, w2, w3]

@[simp] theorem w_apply_zero : w 0 = w0 := rfl
@[simp] theorem w_apply_one : w 1 = w1 := rfl
@[simp] theorem w_apply_two : w 2 = w2 := rfl
@[simp] theorem w_apply_three : w 3 = w3 := rfl

theorem w_affineIndependent : AffineIndependent ℝ w := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro a b ha hb hab
  funext i
  have hcoord (j : Fin 3) := congrArg (fun x : E3 => x j) hab
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using ha),
    Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hb)] at hcoord
  simp [w, w0, w1, w2, w3, Fin.sum_univ_four] at hcoord
  have h0 := hcoord 0
  have h1 := hcoord 1
  have h2 := hcoord 2
  change a 0 * 1 + a 1 * 1 + a 2 * (-1) + a 3 * (-1) =
    b 0 * 1 + b 1 * 1 + b 2 * (-1) + b 3 * (-1) at h0
  change a 0 * 1 + a 1 * (-1) + a 2 * 1 + a 3 * (-1) =
    b 0 * 1 + b 1 * (-1) + b 2 * 1 + b 3 * (-1) at h1
  change a 0 * 1 + a 1 * (-1) + a 2 * (-1) + a 3 * 1 =
    b 0 * 1 + b 1 * (-1) + b 2 * (-1) + b 3 * 1 at h2
  rw [Fin.sum_univ_four] at ha hb
  have e0 : a 0 = b 0 := by linarith
  have e1 : a 1 = b 1 := by linarith
  have e2 : a 2 = b 2 := by linarith
  have e3 : a 3 = b 3 := by linarith
  fin_cases i
  · exact e0
  · exact e1
  · simpa using e2
  · simpa using e3

theorem w_injective : Function.Injective w := w_affineIndependent.injective

def wEmb : Fin 4 ↪ E3 := ⟨w, w_injective⟩

theorem verticiTetra_eq_map : verticiTetra = Finset.univ.map wEmb := by
  ext x
  simp only [verticiTetra, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [wEmb, w]

theorem range_w_eq_vertices : Set.range w = (verticiTetra : Set E3) := by
  rw [verticiTetra_eq_map]
  ext x
  simp [wEmb]

def tetraBasis : AffineBasis (Fin 4) ℝ E3 where
  toFun := w
  ind' := w_affineIndependent
  tot' := by
    apply (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ E3 E3
      ⟨w 0, Set.mem_range_self 0⟩).2
    exact w_affineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one (by simp)

@[simp] theorem tetraBasis_apply (i : Fin 4) : tetraBasis i = w i := rfl

theorem range_tetraBasis_eq_vertices :
    Set.range tetraBasis = (tetraedro.vertices : Set E3) := by
  change Set.range w = (verticiTetra : Set E3)
  exact range_w_eq_vertices

def faceVertices (k : Fin 4) : Finset E3 :=
  (Finset.univ.erase k).map wEmb

def tetraFace (k : Fin 4) : Set E3 :=
  convexHull ℝ (faceVertices k : Set E3)

theorem faceVertices_subset (k : Fin 4) : faceVertices k ⊆ verticiTetra := by
  rw [verticiTetra_eq_map]
  exact Finset.map_subset_map.mpr (Finset.erase_subset _ _)

theorem faceVertices_card (k : Fin 4) : (faceVertices k).card = 3 := by
  simp [faceVertices]

theorem tetraFace_nonempty (k : Fin 4) : (tetraFace k).Nonempty := by
  apply Set.Nonempty.mono (subset_convexHull ℝ (faceVertices k : Set E3))
  simpa only [Finset.coe_nonempty] using (Finset.card_pos.mp (by simp [faceVertices_card k]))

theorem tetraFace_finrank (k : Fin 4) :
    Module.finrank ℝ (vectorSpan ℝ (tetraFace k)) = 2 := by
  rw [tetraFace, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
  unfold faceVertices
  rw [Finset.map_eq_image]
  change Module.finrank ℝ
    (vectorSpan ℝ ((Finset.univ.erase k).image w : Set E3)) = 2
  exact w_affineIndependent.finrank_vectorSpan_image_finset
    (s := Finset.univ.erase k) (n := 2) (by simp)

theorem tetraedro_finrank :
    Module.finrank ℝ (vectorSpan ℝ (tetraedro.vertices : Set E3)) = 3 := by
  change Module.finrank ℝ (vectorSpan ℝ (verticiTetra : Set E3)) = 3
  rw [← range_w_eq_vertices]
  exact w_affineIndependent.finrank_vectorSpan (by simp)

theorem mem_tetraFace_iff (k : Fin 4) (x : E3) :
    x ∈ tetraFace k ↔
      x ∈ tetraedro.toSet ∧ tetraBasis.coord k x = 0 := by
  have hfull : tetraFace k ⊆ tetraedro.toSet := by
    apply convexHull_mono
    change (faceVertices k : Set E3) ⊆ (verticiTetra : Set E3)
    exact_mod_cast faceVertices_subset k
  have hzero : tetraFace k ⊆ (tetraBasis.coord k) ⁻¹' ({0} : Set ℝ) := by
    apply convexHull_min
    · intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hy
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      change tetraBasis.coord k (w i) = 0
      rw [← tetraBasis_apply i, tetraBasis.coord_apply]
      simp [hik.symm]
    · exact convex_singleton 0 |>.affine_preimage (tetraBasis.coord k)
  constructor
  · intro hx
    exact ⟨hfull hx, by simpa using hzero hx⟩
  · rintro ⟨hx, hxk⟩
    have hn : ∀ i : Fin 4, 0 ≤ tetraBasis.coord i x := by
      have hm : x ∈ convexHull ℝ (Set.range tetraBasis) := by
        simpa [FiniteConvexPolytope.toSet, range_tetraBasis_eq_vertices] using hx
      rw [tetraBasis.convexHull_eq_nonneg_coord] at hm
      exact hm
    let I := {i : Fin 4 // i ≠ k}
    refine mem_convexHull_of_exists_fintype
      (ι := I) (fun i => tetraBasis.coord i x) (fun i => w i) ?_ ?_ ?_ ?_
    · intro i
      exact hn i
    · rw [← Finset.sum_subtype (p := fun i : Fin 4 => i ≠ k)
        (Finset.univ.erase k) (by simp) (fun i => tetraBasis.coord i x)]
      calc
        ∑ i ∈ (Finset.univ.erase k), tetraBasis.coord i x =
            ∑ i ∈ (Finset.univ : Finset (Fin 4)), tetraBasis.coord i x :=
          Finset.sum_erase (s := (Finset.univ : Finset (Fin 4)))
            (f := fun i => tetraBasis.coord i x) hxk
        _ = 1 := tetraBasis.sum_coord_apply_eq_one x
    · intro i
      exact Finset.mem_map.mpr ⟨i.val, Finset.mem_erase.mpr ⟨i.property, Finset.mem_univ _⟩, rfl⟩
    · calc
        ∑ i : I, tetraBasis.coord i x • w i =
            ∑ i ∈ Finset.univ.erase k, tetraBasis.coord i x • tetraBasis i := by
              rw [Finset.sum_subtype (p := fun i : Fin 4 => i ≠ k)
                (Finset.univ.erase k) (by simp)]
              rfl
        _ = ∑ i : Fin 4, tetraBasis.coord i x • tetraBasis i := by
              exact Finset.sum_erase (s := (Finset.univ : Finset (Fin 4)))
                (f := fun i => tetraBasis.coord i x • tetraBasis i) (by simp [hxk])
        _ = x := tetraBasis.linear_combination_coord_eq_self x

theorem tetraFace_isExposed (k : Fin 4) :
    IsExposed ℝ tetraedro.toSet (tetraFace k) := by
  intro _hne
  let L : E3 →L[ℝ] ℝ := -(tetraBasis.coord k).linear.toContinuousLinearMap
  refine ⟨L, ?_⟩
  ext x
  rw [mem_tetraFace_iff]
  constructor
  · rintro ⟨hxP, hx0⟩
    refine ⟨hxP, ?_⟩
    intro y hyP
    have hny : 0 ≤ tetraBasis.coord k y := by
      have hm : y ∈ convexHull ℝ (Set.range tetraBasis) := by
        simpa [FiniteConvexPolytope.toSet, range_tetraBasis_eq_vertices] using hyP
      have : ∀ i : Fin 4, 0 ≤ tetraBasis.coord i y := by
        rw [tetraBasis.convexHull_eq_nonneg_coord] at hm
        exact hm
      exact this k
    change -(tetraBasis.coord k).linear y ≤ -(tetraBasis.coord k).linear x
    have haff (z : E3) :
        (tetraBasis.coord k).linear z = tetraBasis.coord k z - tetraBasis.coord k 0 := by
      simpa using congrFun (tetraBasis.coord k).decomp' z
    rw [haff, haff, hx0]
    linarith
  · rintro ⟨hxP, hxmax⟩
    refine ⟨hxP, ?_⟩
    let j : Fin 4 := finRotate 4 k
    have hjk : j ≠ k := by
      dsimp [j]
      fin_cases k <;> decide
    have hwjP : w j ∈ tetraedro.toSet := by
      apply subset_convexHull ℝ
      change w j ∈ (verticiTetra : Set E3)
      rw [← range_w_eq_vertices]
      exact Set.mem_range_self j
    have hle := hxmax (w j) hwjP
    have hxnonneg : 0 ≤ tetraBasis.coord k x := by
      have hm : x ∈ convexHull ℝ (Set.range tetraBasis) := by
        simpa [FiniteConvexPolytope.toSet, range_tetraBasis_eq_vertices] using hxP
      have : ∀ i : Fin 4, 0 ≤ tetraBasis.coord i x := by
        rw [tetraBasis.convexHull_eq_nonneg_coord] at hm
        exact hm
      exact this k
    change -(tetraBasis.coord k).linear (w j) ≤
      -(tetraBasis.coord k).linear x at hle
    have haff (z : E3) :
        (tetraBasis.coord k).linear z = tetraBasis.coord k z - tetraBasis.coord k 0 := by
      simpa using congrFun (tetraBasis.coord k).decomp' z
    rw [haff, haff] at hle
    rw [← tetraBasis_apply j, tetraBasis.coord_apply] at hle
    simp [hjk.symm] at hle
    linarith

theorem tetraFace_isFacet (k : Fin 4) : tetraedro.IsFacet (tetraFace k) := by
  exact ⟨⟨tetraFace_isExposed k, tetraFace_nonempty k⟩, tetraFace_finrank k⟩

theorem faceVertices_eq_erase (k : Fin 4) :
    faceVertices k = verticiTetra.erase (w k) := by
  rw [faceVertices, Finset.map_erase, ← verticiTetra_eq_map]
  rfl

open Classical in
theorem exposedFace_eq_convexHull_vertices {F : Set E3}
    (hF : tetraedro.IsFace F) :
    F = convexHull ℝ ((tetraedro.vertices.filter (· ∈ F) : Finset E3) : Set E3) := by
  classical
  let S : Finset E3 := tetraedro.vertices.filter (· ∈ F)
  have hPcompact : IsCompact tetraedro.toSet := by
    exact (tetraedro.vertices.finite_toSet.isCompact_convexHull ℝ)
  have hFcompact : IsCompact F := hF.1.isCompact hPcompact
  have hFconvex : Convex ℝ F := hF.1.convex (convex_convexHull ℝ _)
  have hKM := closure_convexHull_extremePoints hFcompact hFconvex
  have hext : F.extremePoints ℝ = (S : Set E3) := by
    rw [hF.1.isExtreme.extremePoints_eq]
    ext x
    simp only [S, Finset.mem_coe, Finset.mem_filter, mem_inter_iff]
    change (x ∈ F ∧ x ∈ tetraedro.toSet.extremePoints ℝ) ↔
      x ∈ tetraedro.vertices ∧ x ∈ F
    rw [FiniteConvexPolytope.toSet, ← tetraedro.vertices_eq_extremePoints]
    tauto
  calc
    F = closure (convexHull ℝ (F.extremePoints ℝ)) := hKM.symm
    _ = closure (convexHull ℝ (S : Set E3)) := by rw [hext]
    _ = convexHull ℝ (S : Set E3) :=
      (S.finite_toSet.isClosed_convexHull ℝ).closure_eq
    _ = convexHull ℝ
        ((tetraedro.vertices.filter (· ∈ F) : Finset E3) : Set E3) := rfl

theorem affineIndependent_vertices :
    AffineIndependent ℝ
      ((↑) : {x // x ∈ (tetraedro.vertices : Set E3)} → E3) := by
  rw [← range_tetraBasis_eq_vertices]
  exact tetraBasis.ind.range

theorem facet_classification {F : Set E3} (hF : tetraedro.IsFacet F) :
    ∃ k : Fin 4, F = tetraFace k := by
  classical
  let S : Finset E3 := tetraedro.vertices.filter (· ∈ F)
  have hFS : F = convexHull ℝ (S : Set E3) := exposedFace_eq_convexHull_vertices hF.1
  have hSsub : S ⊆ tetraedro.vertices := by
    change tetraedro.vertices.filter (· ∈ F) ⊆ tetraedro.vertices
    exact Finset.filter_subset _ _
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hne := hF.1.2
    rw [hFS, h] at hne
    simp at hne
  have hSind : AffineIndependent ℝ
      ((↑) : {x // x ∈ (S : Set E3)} → E3) :=
    affineIndependent_vertices.mono (by
      intro x hx
      exact_mod_cast hSsub hx)
  have hd : Module.finrank ℝ (vectorSpan ℝ (S : Set E3)) = 2 := by
    have hdF := hF.2
    rw [hFS, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan] at hdF
    exact hdF
  letI : Nonempty {x // x ∈ (S : Set E3)} :=
    ⟨⟨hSne.choose, hSne.choose_spec⟩⟩
  have hcard : S.card = 3 := by
    have hdim := hSind.finrank_vectorSpan_add_one
    have hrange : Set.range ((↑) : {x // x ∈ (S : Set E3)} → E3) = (S : Set E3) :=
      Subtype.range_coe_subtype
    rw [hrange, hd] at hdim
    simpa using hdim.symm
  have hVcard : tetraedro.vertices.card = 4 := by
    change verticiTetra.card = 4
    rw [verticiTetra_eq_map, Finset.card_map]
    simp
  have hSneV : S ≠ tetraedro.vertices := by
    intro heq
    rw [heq, hVcard] at hcard
    omega
  obtain ⟨a, haV, haS⟩ := Finset.exists_of_ssubset
    (Finset.ssubset_iff_subset_ne.mpr ⟨hSsub, hSneV⟩)
  have hSerase : S = tetraedro.vertices.erase a := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      exact Finset.mem_erase.mpr ⟨fun hxa => haS (hxa ▸ hx), hSsub hx⟩
    · rw [Finset.card_erase_of_mem haV, hVcard, hcard]
  have haRange : a ∈ Set.range w := by
    rw [range_w_eq_vertices]
    exact haV
  obtain ⟨k, rfl⟩ := haRange
  refine ⟨k, ?_⟩
  rw [hFS, hSerase]
  congr 1
  exact_mod_cast (faceVertices_eq_erase k).symm

/-! ## Le quattro rotazioni di ordine tre -/

def flip1 : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.refl ℝ ℝ, LinearIsometryEquiv.neg ℝ,
      LinearIsometryEquiv.neg ℝ]

def flip2 : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.neg ℝ, LinearIsometryEquiv.refl ℝ ℝ,
      LinearIsometryEquiv.neg ℝ]

def flip3 : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.neg ℝ, LinearIsometryEquiv.neg ℝ,
      LinearIsometryEquiv.refl ℝ ℝ]

def rot0Linear : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finRotate 3)

def rotLinear : Fin 4 → E3 ≃ₗᵢ[ℝ] E3 :=
  ![rot0Linear,
    flip1.trans (rot0Linear.trans flip1),
    flip2.trans (rot0Linear.trans flip2),
    flip3.trans (rot0Linear.trans flip3)]

def rot (k : Fin 4) : E3 ≃ᵃⁱ[ℝ] E3 :=
  (rotLinear k).toAffineIsometryEquiv

def τ0 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 3, 1]
  invFun := ![0, 3, 1, 2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def τ1 : Equiv.Perm (Fin 4) where
  toFun := ![3, 1, 0, 2]
  invFun := ![2, 1, 3, 0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def τ2 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 2, 0]
  invFun := ![3, 0, 2, 1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def τ3 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def τ : Fin 4 → Equiv.Perm (Fin 4) := ![τ0, τ1, τ2, τ3]

def opp : Fin 4 → Fin 3 → Fin 4 :=
  ![![1, 2, 3], ![0, 3, 2], ![0, 1, 3], ![0, 2, 1]]

theorem τ_fixed (k : Fin 4) : τ k k = k := by
  fin_cases k <;> rfl

theorem opp_ne (k : Fin 4) (i : Fin 3) : opp k i ≠ k := by
  fin_cases k <;> fin_cases i <;> decide

theorem opp_injective (k : Fin 4) : Function.Injective (opp k) := by
  intro i j hij
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp_all [opp]

theorem opp_complete (k j : Fin 4) (hjk : j ≠ k) : ∃ i : Fin 3, opp k i = j := by
  fin_cases k <;> fin_cases j <;> simp_all [opp]
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩

theorem τ_opp (k : Fin 4) (i : Fin 3) :
    τ k (opp k i) = opp k (finRotate 3 i) := by
  fin_cases k <;> fin_cases i <;> rfl

theorem rot_vertex (k i : Fin 4) : rot k (w i) = w (τ k i) := by
  have hm1 : (-1 : Fin 3) = 2 := by decide
  have h21 : (2 - 1 : Fin 3) = 1 := by decide
  fin_cases k <;> fin_cases i <;> ext j <;> fin_cases j <;>
    simp [rot, rotLinear, rot0Linear, flip1, flip2, flip3,
      w, w0, w1, w2, w3, τ, τ0, τ1, τ2, τ3, hm1, h21]

theorem rot_fixed (k : Fin 4) : rot k (w k) = w k := by
  rw [rot_vertex, τ_fixed]

theorem rot_image_vertices (k : Fin 4) :
    (⇑(rot k)) '' (tetraedro.vertices : Set E3) =
      (tetraedro.vertices : Set E3) := by
  rw [← range_tetraBasis_eq_vertices, show Set.range tetraBasis = Set.range w by rfl]
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [rot_vertex]
    exact Set.mem_range_self (τ k i)
  · rintro ⟨i, rfl⟩
    refine ⟨w ((τ k).symm i), Set.mem_range_self _, ?_⟩
    rw [rot_vertex, (τ k).apply_symm_apply]

theorem rot_preserves_polytope (k : Fin 4) :
    (⇑(rot k)) '' tetraedro.toSet = tetraedro.toSet := by
  change (⇑(rot k)) '' convexHull ℝ (tetraedro.vertices : Set E3) =
    convexHull ℝ (tetraedro.vertices : Set E3)
  calc
    (⇑(rot k)) '' convexHull ℝ (tetraedro.vertices : Set E3) =
        convexHull ℝ ((⇑(rot k)) '' (tetraedro.vertices : Set E3)) := by
      simpa only [AffineEquiv.coe_toAffineMap,
        AffineIsometryEquiv.coe_toAffineEquiv] using
        ((rot k).toAffineEquiv.toAffineMap.image_convexHull
          (tetraedro.vertices : Set E3))
    _ = convexHull ℝ (tetraedro.vertices : Set E3) := by
      rw [rot_image_vertices]

theorem rot_image_faceVertices (k a : Fin 4) :
    (⇑(rot k)) '' (faceVertices a : Set E3) =
      (faceVertices (τ k a) : Set E3) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hy
    change rot k (w i) ∈ (faceVertices (τ k a) : Set E3)
    rw [rot_vertex]
    apply Finset.mem_map.mpr
    refine ⟨τ k i, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, rfl⟩
    exact (τ k).injective.ne (Finset.ne_of_mem_erase hi)
  · intro hx
    obtain ⟨j, hj, hxj⟩ := Finset.mem_map.mp hx
    subst x
    let i := (τ k).symm j
    have hia : i ≠ a := by
      intro h
      apply Finset.ne_of_mem_erase hj
      rw [← h, (τ k).apply_symm_apply]
    refine ⟨w i, ?_, ?_⟩
    · exact Finset.mem_map.mpr
        ⟨i, Finset.mem_erase.mpr ⟨hia, Finset.mem_univ _⟩, rfl⟩
    · rw [rot_vertex, (τ k).apply_symm_apply]
      rfl

theorem rot_image_tetraFace (k a : Fin 4) :
    (⇑(rot k)) '' tetraFace a = tetraFace (τ k a) := by
  change (⇑(rot k)) '' convexHull ℝ (faceVertices a : Set E3) =
    convexHull ℝ (faceVertices (τ k a) : Set E3)
  calc
    (⇑(rot k)) '' convexHull ℝ (faceVertices a : Set E3) =
        convexHull ℝ ((⇑(rot k)) '' (faceVertices a : Set E3)) := by
      simpa only [AffineEquiv.coe_toAffineMap,
        AffineIsometryEquiv.coe_toAffineEquiv] using
        ((rot k).toAffineEquiv.toAffineMap.image_convexHull
          (faceVertices a : Set E3))
    _ = convexHull ℝ (faceVertices (τ k a) : Set E3) := by
      rw [rot_image_faceVertices]

/-! ## Regolarità uniforme delle quattro faccette -/

def edgeLength : ℝ := Real.sqrt 8

theorem edgeLength_pos : 0 < edgeLength := by
  dsimp [edgeLength]
  positivity

theorem dist_w_of_ne (i j : Fin 4) (hij : i ≠ j) :
    dist (w i) (w j) = edgeLength := by
  fin_cases i <;> fin_cases j <;>
    simp_all [w, w0, w1, w2, w3, edgeLength, dist_eq_norm,
      EuclideanSpace.norm_eq, Fin.sum_univ_three]
  all_goals norm_num

theorem rot_iter_opp (k : Fin 4) (i : Fin 3) :
    (⇑(rot k))^[(i : ℕ)] (w (opp k 0)) = w (opp k i) := by
  fin_cases i
  · simp
  · simp [rot_vertex, τ_opp]
  · simp [rot_vertex, τ_opp]

theorem rot_order_three_on_opp (k : Fin 4) :
    (⇑(rot k))^[3] (w (opp k 0)) = w (opp k 0) := by
  simp [Function.iterate_succ_apply, rot_vertex, τ_opp]

theorem range_rot_orbit (k : Fin 4) :
    Set.range (fun i : Fin 3 => (⇑(rot k))^[(i : ℕ)] (w (opp k 0))) =
      (faceVertices k : Set E3) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    change (⇑(rot k))^[(i : ℕ)] (w (opp k 0)) ∈ (faceVertices k : Set E3)
    rw [rot_iter_opp]
    exact Finset.mem_map.mpr
      ⟨opp k i, Finset.mem_erase.mpr ⟨opp_ne k i, Finset.mem_univ _⟩, rfl⟩
  · intro hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨i, hi⟩ := opp_complete k j (Finset.ne_of_mem_erase hj)
    refine ⟨i, ?_⟩
    change (⇑(rot k))^[(i : ℕ)] (w (opp k 0)) = w j
    rw [rot_iter_opp, hi]

theorem rot_orbit_injective (k : Fin 4) :
    Function.Injective
      (fun i : Fin 3 => (⇑(rot k))^[(i : ℕ)] (w (opp k 0))) := by
  intro i j hij
  change (⇑(rot k))^[(i : ℕ)] (w (opp k 0)) =
    (⇑(rot k))^[(j : ℕ)] (w (opp k 0)) at hij
  rw [rot_iter_opp, rot_iter_opp] at hij
  exact opp_injective k (w_injective hij)

theorem tetraFace_regular (k : Fin 4) :
    tetraedro.IsRegularFacet (tetraFace k) 3 edgeLength := by
  refine ⟨tetraFace_isFacet k, edgeLength_pos, by omega, rot k,
    w (opp k 0), ?_, ?_, rot_orbit_injective k,
    rot_order_three_on_opp k, ?_, ?_⟩
  · apply subset_convexHull ℝ
    exact Finset.mem_map.mpr
      ⟨opp k 0, Finset.mem_erase.mpr ⟨opp_ne k 0, Finset.mem_univ _⟩, rfl⟩
  · rw [rot_image_tetraFace, τ_fixed]
  · rw [tetraFace, range_rot_orbit]
  · rw [rot_vertex, τ_opp]
    apply dist_w_of_ne
    intro h
    have h01 := opp_injective k h
    norm_num at h01

theorem every_facet_regular (F : Set E3) (hF : tetraedro.IsFacet F) :
    tetraedro.IsRegularFacet F 3 edgeLength := by
  obtain ⟨k, rfl⟩ := facet_classification hF
  exact tetraFace_regular k

/-! ## I fan ciclici ai quattro vertici -/

theorem vertex_mem_tetraFace_iff (i a : Fin 4) :
    w i ∈ tetraFace a ↔ i ≠ a := by
  constructor
  · intro hi hia
    subst a
    have hz := (mem_tetraFace_iff i (w i)).mp hi |>.2
    rw [← tetraBasis_apply i, tetraBasis.coord_apply] at hz
    norm_num at hz
  · intro hia
    apply subset_convexHull ℝ
    exact Finset.mem_map.mpr
      ⟨i, Finset.mem_erase.mpr ⟨hia, Finset.mem_univ _⟩, rfl⟩

theorem tetraFace_injective : Function.Injective tetraFace := by
  intro a b hab
  by_contra habne
  have hmem : w a ∈ tetraFace b := (vertex_mem_tetraFace_iff a b).2 habne
  rw [← hab] at hmem
  exact (vertex_mem_tetraFace_iff a a).1 hmem rfl

theorem vertex_mem_incident_face (k : Fin 4) (i : Fin 3) :
    w k ∈ tetraFace (opp k i) :=
  (vertex_mem_tetraFace_iff k (opp k i)).2 (opp_ne k i).symm

def thirdOpp (k : Fin 4) (i : Fin 3) : Fin 4 :=
  opp k (finRotate 3 (finRotate 3 i))

theorem thirdOpp_ne_vertex (k : Fin 4) (i : Fin 3) : thirdOpp k i ≠ k :=
  opp_ne k _

theorem thirdOpp_ne_current (k : Fin 4) (i : Fin 3) :
    thirdOpp k i ≠ opp k i := by
  intro h
  have := opp_injective k h
  fin_cases i <;> contradiction

theorem thirdOpp_ne_next (k : Fin 4) (i : Fin 3) :
    thirdOpp k i ≠ opp k (finRotate 3 i) := by
  intro h
  have := opp_injective k h
  fin_cases i <;> contradiction

theorem fin3_cycle_exhausts (i j : Fin 3) (hji : j ≠ i)
    (hjr : j ≠ finRotate 3 i) (t : Fin 3) :
    t = i ∨ t = finRotate 3 i ∨ t = j := by
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals fin_cases t <;> simp

theorem three_incident_faces_meet_at_vertex (k : Fin 4) (x : E3)
    (hx : ∀ i : Fin 3, x ∈ tetraFace (opp k i)) : x = w k := by
  have hzero (a : Fin 4) (hak : a ≠ k) : tetraBasis.coord a x = 0 := by
    obtain ⟨i, hi⟩ := opp_complete k a hak
    rw [← hi]
    exact (mem_tetraFace_iff (opp k i) x).mp (hx i) |>.2
  have hk : tetraBasis.coord k x = 1 := by
    have hs := tetraBasis.sum_coord_apply_eq_one x
    rw [Fin.sum_univ_four] at hs
    fin_cases k
    · have h1 := hzero 1 (by decide)
      have h2 := hzero 2 (by decide)
      have h3 := hzero 3 (by decide)
      change tetraBasis.coord 0 x = 1
      linarith
    · have h0 := hzero 0 (by decide)
      have h2 := hzero 2 (by decide)
      have h3 := hzero 3 (by decide)
      change tetraBasis.coord 1 x = 1
      linarith
    · have h0 := hzero 0 (by decide)
      have h1 := hzero 1 (by decide)
      have h3 := hzero 3 (by decide)
      change tetraBasis.coord 2 x = 1
      linarith
    · have h0 := hzero 0 (by decide)
      have h1 := hzero 1 (by decide)
      have h2 := hzero 2 (by decide)
      change tetraBasis.coord 3 x = 1
      linarith
  apply tetraBasis.ext_elem
  intro a
  by_cases hak : a = k
  · subst a
    rw [hk, ← tetraBasis_apply k, tetraBasis.coord_apply]
    simp
  · rw [hzero a hak, ← tetraBasis_apply k, tetraBasis.coord_apply]
    simp [hak]

def tetraCyclicData (k : Fin 4) :
    tetraedro.CyclicVertexData (w k) 3 where
  faccetta i := tetraFace (opp k i)
  isFacet i := tetraFace_isFacet (opp k i)
  mem_v i := vertex_mem_incident_face k i
  distinte := by
    intro i j hij
    exact opp_injective k (tetraFace_injective hij)
  complete := by
    intro F hF hwk
    obtain ⟨a, rfl⟩ := facet_classification hF
    have hak : a ≠ k := by
      exact ((vertex_mem_tetraFace_iff k a).1 hwk).symm
    obtain ⟨i, hi⟩ := opp_complete k a hak
    exact ⟨i, by rw [hi]⟩
  σ := rot k
  fissa_v := rot_fixed k
  preserva := rot_preserves_polytope k
  ruota i := by
    rw [rot_image_tetraFace, τ_opp]
  spigolo i := by
    refine ⟨w (thirdOpp k i), w_injective.ne (thirdOpp_ne_vertex k i), ?_, ?_⟩
    · exact (vertex_mem_tetraFace_iff _ _).2 (thirdOpp_ne_current k i)
    · exact (vertex_mem_tetraFace_iff _ _).2 (thirdOpp_ne_next k i)
  spigolo_due i j x hx hxne hxj := by
    by_cases hji : j = i
    · exact Or.inl hji
    by_cases hjr : j = finRotate 3 i
    · exact Or.inr hjr
    exfalso
    apply hxne
    apply three_incident_faces_meet_at_vertex k x
    intro t
    rcases fin3_cycle_exhausts i j hji hjr t with rfl | ht | ht
    · exact hx.1
    · rw [ht]
      exact hx.2
    · rw [ht]
      exact hxj

theorem tetra_vertex_cyclic (k : Fin 4) :
    tetraedro.IsCyclicVertex (w k) 3 :=
  ⟨tetraCyclicData k⟩

theorem every_vertex_cyclic (v : E3) (hv : v ∈ tetraedro.vertices) :
    tetraedro.IsCyclicVertex v 3 := by
  have : v ∈ Set.range w := by
    rw [range_w_eq_vertices]
    exact hv
  obtain ⟨k, rfl⟩ := this
  exact tetra_vertex_cyclic k

/-! ## Assemblaggio finale -/

theorem tetraedro_cyclicallyRegular :
    tetraedro.IsCyclicallyRegularOfType 3 3 := by
  refine ⟨tetraedro_finrank, by omega, by omega, edgeLength, edgeLength_pos, ?_, ?_⟩
  · intro F hF
    exact every_facet_regular F hF
  · intro v hv
    exact every_vertex_cyclic v hv
