import Mathlib
import Challenge
import Solution.IstanzeBenchmark
import Solution.ConteggioBenchmark

/-!
FASE 2 — I CINQUE IsRegular SUL CONTRATTO, port a modulo (18 lug 2026).
Fascicoli 10-12 di sol (CERTIFICATI 37+43+46), ciascuno nel suo
sotto-namespace (F10/F11/F12: zero collisioni per costruzione); contratto
embedded sostituito dall'import del modulo `Benchmark`. In coda il finale.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

abbrev E3 := E 3

namespace F10

open scoped Topology
open ConvexPolytope


/-! ## Il simplesso tetraedrale -/


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

theorem norm_vertici : ∀ v ∈ verticiTetra, ‖v‖ = Real.sqrt 3 := by
  intro v hv
  have hcasi : v = w0 ∨ v = w1 ∨ v = w2 ∨ v = w3 := by
    simpa [verticiTetra] using hv
  rcases hcasi with h | h | h | h
  · subst h
    show ‖(WithLp.toLp 2 ![(1 : ℝ), 1, 1] : E3)‖ = _
    rw [norma_toLp]
    norm_num
  · subst h
    show ‖(WithLp.toLp 2 ![(1 : ℝ), -1, -1] : E3)‖ = _
    rw [norma_toLp]
    norm_num
  · subst h
    show ‖(WithLp.toLp 2 ![(-1 : ℝ), 1, -1] : E3)‖ = _
    rw [norma_toLp]
    norm_num
  · subst h
    show ‖(WithLp.toLp 2 ![(-1 : ℝ), -1, 1] : E3)‖ = _
    rw [norma_toLp]
    norm_num

def tetraedroB : ConvexPolytope 3 where
  vertices := verticiTetra
  vertices_nonempty := ⟨w0, by simp [verticiTetra]⟩
  vertices_eq_extremePoints := by
    have hV : (verticiTetra : Set E3) ⊆ sphere 0 (Real.sqrt 3) := by
      intro v hv
      rw [mem_sphere_zero_iff_norm]
      exact norm_vertici v (by exact_mod_cast hv)
    exact (cosferico_extremePoints 0 (Real.sqrt 3) _ hV).symm

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

theorem range_w_eq_vertices : Set.range w = (tetraedroB.vertices : Set E3) := by
  change Set.range w = (verticiTetra : Set E3)
  rw [verticiTetra_eq_map]
  ext x
  simp [wEmb]

theorem tetraedroB_finrank :
    Module.finrank ℝ (vectorSpan ℝ (tetraedroB.vertices : Set E3)) = 3 := by
  rw [← range_w_eq_vertices]
  exact w_affineIndependent.finrank_vectorSpan (by simp)

/-! ## Classificazione di tutte le facce che possono comparire in una bandiera -/

open Classical in
theorem exposedFace_eq_convexHull_vertices {F : Set E3}
    (hF : tetraedroB.IsFace F) :
    F = convexHull ℝ ((tetraedroB.vertices.filter (· ∈ F) : Finset E3) : Set E3) := by
  classical
  let S : Finset E3 := tetraedroB.vertices.filter (· ∈ F)
  have hPcompact : IsCompact tetraedroB.toSet :=
    tetraedroB.vertices.finite_toSet.isCompact_convexHull ℝ
  have hFcompact : IsCompact F := hF.1.isCompact hPcompact
  have hFconvex : Convex ℝ F := hF.1.convex (convex_convexHull ℝ _)
  have hKM := closure_convexHull_extremePoints hFcompact hFconvex
  have hext : F.extremePoints ℝ = (S : Set E3) := by
    rw [hF.1.isExtreme.extremePoints_eq]
    ext x
    simp only [S, Finset.mem_coe, Finset.mem_filter, mem_inter_iff]
    change (x ∈ F ∧ x ∈ tetraedroB.toSet.extremePoints ℝ) ↔
      x ∈ tetraedroB.vertices ∧ x ∈ F
    rw [ConvexPolytope.toSet, ← tetraedroB.vertices_eq_extremePoints]
    tauto
  calc
    F = closure (convexHull ℝ (F.extremePoints ℝ)) := hKM.symm
    _ = closure (convexHull ℝ (S : Set E3)) := by rw [hext]
    _ = convexHull ℝ (S : Set E3) :=
      (S.finite_toSet.isClosed_convexHull ℝ).closure_eq
    _ = convexHull ℝ
        ((tetraedroB.vertices.filter (· ∈ F) : Finset E3) : Set E3) := rfl

theorem affineIndependent_vertices :
    AffineIndependent ℝ
      ((↑) : {x // x ∈ (tetraedroB.vertices : Set E3)} → E3) := by
  rw [← range_w_eq_vertices]
  exact w_affineIndependent.range

open Classical in
def faceIndices (F : Set E3) : Finset (Fin 4) :=
  Finset.univ.filter fun i => w i ∈ F

open Classical in
theorem filtered_vertices_eq_map (F : Set E3) :
    tetraedroB.vertices.filter (· ∈ F) = (faceIndices F).map wEmb := by
  classical
  rw [show tetraedroB.vertices = verticiTetra by rfl, verticiTetra_eq_map]
  ext x
  constructor
  · intro hx
    obtain ⟨hxv, hxF⟩ := Finset.mem_filter.mp hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hxv
    exact Finset.mem_map.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxF⟩, rfl⟩
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    have hiF := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩, hiF⟩

theorem face_eq_hull_indices {F : Set E3} (hF : tetraedroB.IsFace F) :
    F = convexHull ℝ (((faceIndices F).map wEmb : Finset E3) : Set E3) := by
  rw [← filtered_vertices_eq_map]
  exact exposedFace_eq_convexHull_vertices hF

theorem faceIndices_card {F : Set E3} (hF : tetraedroB.IsFace F) :
    (faceIndices F).card = ConvexPolytope.faceDim F + 1 := by
  classical
  let S : Finset E3 := tetraedroB.vertices.filter (· ∈ F)
  have hFS : F = convexHull ℝ (S : Set E3) := exposedFace_eq_convexHull_vertices hF
  have hSsub : S ⊆ tetraedroB.vertices := Finset.filter_subset _ _
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hne := hF.2
    rw [hFS, h] at hne
    simp at hne
  have hSind : AffineIndependent ℝ
      ((↑) : {x // x ∈ (S : Set E3)} → E3) :=
    affineIndependent_vertices.mono (by
      intro x hx
      exact_mod_cast hSsub hx)
  letI : Nonempty {x // x ∈ (S : Set E3)} :=
    ⟨⟨hSne.choose, hSne.choose_spec⟩⟩
  have hdim := hSind.finrank_vectorSpan_add_one
  have hrange : Set.range ((↑) : {x // x ∈ (S : Set E3)} → E3) = (S : Set E3) :=
    Subtype.range_coe_subtype
  rw [hrange] at hdim
  have hdim' : Module.finrank ℝ (vectorSpan ℝ (S : Set E3)) =
      ConvexPolytope.faceDim F := by
    symm
    unfold ConvexPolytope.faceDim
    rw [hFS, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
  rw [hdim'] at hdim
  rw [← Finset.card_map wEmb, ← filtered_vertices_eq_map F]
  change S.card = ConvexPolytope.faceDim F + 1
  simpa using hdim.symm

theorem faceIndices_mono {F G : Set E3} (h : F ⊆ G) :
    faceIndices F ⊆ faceIndices G := by
  intro i hi
  simpa [faceIndices] using h (by simpa [faceIndices] using hi)

structure FlagTriple (F : tetraedroB.Flag) where
  idx : Fin 3 → Fin 4
  injective : Function.Injective idx
  face_zero : F.face 0 = convexHull ℝ ({w (idx 0)} : Set E3)
  face_one : F.face 1 = convexHull ℝ ({w (idx 0), w (idx 1)} : Set E3)
  face_two : F.face 2 = convexHull ℝ ({w (idx 0), w (idx 1), w (idx 2)} : Set E3)

theorem flag_has_triple (F : tetraedroB.Flag) : Nonempty (FlagTriple F) := by
  classical
  let S0 := faceIndices (F.face 0)
  let S1 := faceIndices (F.face 1)
  let S2 := faceIndices (F.face 2)
  have hc0 : S0.card = 1 := by
    simpa [S0, F.dim_eq] using faceIndices_card (F.isFace 0)
  have hc1 : S1.card = 2 := by
    simpa [S1, F.dim_eq] using faceIndices_card (F.isFace 1)
  have hc2 : S2.card = 3 := by
    simpa [S2, F.dim_eq] using faceIndices_card (F.isFace 2)
  have h01 : S0 ⊆ S1 :=
    faceIndices_mono (F.strict_mono 0 1 (by decide)).1
  have h12 : S1 ⊆ S2 :=
    faceIndices_mono (F.strict_mono 1 2 (by decide)).1
  obtain ⟨a, hS0⟩ := Finset.card_eq_one.mp hc0
  obtain ⟨b, hb0, hbEq⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨h01, by omega⟩
  have hS1 : S1 = {a, b} := by
    rw [← hbEq, hS0]
    ext x
    simp [or_comm]
  obtain ⟨c, hc1not, hcEq⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨h12, by omega⟩
  have hS2 : S2 = {a, b, c} := by
    rw [← hcEq, hS1]
    ext x
    simp [or_left_comm, or_comm]
  let p : Fin 3 → Fin 4 := ![a, b, c]
  have hp : Function.Injective p := by
    intro i j hij
    have hba : b ≠ a := by
      intro h
      apply hb0
      simp [hS0, h]
    have hca : c ≠ a := by
      intro h
      apply hc1not
      simp [hS1, h]
    have hcb : c ≠ b := by
      intro h
      apply hc1not
      simp [hS1, h]
    fin_cases i <;> fin_cases j <;> simp_all [p]
  refine ⟨{
    idx := p
    injective := hp
    face_zero := ?_
    face_one := ?_
    face_two := ?_ }⟩
  · rw [face_eq_hull_indices (F.isFace 0)]
    rw [show faceIndices (F.face 0) = S0 by rfl, hS0]
    congr 2
    ext x
    simp [p, wEmb]
  · rw [face_eq_hull_indices (F.isFace 1)]
    rw [show faceIndices (F.face 1) = S1 by rfl, hS1]
    congr 2
    ext x
    simp [p, wEmb]
  · rw [face_eq_hull_indices (F.isFace 2)]
    rw [show faceIndices (F.face 2) = S2 by rfl, hS2]
    congr 2
    ext x
    simp [p, wEmb]

/-! ## Ogni permutazione dei quattro vertici è una isometria -/

theorem inner_toLp (a b c d e f : ℝ) :
    inner ℝ (WithLp.toLp 2 ![a, b, c] : E3)
      (WithLp.toLp 2 ![d, e, f] : E3) = a * d + b * e + c * f := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [RCLike.inner_apply, conj_trivial]
  norm_num [show (![a, b, c] : Fin 3 → ℝ) 0 = a from rfl,
    show (![a, b, c] : Fin 3 → ℝ) 1 = b from rfl,
    show (![a, b, c] : Fin 3 → ℝ) 2 = c from rfl,
    show (![d, e, f] : Fin 3 → ℝ) 0 = d from rfl,
    show (![d, e, f] : Fin 3 → ℝ) 1 = e from rfl,
    show (![d, e, f] : Fin 3 → ℝ) 2 = f from rfl]
  ring

theorem inner_w (i j : Fin 4) :
    inner ℝ (w i) (w j) = if i = j then 3 else -1 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, real_inner_self_eq_norm_sq]
    have hi : w i ∈ verticiTetra := by
      rw [verticiTetra_eq_map]
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [norm_vertici (w i) hi, Real.sq_sqrt (by norm_num)]
  · rw [if_neg hij]
    fin_cases i <;> fin_cases j <;>
      simp_all [w, w0, w1, w2, w3, inner_toLp]

def axis (σ : Equiv.Perm (Fin 4)) (j : Fin 3) : E3 :=
  (2 : ℝ)⁻¹ • (w (σ 0) + w (σ j.succ))

theorem axis_orthonormal (σ : Equiv.Perm (Fin 4)) : Orthonormal ℝ (axis σ) := by
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst j
    have h0 : σ 0 ≠ σ i.succ := σ.injective.ne (Fin.succ_ne_zero i).symm
    simp only [axis, real_inner_smul_left, real_inner_smul_right, inner_add_left,
      inner_add_right, inner_w]
    simp [h0]
    norm_num
  · have h0i : σ 0 ≠ σ i.succ := σ.injective.ne (Fin.succ_ne_zero i).symm
    have h0j : σ 0 ≠ σ j.succ := σ.injective.ne (Fin.succ_ne_zero j).symm
    have hij' : σ i.succ ≠ σ j.succ :=
      σ.injective.ne (fun h => hij (Fin.succ_injective 3 h))
    rw [if_neg hij]
    simp only [axis, real_inner_smul_left, real_inner_smul_right, inner_add_left,
      inner_add_right, inner_w]
    simp [h0j, hij']
    norm_num

def axisBasis (σ : Equiv.Perm (Fin 4)) : OrthonormalBasis (Fin 3) ℝ E3 :=
  OrthonormalBasis.mk (axis_orthonormal σ)
    ((axis_orthonormal σ).linearIndependent.span_eq_top_of_card_eq_finrank (by simp [E3])).ge

@[simp] theorem axisBasis_apply (σ : Equiv.Perm (Fin 4)) (j : Fin 3) :
    axisBasis σ j = axis σ j := by
  simp only [axisBasis]
  rw [OrthonormalBasis.coe_mk]

theorem sum_w : ∑ i : Fin 4, w i = 0 := by
  ext j
  fin_cases j <;> simp [w, w0, w1, w2, w3, Fin.sum_univ_four]

theorem sum_w_tail (σ : Equiv.Perm (Fin 4)) :
    ∑ j : Fin 3, w (σ j.succ) = -w (σ 0) := by
  have hall : ∑ i : Fin 4, w (σ i) = 0 := by
    rw [Equiv.sum_comp σ w]
    exact sum_w
  rw [Fin.sum_univ_succ] at hall
  exact eq_neg_of_add_eq_zero_right hall

theorem sum_axis (σ : Equiv.Perm (Fin 4)) :
    ∑ j : Fin 3, axis σ j = w (σ 0) := by
  rw [show (∑ j : Fin 3, axis σ j) =
      (2 : ℝ)⁻¹ • ∑ j : Fin 3, (w (σ 0) + w (σ j.succ)) by
    simp [axis, Finset.smul_sum]]
  rw [Finset.sum_add_distrib, sum_w_tail]
  simp
  module

def tetraLinear (σ : Equiv.Perm (Fin 4)) : E3 ≃ₗᵢ[ℝ] E3 :=
  (axisBasis (Equiv.refl (Fin 4))).equiv (axisBasis σ) (Equiv.refl (Fin 3))

theorem tetraLinear_axis (σ : Equiv.Perm (Fin 4)) (j : Fin 3) :
    tetraLinear σ (axis (Equiv.refl (Fin 4)) j) = axis σ j := by
  rw [← axisBasis_apply (Equiv.refl (Fin 4)) j, ← axisBasis_apply σ j]
  simpa [tetraLinear] using
    (axisBasis (Equiv.refl (Fin 4))).equiv_apply_basis
      (axisBasis σ) (Equiv.refl (Fin 3)) j

theorem tetraLinear_vertex_zero (σ : Equiv.Perm (Fin 4)) :
    tetraLinear σ (w 0) = w (σ 0) := by
  have hbase : ∑ j : Fin 3, axis (Equiv.refl (Fin 4)) j = w 0 := by
    simpa using sum_axis (Equiv.refl (Fin 4))
  rw [← hbase, map_sum]
  simp_rw [tetraLinear_axis]
  exact sum_axis σ

theorem tetraLinear_vertex (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    tetraLinear σ (w i) = w (σ i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact tetraLinear_vertex_zero σ
  · have hsource : w j.succ = (2 : ℝ) • axis (Equiv.refl (Fin 4)) j - w 0 := by
      simp [axis]
    have htarget : w (σ j.succ) = (2 : ℝ) • axis σ j - w (σ 0) := by
      simp [axis]
    rw [hsource, map_sub, map_smul, tetraLinear_axis]
    rw [tetraLinear_vertex_zero]
    exact htarget.symm

def tetraIsom (σ : Equiv.Perm (Fin 4)) : ConvexPolytope.Isom 3 :=
  (tetraLinear σ).toAffineIsometryEquiv

theorem tetraIsom_vertex (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    tetraIsom σ (w i) = w (σ i) := tetraLinear_vertex σ i

theorem tetraIsom_image_vertices (σ : Equiv.Perm (Fin 4)) :
    (⇑(tetraIsom σ)) '' (tetraedroB.vertices : Set E3) =
      (tetraedroB.vertices : Set E3) := by
  rw [← range_w_eq_vertices]
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [tetraIsom_vertex]
    exact Set.mem_range_self (σ i)
  · rintro ⟨i, rfl⟩
    refine ⟨w (σ.symm i), Set.mem_range_self _, ?_⟩
    rw [tetraIsom_vertex, σ.apply_symm_apply]

theorem tetraIsom_image_hull (σ : Equiv.Perm (Fin 4)) (S : Set E3) :
    (⇑(tetraIsom σ)) '' convexHull ℝ S =
      convexHull ℝ ((⇑(tetraIsom σ)) '' S) := by
  simpa only [AffineEquiv.coe_toAffineMap, AffineIsometryEquiv.coe_toAffineEquiv] using
    (tetraIsom σ).toAffineEquiv.toAffineMap.image_convexHull S

theorem tetraIsom_symmetry (σ : Equiv.Perm (Fin 4)) :
    tetraedroB.isSymmetry (tetraIsom σ) := by
  change (⇑(tetraIsom σ)) '' convexHull ℝ (tetraedroB.vertices : Set E3) =
    convexHull ℝ (tetraedroB.vertices : Set E3)
  rw [tetraIsom_image_hull, tetraIsom_image_vertices]

theorem image_vertex_set_one (σ : Equiv.Perm (Fin 4)) (a : Fin 4) :
    (⇑(tetraIsom σ)) '' ({w a} : Set E3) = {w (σ a)} := by
  ext x
  simp [tetraIsom_vertex]

theorem image_vertex_set_two (σ : Equiv.Perm (Fin 4)) (a b : Fin 4) :
    (⇑(tetraIsom σ)) '' ({w a, w b} : Set E3) = {w (σ a), w (σ b)} := by
  ext x
  simp [tetraIsom_vertex, eq_comm]

theorem image_vertex_set_three (σ : Equiv.Perm (Fin 4)) (a b c : Fin 4) :
    (⇑(tetraIsom σ)) '' ({w a, w b, w c} : Set E3) =
      {w (σ a), w (σ b), w (σ c)} := by
  ext x
  simp [tetraIsom_vertex, eq_comm]

/-! ## CONSEGNA -/

theorem tetraedroB_isRegular : tetraedroB.IsRegular := by
  refine ⟨?_, ?_⟩
  · rw [ConvexPolytope.IsFullDim, ConvexPolytope.dim,
      ConvexPolytope.toSet, ← direction_affineSpan,
      affineSpan_convexHull, direction_affineSpan]
    exact tetraedroB_finrank
  · intro F G
    let f := (flag_has_triple F).some
    let g := (flag_has_triple G).some
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
      f.idx g.idx f.injective g.injective
    refine ⟨tetraIsom σ, tetraIsom_symmetry σ, ?_⟩
    intro k
    by_cases hk0 : k = 0
    · subst k
      rw [f.face_zero, g.face_zero, tetraIsom_image_hull,
        image_vertex_set_one, hσ]
    by_cases hk1 : k = 1
    · subst k
      rw [f.face_one, g.face_one, tetraIsom_image_hull,
        image_vertex_set_two]
      simp_rw [hσ]
    · have hk2 : k = 2 := by
        apply Fin.ext
        omega
      subst k
      rw [f.face_two, g.face_two, tetraIsom_image_hull,
        image_vertex_set_three]
      simp_rw [hσ]


end F10

namespace F11

open scoped Topology
open ConvexPolytope



/-! ## Trasporto affine delle facce e delle dimensioni -/

theorem isExposed_image_isom (φ : ConvexPolytope.Isom 3) {A B : Set E3}
    (h : IsExposed ℝ A B) : IsExposed ℝ ((⇑φ) '' A) ((⇑φ) '' B) := by
  intro hne
  obtain ⟨b, hbB⟩ := hne
  obtain ⟨a, haB, hab⟩ := hbB
  obtain ⟨l, hl⟩ := h ⟨a, haB⟩
  let l' : E3 →L[ℝ] ℝ :=
    l.comp φ.symm.linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
  have hl' (x : E3) : l' (φ x) = l x - l (φ.symm 0) := by
    have hm := φ.symm.map_vsub (φ x) 0
    have hm' : φ.symm.linearIsometryEquiv (φ x) = x - φ.symm 0 := by
      simpa using hm
    simp only [l', ContinuousLinearMap.comp_apply]
    change l (φ.symm.linearIsometryEquiv (φ x)) = _
    rw [hm', map_sub]
  refine ⟨l', Set.ext ?_⟩
  intro x
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [hl] at hb
    refine ⟨⟨b, hb.1, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [hl' y, hl' b]
    exact sub_le_sub_right (hb.2 y hy) _
  · rintro ⟨hxA, hxmax⟩
    obtain ⟨a, ha, rfl⟩ := hxA
    refine ⟨a, ?_, rfl⟩
    rw [hl]
    refine ⟨ha, ?_⟩
    intro y hy
    have hle := hxmax (φ y) ⟨y, hy, rfl⟩
    rw [hl' y, hl' a] at hle
    linarith

theorem faceDim_image_isom (φ : ConvexPolytope.Isom 3) (F : Set E3) :
    ConvexPolytope.faceDim ((⇑φ) '' F) = ConvexPolytope.faceDim F := by
  unfold ConvexPolytope.faceDim
  have hmap := φ.toAffineEquiv.toAffineMap.map_vectorSpan (s := F)
  change Submodule.map (φ.toAffineEquiv.linear : E3 →ₗ[ℝ] E3) (vectorSpan ℝ F) =
    vectorSpan ℝ ((⇑φ) '' F) at hmap
  rw [← hmap]
  exact φ.toAffineEquiv.linear.finrank_map_eq (vectorSpan ℝ F)

theorem isFace_image_isom {P : ConvexPolytope 3} (φ : ConvexPolytope.Isom 3)
    (hφ : P.isSymmetry φ) {F : Set E3} (hF : P.IsFace F) :
    P.IsFace ((⇑φ) '' F) := by
  refine ⟨?_, hF.2.image _⟩
  rw [← hφ]
  exact isExposed_image_isom φ hF.1

theorem symmetry_refl (P : ConvexPolytope 3) :
    P.isSymmetry (AffineIsometryEquiv.refl ℝ E3) := by
  exact Set.image_id _

theorem symmetry_trans {P : ConvexPolytope 3} {φ ψ : ConvexPolytope.Isom 3}
    (hφ : P.isSymmetry φ) (hψ : P.isSymmetry ψ) :
    P.isSymmetry (φ.trans ψ) := by
  unfold ConvexPolytope.isSymmetry at *
  calc
    (⇑(φ.trans ψ)) '' P.toSet = (⇑ψ) '' ((⇑φ) '' P.toSet) := by
      rw [Set.image_image]
      rfl
    _ = P.toSet := by rw [hφ, hψ]

theorem symmetry_symm {P : ConvexPolytope 3} {φ : ConvexPolytope.Isom 3}
    (hφ : P.isSymmetry φ) : P.isSymmetry φ.symm := by
  unfold ConvexPolytope.isSymmetry at *
  calc
    (⇑φ.symm) '' P.toSet = (⇑φ.symm) '' ((⇑φ) '' P.toSet) := by rw [hφ]
    _ = P.toSet := φ.toEquiv.symm_image_image P.toSet

theorem zeroFace_is_vertex {P : ConvexPolytope 3} {F : Set E3}
    (hF : P.IsFace F) (hd : ConvexPolytope.faceDim F = 0) :
    ∃ v : E3, F = {v} ∧ v ∈ P.vertices := by
  obtain ⟨v, hv⟩ := hF.2
  have hspan : vectorSpan ℝ F = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    exact hd
  have hsingle : F = {v} := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxv := vsub_mem_vectorSpan ℝ hx hv
      rw [hspan] at hxv
      have : x - v = 0 := by simpa using hxv
      simpa using sub_eq_zero.mp this
    · exact Set.singleton_subset_iff.mpr hv
  refine ⟨v, hsingle, ?_⟩
  have hexposed : IsExposed ℝ P.toSet ({v} : Set E3) := by
    rw [← hsingle]
    exact hF.1
  have hvext : v ∈ P.toSet.extremePoints ℝ :=
    hexposed.isExtreme.mem_extremePoints
  rw [ConvexPolytope.toSet, ← P.vertices_eq_extremePoints] at hvext
  exact hvext

/-! ## I due politopi sul contratto -/

def cuboB : ConvexPolytope 3 where
  vertices := verticiCubo
  vertices_nonempty := ⟨c0, by simp [verticiCubo]⟩
  vertices_eq_extremePoints := cubo.vertices_eq_extremePoints

def ottaedroB : ConvexPolytope 3 where
  vertices := verticiOtta
  vertices_nonempty := ⟨o0, by simp [verticiOtta]⟩
  vertices_eq_extremePoints := ottaedro.vertices_eq_extremePoints

@[simp] theorem cuboB_vertices : cuboB.vertices = verticiCubo := rfl
@[simp] theorem ottaedroB_vertices : ottaedroB.vertices = verticiOtta := rfl

theorem cuboB_toSet : cuboB.toSet = cubo.toSet := rfl
theorem ottaedroB_toSet : ottaedroB.toSet = ottaedro.toSet := rfl

theorem cuboB_face_to_old {F : Set E3} (hF : cuboB.IsFace F) : cubo.IsFace F := by
  simpa only [ConvexPolytope.IsFace, FiniteConvexPolytope.IsFace,
    cuboB_toSet] using hF

theorem ottaedroB_face_to_old {F : Set E3} (hF : ottaedroB.IsFace F) :
    ottaedro.IsFace F := by
  simpa only [ConvexPolytope.IsFace, FiniteConvexPolytope.IsFace,
    ottaedroB_toSet] using hF

theorem cuboB_fullDim : cuboB.IsFullDim := by
  rw [ConvexPolytope.IsFullDim, ConvexPolytope.dim,
    ConvexPolytope.toSet, ← direction_affineSpan,
    affineSpan_convexHull, direction_affineSpan]
  exact cubo_finrank

theorem ottaedroB_fullDim : ottaedroB.IsFullDim := by
  rw [ConvexPolytope.IsFullDim, ConvexPolytope.dim,
    ConvexPolytope.toSet, ← direction_affineSpan,
    affineSpan_convexHull, direction_affineSpan]
  exact ottaedro_finrank

/-! ## Normalizzazione delle faccette -/

structure FaceNormalization (P : ConvexPolytope 3) (F C : Set E3) where
  φ : ConvexPolytope.Isom 3
  symmetry : P.isSymmetry φ
  image_eq : (⇑φ) '' F = C

def inverseFaceNormalization {P : ConvexPolytope 3} {C : Set E3}
    (g : ConvexPolytope.Isom 3) (hg : P.isSymmetry g) :
    FaceNormalization P ((⇑g) '' C) C where
  φ := g.symm
  symmetry := symmetry_symm hg
  image_eq := g.toEquiv.symm_image_image C

theorem cuboB_linear_symmetry (g : E3 ≃ₗᵢ[ℝ] E3)
    (hv : (⇑g) '' (verticiCubo : Set E3) = (verticiCubo : Set E3)) :
    cuboB.isSymmetry g.toAffineIsometryEquiv := by
  unfold ConvexPolytope.isSymmetry
  rw [cuboB_toSet]
  exact preserva_toSet_di_vertici g hv

theorem ottaedroB_linear_symmetry (g : E3 ≃ₗᵢ[ℝ] E3)
    (hv : (⇑g) '' (verticiOtta : Set E3) = (verticiOtta : Set E3)) :
    ottaedroB.isSymmetry g.toAffineIsometryEquiv := by
  unfold ConvexPolytope.isSymmetry
  rw [ottaedroB_toSet]
  exact preserva_toSet_otta g hv

abbrev cuboBaseFace : Set E3 := convexHull ℝ (facciaX1 : Set E3)
abbrev ottaBaseFace : Set E3 := convexHull ℝ (facciaOtta : Set E3)

theorem cubo_facet_normalization {F : Set E3} (hF : cuboB.IsFace F)
    (hd : ConvexPolytope.faceDim F = 2) :
    Nonempty (FaceNormalization cuboB F cuboBaseFace) := by
  have hOld : cubo.IsFacet F := by
    refine ⟨cuboB_face_to_old hF, ?_⟩
    exact hd
  rcases facet_classification_cubo hOld with h | h | h | h | h | h
  · subst F
    exact ⟨⟨AffineIsometryEquiv.refl ℝ E3, symmetry_refl cuboB,
      Set.image_id _⟩⟩
  · rw [← segnoX_F₀] at h
    subst F
    exact ⟨inverseFaceNormalization segnoX.toAffineIsometryEquiv
      (cuboB_linear_symmetry segnoX segnoX_vertset)⟩
  · rw [← scambioXY_F₀] at h
    subst F
    exact ⟨inverseFaceNormalization scambioXY.toAffineIsometryEquiv
      (cuboB_linear_symmetry scambioXY scambioXY_vertset)⟩
  · rw [← portaYm_F₀] at h
    subst F
    exact ⟨inverseFaceNormalization portaYm.toAffineIsometryEquiv
      (cuboB_linear_symmetry portaYm portaYm_vertset)⟩
  · rw [← scambioXZ_F₀] at h
    subst F
    exact ⟨inverseFaceNormalization scambioXZ.toAffineIsometryEquiv
      (cuboB_linear_symmetry scambioXZ scambioXZ_vertset)⟩
  · rw [← portaZm_F₀] at h
    subst F
    exact ⟨inverseFaceNormalization portaZm.toAffineIsometryEquiv
      (cuboB_linear_symmetry portaZm portaZm_vertset)⟩

theorem otta_facet_normalization {F : Set E3} (hF : ottaedroB.IsFace F)
    (hd : ConvexPolytope.faceDim F = 2) :
    Nonempty (FaceNormalization ottaedroB F ottaBaseFace) := by
  have hOld : ottaedro.IsFacet F := by
    refine ⟨ottaedroB_face_to_old hF, ?_⟩
    exact hd
  rcases facet_classification_otta hOld with h | h | h | h | h | h | h | h
  · subst F
    exact ⟨⟨AffineIsometryEquiv.refl ℝ E3, symmetry_refl ottaedroB,
      Set.image_id _⟩⟩
  · rw [← segnoX_T₀] at h
    subst F
    exact ⟨inverseFaceNormalization segnoX.toAffineIsometryEquiv
      (ottaedroB_linear_symmetry segnoX segnoX_overtset)⟩
  · rw [← segnoY_T₀] at h
    subst F
    exact ⟨inverseFaceNormalization segnoY.toAffineIsometryEquiv
      (ottaedroB_linear_symmetry segnoY segnoY_overtset)⟩
  · rw [← segnoZ_T₀] at h
    subst F
    exact ⟨inverseFaceNormalization segnoZ.toAffineIsometryEquiv
      (ottaedroB_linear_symmetry segnoZ segnoZ_overtset)⟩
  · rw [← sXY_T₀] at h
    subst F
    exact ⟨inverseFaceNormalization (segnoX.trans segnoY).toAffineIsometryEquiv
      (ottaedroB_linear_symmetry (segnoX.trans segnoY)
        (overtset_trans segnoX segnoY segnoX_overtset segnoY_overtset))⟩
  · rw [← sXZ_T₀] at h
    subst F
    exact ⟨inverseFaceNormalization (segnoX.trans segnoZ).toAffineIsometryEquiv
      (ottaedroB_linear_symmetry (segnoX.trans segnoZ)
        (overtset_trans segnoX segnoZ segnoX_overtset segnoZ_overtset))⟩
  · rw [← sYZ_T₀] at h
    subst F
    exact ⟨inverseFaceNormalization (segnoY.trans segnoZ).toAffineIsometryEquiv
      (ottaedroB_linear_symmetry (segnoY.trans segnoZ)
        (overtset_trans segnoY segnoZ segnoY_overtset segnoZ_overtset))⟩
  · rw [← sXYZ_T₀] at h
    subst F
    exact ⟨inverseFaceNormalization ((segnoX.trans segnoY).trans segnoZ).toAffineIsometryEquiv
      (ottaedroB_linear_symmetry ((segnoX.trans segnoY).trans segnoZ)
        (overtset_trans (segnoX.trans segnoY) segnoZ
          (overtset_trans segnoX segnoY segnoX_overtset segnoY_overtset)
          segnoZ_overtset))⟩

/-! ## Normalizzazione del vertice dentro la faccetta base -/

theorem rotFacciaX_vertset :
    (⇑rotFacciaX) '' (verticiCubo : Set E3) = (verticiCubo : Set E3) := by
  have hc4 : rotFacciaX c4 = c6 := by
    ext j
    fin_cases j <;>
      simp [rotFacciaX, scambioYZ, segnoY, c4, c6, Equiv.swap_apply_def,
        LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.piLpCongrRight]
  have hc5 : rotFacciaX c5 = c4 := by
    ext j
    fin_cases j <;>
      simp [rotFacciaX, scambioYZ, segnoY, c4, c5, Equiv.swap_apply_def,
        LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.piLpCongrRight]
  have hc6 : rotFacciaX c6 = c7 := by
    ext j
    fin_cases j <;>
      simp [rotFacciaX, scambioYZ, segnoY, c6, c7, Equiv.swap_apply_def,
        LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.piLpCongrRight]
  have hc7 : rotFacciaX c7 = c5 := by
    ext j
    fin_cases j <;>
      simp [rotFacciaX, scambioYZ, segnoY, c5, c7, Equiv.swap_apply_def,
        LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.piLpCongrRight]
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [rotX_c0, rotX_c1, rotX_c2, rotX_c3, hc4, hc5, hc6, hc7] <;>
      simp [verticiCubo]
  · intro hz
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨c1, by simp [verticiCubo], rotX_c1⟩
    · exact ⟨c3, by simp [verticiCubo], rotX_c3⟩
    · exact ⟨c0, by simp [verticiCubo], rotX_c0⟩
    · exact ⟨c2, by simp [verticiCubo], rotX_c2⟩
    · exact ⟨c5, by simp [verticiCubo], hc5⟩
    · exact ⟨c7, by simp [verticiCubo], hc7⟩
    · exact ⟨c4, by simp [verticiCubo], hc4⟩
    · exact ⟨c6, by simp [verticiCubo], hc6⟩

theorem cubo_base_vertex_cases {v : E3} (hv : v ∈ cuboB.vertices)
    (hvF : v ∈ cuboBaseFace) : v = c0 ∨ v = c2 ∨ v = c3 ∨ v = c1 := by
  have hvCube : v ∈ cubo.toSet := by
    exact subset_convexHull ℝ _ hv
  have hle := toSet_le_uno v hvCube
  have hge := F₀_ge_uno v hvF
  have heq : lX v = 1 := le_antisymm hle hge
  have hm : v ∈ {x ∈ (verticiCubo : Set E3) | lX x = 1} := ⟨hv, heq⟩
  rw [argmax_verticiX] at hm
  simpa [facciaX1] using hm

theorem otta_base_vertex_cases {v : E3} (hv : v ∈ ottaedroB.vertices)
    (hvF : v ∈ ottaBaseFace) : v = o0 ∨ v = o1 ∨ v = o2 := by
  have hvOtta : v ∈ ottaedro.toSet := by
    exact subset_convexHull ℝ _ hv
  have hle := toSet_otta_le v hvOtta
  have hge := T₀_ge_uno v hvF
  have heq : (lX + lY + lZ) v = 1 := le_antisymm hle hge
  have hm : v ∈ {x ∈ (verticiOtta : Set E3) | (lX + lY + lZ) x = 1} :=
    ⟨hv, heq⟩
  rw [argmax_verticiOtta] at hm
  simpa [facciaOtta] using hm

structure VertexFacetNormalization (P : ConvexPolytope 3)
    (F0 F2 C0 C2 : Set E3) where
  φ : ConvexPolytope.Isom 3
  symmetry : P.isSymmetry φ
  image_zero : (⇑φ) '' F0 = C0
  image_two : (⇑φ) '' F2 = C2

def extendFacetNormalization {P : ConvexPolytope 3} {F0 F2 C2 : Set E3}
    (n : FaceNormalization P F2 C2) (u v : E3)
    (hu : (⇑n.φ) '' F0 = {u})
    (r : ConvexPolytope.Isom 3) (hr : P.isSymmetry r)
    (hrC : (⇑r) '' C2 = C2) (hru : r u = v) :
    VertexFacetNormalization P F0 F2 ({v} : Set E3) C2 where
  φ := n.φ.trans r
  symmetry := symmetry_trans n.symmetry hr
  image_zero := by
    calc
      (⇑(n.φ.trans r)) '' F0 = (⇑r) '' ((⇑n.φ) '' F0) := by
        rw [Set.image_image]
        rfl
      _ = {v} := by simp [hu, hru]
  image_two := by
    calc
      (⇑(n.φ.trans r)) '' F2 = (⇑r) '' ((⇑n.φ) '' F2) := by
        rw [Set.image_image]
        rfl
      _ = C2 := by rw [n.image_eq, hrC]

theorem cubo_vertex_facet_normalization (F : cuboB.Flag) :
    Nonempty (VertexFacetNormalization cuboB (F.face 0) (F.face 2)
      ({c0} : Set E3) cuboBaseFace) := by
  let n := (cubo_facet_normalization (F.isFace 2) (by simpa using F.dim_eq 2)).some
  have h0face := isFace_image_isom n.φ n.symmetry (F.isFace 0)
  have h0dim : ConvexPolytope.faceDim ((⇑n.φ) '' F.face 0) = 0 := by
    rw [faceDim_image_isom, F.dim_eq]
    norm_num
  obtain ⟨u, hu, huvert⟩ := zeroFace_is_vertex h0face h0dim
  have h02 : F.face 0 ⊆ F.face 2 :=
    (F.strict_mono 0 2 (by decide)).1
  have huBase : u ∈ cuboBaseFace := by
    have hu0 : u ∈ (⇑n.φ) '' F.face 0 := by
      rw [hu]
      exact Set.mem_singleton u
    have hutwo := Set.image_mono h02 hu0
    rw [n.image_eq] at hutwo
    exact hutwo
  rcases cubo_base_vertex_cases huvert huBase with rfl | rfl | rfl | rfl
  · exact ⟨extendFacetNormalization n c0 c0 hu
      (AffineIsometryEquiv.refl ℝ E3) (symmetry_refl cuboB)
      (Set.image_id _) rfl⟩
  · exact ⟨extendFacetNormalization n c2 c0 hu
      rotFacciaX.toAffineIsometryEquiv.symm
      (symmetry_symm (cuboB_linear_symmetry rotFacciaX rotFacciaX_vertset))
      (by
        have hpres : (⇑rotFacciaX.toAffineIsometryEquiv) '' cuboBaseFace =
            cuboBaseFace := rotAffX_preserva_F₀
        calc
          (⇑rotFacciaX.toAffineIsometryEquiv.symm) '' cuboBaseFace =
              (⇑rotFacciaX.toAffineIsometryEquiv.symm) ''
                ((⇑rotFacciaX.toAffineIsometryEquiv) '' cuboBaseFace) := by
            exact congrArg (fun S : Set E3 =>
              (⇑rotFacciaX.toAffineIsometryEquiv.symm) '' S) hpres.symm
          _ = cuboBaseFace := by
            ext x
            constructor
            · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
              simpa only [AffineIsometryEquiv.symm_apply_apply] using hz
            · intro hx
              exact ⟨rotFacciaX.toAffineIsometryEquiv x,
                ⟨x, hx, rfl⟩,
                rotFacciaX.toAffineIsometryEquiv.symm_apply_apply x⟩)
      ((Equiv.symm_apply_eq rotFacciaX.toAffineIsometryEquiv.toEquiv).2
        rotX_c0.symm)⟩
  · let r := rotFacciaX.toAffineIsometryEquiv.trans rotFacciaX.toAffineIsometryEquiv
    have hrs : cuboB.isSymmetry r := symmetry_trans
      (cuboB_linear_symmetry rotFacciaX rotFacciaX_vertset)
      (cuboB_linear_symmetry rotFacciaX rotFacciaX_vertset)
    have hrF : (⇑r) '' cuboBaseFace = cuboBaseFace := by
      have hpres : (⇑rotFacciaX.toAffineIsometryEquiv) '' cuboBaseFace =
          cuboBaseFace := rotAffX_preserva_F₀
      calc
        (⇑r) '' cuboBaseFace = (⇑rotFacciaX.toAffineIsometryEquiv) ''
            ((⇑rotFacciaX.toAffineIsometryEquiv) '' cuboBaseFace) := by
          rw [Set.image_image]
          rfl
        _ = cuboBaseFace := by rw [hpres, hpres]
    have hrc3 : r c3 = c0 := by
      change rotFacciaX (rotFacciaX c3) = c0
      rw [rotX_c3, rotX_c1]
    exact ⟨extendFacetNormalization n c3 c0 hu r hrs hrF hrc3⟩
  · exact ⟨extendFacetNormalization n c1 c0 hu
      rotFacciaX.toAffineIsometryEquiv
      (cuboB_linear_symmetry rotFacciaX rotFacciaX_vertset)
      rotAffX_preserva_F₀ rotX_c1⟩

theorem otta_vertex_facet_normalization (F : ottaedroB.Flag) :
    Nonempty (VertexFacetNormalization ottaedroB (F.face 0) (F.face 2)
      ({o0} : Set E3) ottaBaseFace) := by
  let n := (otta_facet_normalization (F.isFace 2) (by simpa using F.dim_eq 2)).some
  have h0face := isFace_image_isom n.φ n.symmetry (F.isFace 0)
  have h0dim : ConvexPolytope.faceDim ((⇑n.φ) '' F.face 0) = 0 := by
    rw [faceDim_image_isom, F.dim_eq]
    norm_num
  obtain ⟨u, hu, huvert⟩ := zeroFace_is_vertex h0face h0dim
  have h02 : F.face 0 ⊆ F.face 2 :=
    (F.strict_mono 0 2 (by decide)).1
  have huBase : u ∈ ottaBaseFace := by
    have hu0 : u ∈ (⇑n.φ) '' F.face 0 := by
      rw [hu]
      exact Set.mem_singleton u
    have hutwo := Set.image_mono h02 hu0
    rw [n.image_eq] at hutwo
    exact hutwo
  rcases otta_base_vertex_cases huvert huBase with rfl | rfl | rfl
  · exact ⟨extendFacetNormalization n o0 o0 hu
      (AffineIsometryEquiv.refl ℝ E3) (symmetry_refl ottaedroB)
      (Set.image_id _) rfl⟩
  · let r := rotDiag.toAffineIsometryEquiv.trans rotDiag.toAffineIsometryEquiv
    have hrs : ottaedroB.isSymmetry r := symmetry_trans
      (ottaedroB_linear_symmetry rotDiag rotDiag_overtset)
      (ottaedroB_linear_symmetry rotDiag rotDiag_overtset)
    have hrF : (⇑r) '' ottaBaseFace = ottaBaseFace := by
      have hpres : (⇑rotDiag.toAffineIsometryEquiv) '' ottaBaseFace =
          ottaBaseFace := rotDiag_preserva_T₀
      calc
        (⇑r) '' ottaBaseFace = (⇑rotDiag.toAffineIsometryEquiv) ''
            ((⇑rotDiag.toAffineIsometryEquiv) '' ottaBaseFace) := by
          rw [Set.image_image]
          rfl
        _ = ottaBaseFace := by rw [hpres, hpres]
    have hro1 : r o1 = o0 := by
      change rotDiag (rotDiag o1) = o0
      rw [rotDiag_o.2.1, rotDiag_o.2.2.1]
    exact ⟨extendFacetNormalization n o1 o0 hu r hrs hrF hro1⟩
  · exact ⟨extendFacetNormalization n o2 o0 hu
      rotDiag.toAffineIsometryEquiv
      (ottaedroB_linear_symmetry rotDiag rotDiag_overtset)
      rotDiag_preserva_T₀ rotDiag_o.2.2.1⟩

/-! ## Classificazione dello spigolo nella bandiera normalizzata -/

theorem cubo_three_base_vertices_rank {H : Set E3}
    (h0 : c0 ∈ H) (h1 : c1 ∈ H) (h2 : c2 ∈ H) :
    2 ≤ ConvexPolytope.faceDim H := by
  have hsub : Submodule.span ℝ (Set.range ![d1, d2]) ≤ vectorSpan ℝ H := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · have hm := vsub_mem_vectorSpan ℝ h0 h2
      simpa [d1, vsub_eq_sub] using hm
    · have hm := vsub_mem_vectorSpan ℝ h0 h1
      simpa [d2, vsub_eq_sub] using hm
  have h2rank : Module.finrank ℝ (Submodule.span ℝ (Set.range ![d1, d2])) = 2 := by
    rw [finrank_span_eq_card indep_d]
    simp
  unfold ConvexPolytope.faceDim
  calc
    2 = Module.finrank ℝ (Submodule.span ℝ (Set.range ![d1, d2])) := h2rank.symm
    _ ≤ Module.finrank ℝ (vectorSpan ℝ H) := Submodule.finrank_mono hsub

theorem otta_three_base_vertices_rank {H : Set E3}
    (h0 : o0 ∈ H) (h1 : o1 ∈ H) (h2 : o2 ∈ H) :
    2 ≤ ConvexPolytope.faceDim H := by
  have hsub : Submodule.span ℝ (Set.range ![dOtta1, dOtta2]) ≤ vectorSpan ℝ H := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · have hm := vsub_mem_vectorSpan ℝ h0 h1
      simpa [dOtta1, vsub_eq_sub] using hm
    · have hm := vsub_mem_vectorSpan ℝ h0 h2
      simpa [dOtta2, vsub_eq_sub] using hm
  have h2rank : Module.finrank ℝ
      (Submodule.span ℝ (Set.range ![dOtta1, dOtta2])) = 2 := by
    rw [finrank_span_eq_card indep_dOtta]
    simp
  unfold ConvexPolytope.faceDim
  calc
    2 = Module.finrank ℝ
        (Submodule.span ℝ (Set.range ![dOtta1, dOtta2])) := h2rank.symm
    _ ≤ Module.finrank ℝ (vectorSpan ℝ H) := Submodule.finrank_mono hsub

theorem cubo_base_edge_cases {H : Set E3} (hH : cuboB.IsFace H)
    (hd : ConvexPolytope.faceDim H = 1) (hc0 : c0 ∈ H)
    (hsubBase : H ⊆ cuboBaseFace) :
    H = convexHull ℝ ({c0, c1} : Set E3) ∨
      H = convexHull ℝ ({c0, c2} : Set E3) := by
  classical
  have hOld := cuboB_face_to_old hH
  obtain ⟨l, hl⟩ := hOld.1 hOld.2
  have hFS := exposedFace_eq_convexHull_vertices_cubo hOld
  let S : Finset E3 := cubo.vertices.filter (· ∈ H)
  have hcrit : ∀ u ∈ (cubo.vertices : Set E3),
      (u ∈ (S : Set E3) ↔ ∀ w ∈ (cubo.vertices : Set E3), l w ≤ l u) := by
    intro u hu
    constructor
    · intro huS w hw
      have huH : u ∈ H := (Finset.mem_filter.mp (by exact_mod_cast huS)).2
      rw [hl] at huH
      exact huH.2 w (subset_convexHull ℝ _ hw)
    · intro hmax
      have huH : u ∈ H := by
        rw [hl]
        refine ⟨subset_convexHull ℝ _ hu, ?_⟩
        intro y hy
        exact convexHull_min hmax
          (convex_halfSpace_le (LinearMap.isLinear l.toLinearMap) (l u)) hy
      exact_mod_cast Finset.mem_filter.mpr ⟨by exact_mod_cast hu, huH⟩
  have hc0v : c0 ∈ (cubo.vertices : Set E3) := by simp [cubo, verticiCubo]
  have hc1v : c1 ∈ (cubo.vertices : Set E3) := by simp [cubo, verticiCubo]
  have hc2v : c2 ∈ (cubo.vertices : Set E3) := by simp [cubo, verticiCubo]
  have hc3v : c3 ∈ (cubo.vertices : Set E3) := by simp [cubo, verticiCubo]
  have hc0S : c0 ∈ (S : Set E3) := by
    exact_mod_cast Finset.mem_filter.mpr ⟨by exact_mod_cast hc0v, hc0⟩
  have hc3not : c3 ∉ (S : Set E3) := by
    intro hc3S
    have hm0 := (hcrit c0 hc0v).mp hc0S
    have hm3 := (hcrit c3 hc3v).mp hc3S
    have heq : l c0 = l c3 := le_antisymm (hm3 c0 hc0v) (hm0 c3 hc3v)
    have hb : 0 ≤ compL l 1 := by
      have h := hm0 c2 hc2v
      rw [l_c2, l_c0] at h
      linarith
    have hc : 0 ≤ compL l 2 := by
      have h := hm0 c1 hc1v
      rw [l_c1, l_c0] at h
      linarith
    rw [l_c0, l_c3] at heq
    have hb0 : compL l 1 = 0 := by linarith
    have hc0' : compL l 2 = 0 := by linarith
    have hc1S : c1 ∈ (S : Set E3) := (hcrit c1 hc1v).mpr (by
      intro w hw
      have h := hm0 w hw
      rw [l_c0, hb0, hc0'] at h
      rw [l_c1, hb0, hc0']
      linarith)
    have hc2S : c2 ∈ (S : Set E3) := (hcrit c2 hc2v).mpr (by
      intro w hw
      have h := hm0 w hw
      rw [l_c0, hb0, hc0'] at h
      rw [l_c2, hb0, hc0']
      linarith)
    have hc1H := (Finset.mem_filter.mp (by exact_mod_cast hc1S)).2
    have hc2H := (Finset.mem_filter.mp (by exact_mod_cast hc2S)).2
    have hrank := cubo_three_base_vertices_rank hc0 hc1H hc2H
    omega
  have hS_cases {u : E3} (hu : u ∈ (S : Set E3)) :
      u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
    have huf := Finset.mem_filter.mp (by exact_mod_cast hu)
    exact cubo_base_vertex_cases huf.1 (hsubBase huf.2)
  by_cases hc1S : c1 ∈ (S : Set E3)
  · by_cases hc2S : c2 ∈ (S : Set E3)
    · have hc1H := (Finset.mem_filter.mp (by exact_mod_cast hc1S)).2
      have hc2H := (Finset.mem_filter.mp (by exact_mod_cast hc2S)).2
      have hrank := cubo_three_base_vertices_rank hc0 hc1H hc2H
      omega
    · left
      rw [hFS]
      congr 1
      ext u
      constructor
      · intro hu
        rcases hS_cases hu with rfl | rfl | rfl | rfl
        · simp
        · exact absurd hu hc2S
        · exact absurd hu hc3not
        · simp
      · intro hu
        rcases (by simpa using hu : u = c0 ∨ u = c1) with rfl | rfl
        · exact hc0S
        · exact hc1S
  · by_cases hc2S : c2 ∈ (S : Set E3)
    · right
      rw [hFS]
      congr 1
      ext u
      constructor
      · intro hu
        rcases hS_cases hu with rfl | rfl | rfl | rfl
        · simp
        · simp
        · exact absurd hu hc3not
        · exact absurd hu hc1S
      · intro hu
        rcases (by simpa using hu : u = c0 ∨ u = c2) with rfl | rfl
        · exact hc0S
        · exact hc2S
    · exfalso
      have hSeq : (S : Set E3) = {c0} := by
        ext u
        constructor
        · intro hu
          rcases hS_cases hu with rfl | rfl | rfl | rfl
          · simp
          · exact absurd hu hc2S
          · exact absurd hu hc3not
          · exact absurd hu hc1S
        · intro hu
          simpa using hu ▸ hc0S
      rw [hFS, hSeq, convexHull_singleton] at hd
      unfold ConvexPolytope.faceDim at hd
      rw [vectorSpan_singleton] at hd
      norm_num at hd

theorem otta_base_edge_cases {H : Set E3} (hH : ottaedroB.IsFace H)
    (hd : ConvexPolytope.faceDim H = 1) (ho0 : o0 ∈ H)
    (hsubBase : H ⊆ ottaBaseFace) :
    H = convexHull ℝ ({o0, o1} : Set E3) ∨
      H = convexHull ℝ ({o0, o2} : Set E3) := by
  classical
  have hOld := ottaedroB_face_to_old hH
  have hFS := exposedFace_eq_convexHull_vertices_otta hOld
  let S : Finset E3 := ottaedro.vertices.filter (· ∈ H)
  have ho0S : o0 ∈ (S : Set E3) := by
    exact_mod_cast Finset.mem_filter.mpr ⟨by simp [ottaedro, verticiOtta], ho0⟩
  have hS_cases {u : E3} (hu : u ∈ (S : Set E3)) :
      u = o0 ∨ u = o1 ∨ u = o2 := by
    have huf := Finset.mem_filter.mp (by exact_mod_cast hu)
    exact otta_base_vertex_cases huf.1 (hsubBase huf.2)
  by_cases ho1S : o1 ∈ (S : Set E3)
  · by_cases ho2S : o2 ∈ (S : Set E3)
    · have ho1H := (Finset.mem_filter.mp (by exact_mod_cast ho1S)).2
      have ho2H := (Finset.mem_filter.mp (by exact_mod_cast ho2S)).2
      have hrank := otta_three_base_vertices_rank ho0 ho1H ho2H
      omega
    · left
      rw [hFS]
      congr 1
      ext u
      constructor
      · intro hu
        rcases hS_cases hu with rfl | rfl | rfl
        · simp
        · simp
        · exact absurd hu ho2S
      · intro hu
        rcases (by simpa using hu : u = o0 ∨ u = o1) with rfl | rfl
        · exact ho0S
        · exact ho1S
  · by_cases ho2S : o2 ∈ (S : Set E3)
    · right
      rw [hFS]
      congr 1
      ext u
      constructor
      · intro hu
        rcases hS_cases hu with rfl | rfl | rfl
        · simp
        · exact absurd hu ho1S
        · simp
      · intro hu
        rcases (by simpa using hu : u = o0 ∨ u = o2) with rfl | rfl
        · exact ho0S
        · exact ho2S
    · exfalso
      have hSeq : (S : Set E3) = {o0} := by
        ext u
        constructor
        · intro hu
          rcases hS_cases hu with rfl | rfl | rfl
          · simp
          · exact absurd hu ho1S
          · exact absurd hu ho2S
        · intro hu
          simpa using hu ▸ ho0S
      rw [hFS, hSeq, convexHull_singleton] at hd
      unfold ConvexPolytope.faceDim at hd
      rw [vectorSpan_singleton] at hd
      norm_num at hd

/-! ## Lo scambio finale dei due spigoli della faccetta base -/

theorem scambioYZ_cubo_actions :
    scambioYZ c0 = c0 ∧ scambioYZ c1 = c2 ∧ scambioYZ c2 = c1 ∧
    scambioYZ c3 = c3 ∧ scambioYZ c4 = c4 ∧ scambioYZ c5 = c6 ∧
    scambioYZ c6 = c5 ∧ scambioYZ c7 = c7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j; fin_cases j <;>
      simp [scambioYZ, c0, c1, c2, c3, c4, c5, c6, c7,
        Equiv.swap_apply_def, LinearIsometryEquiv.piLpCongrLeft])

theorem scambioYZ_otta_actions :
    scambioYZ o0 = o0 ∧ scambioYZ o1 = o2 ∧ scambioYZ o2 = o1 ∧
    scambioYZ o3 = o3 ∧ scambioYZ o4 = o5 ∧ scambioYZ o5 = o4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j; fin_cases j <;>
      simp [scambioYZ, o0, o1, o2, o3, o4, o5,
        Equiv.swap_apply_def, LinearIsometryEquiv.piLpCongrLeft])

theorem scambioYZ_cubo_vertset :
    (⇑scambioYZ) '' (verticiCubo : Set E3) = (verticiCubo : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [scambioYZ_cubo_actions.1, scambioYZ_cubo_actions.2.1,
        scambioYZ_cubo_actions.2.2.1, scambioYZ_cubo_actions.2.2.2.1,
        scambioYZ_cubo_actions.2.2.2.2.1, scambioYZ_cubo_actions.2.2.2.2.2.1,
        scambioYZ_cubo_actions.2.2.2.2.2.2.1,
        scambioYZ_cubo_actions.2.2.2.2.2.2.2] <;> simp [verticiCubo]
  · intro hz
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨c0, by simp [verticiCubo], scambioYZ_cubo_actions.1⟩
    · exact ⟨c2, by simp [verticiCubo], scambioYZ_cubo_actions.2.2.1⟩
    · exact ⟨c1, by simp [verticiCubo], scambioYZ_cubo_actions.2.1⟩
    · exact ⟨c3, by simp [verticiCubo], scambioYZ_cubo_actions.2.2.2.1⟩
    · exact ⟨c4, by simp [verticiCubo], scambioYZ_cubo_actions.2.2.2.2.1⟩
    · exact ⟨c6, by simp [verticiCubo], scambioYZ_cubo_actions.2.2.2.2.2.2.1⟩
    · exact ⟨c5, by simp [verticiCubo], scambioYZ_cubo_actions.2.2.2.2.2.1⟩
    · exact ⟨c7, by simp [verticiCubo], scambioYZ_cubo_actions.2.2.2.2.2.2.2⟩

theorem scambioYZ_otta_vertset :
    (⇑scambioYZ) '' (verticiOtta : Set E3) = (verticiOtta : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [scambioYZ_otta_actions.1, scambioYZ_otta_actions.2.1,
        scambioYZ_otta_actions.2.2.1, scambioYZ_otta_actions.2.2.2.1,
        scambioYZ_otta_actions.2.2.2.2.1, scambioYZ_otta_actions.2.2.2.2.2] <;>
      simp [verticiOtta]
  · intro hz
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hz) with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨o0, by simp [verticiOtta], scambioYZ_otta_actions.1⟩
    · exact ⟨o2, by simp [verticiOtta], scambioYZ_otta_actions.2.2.1⟩
    · exact ⟨o1, by simp [verticiOtta], scambioYZ_otta_actions.2.1⟩
    · exact ⟨o3, by simp [verticiOtta], scambioYZ_otta_actions.2.2.2.1⟩
    · exact ⟨o5, by simp [verticiOtta], scambioYZ_otta_actions.2.2.2.2.2⟩
    · exact ⟨o4, by simp [verticiOtta], scambioYZ_otta_actions.2.2.2.2.1⟩

theorem image_convexHull_isom (φ : ConvexPolytope.Isom 3) (S : Set E3) :
    (⇑φ) '' convexHull ℝ S = convexHull ℝ ((⇑φ) '' S) := by
  simpa only [AffineEquiv.coe_toAffineMap, AffineIsometryEquiv.coe_toAffineEquiv] using
    φ.toAffineEquiv.toAffineMap.image_convexHull S

theorem scambioYZ_cubo_base :
    (⇑scambioYZ.toAffineIsometryEquiv) '' cuboBaseFace = cuboBaseFace := by
  rw [image_convexHull_isom]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases (by simpa [facciaX1] using hu : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1) with
      rfl | rfl | rfl | rfl
    all_goals simp [facciaX1, scambioYZ_cubo_actions.1,
      scambioYZ_cubo_actions.2.1, scambioYZ_cubo_actions.2.2.1,
      scambioYZ_cubo_actions.2.2.2.1]
  · intro hz
    rcases (by simpa [facciaX1] using hz : z = c0 ∨ z = c2 ∨ z = c3 ∨ z = c1) with
      rfl | rfl | rfl | rfl
    · exact ⟨c0, by simp [facciaX1], scambioYZ_cubo_actions.1⟩
    · exact ⟨c1, by simp [facciaX1], scambioYZ_cubo_actions.2.1⟩
    · exact ⟨c3, by simp [facciaX1], scambioYZ_cubo_actions.2.2.2.1⟩
    · exact ⟨c2, by simp [facciaX1], scambioYZ_cubo_actions.2.2.1⟩

theorem scambioYZ_otta_base :
    (⇑scambioYZ.toAffineIsometryEquiv) '' ottaBaseFace = ottaBaseFace := by
  rw [image_convexHull_isom]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases (by simpa [facciaOtta] using hu : u = o0 ∨ u = o1 ∨ u = o2) with
      rfl | rfl | rfl
    all_goals simp [facciaOtta, scambioYZ_otta_actions.1,
      scambioYZ_otta_actions.2.1, scambioYZ_otta_actions.2.2.1]
  · intro hz
    rcases (by simpa [facciaOtta] using hz : z = o0 ∨ z = o1 ∨ z = o2) with
      rfl | rfl | rfl
    · exact ⟨o0, by simp [facciaOtta], scambioYZ_otta_actions.1⟩
    · exact ⟨o2, by simp [facciaOtta], scambioYZ_otta_actions.2.2.1⟩
    · exact ⟨o1, by simp [facciaOtta], scambioYZ_otta_actions.2.1⟩

abbrev cuboBaseEdge : Set E3 := convexHull ℝ ({c0, c1} : Set E3)
abbrev cuboOtherEdge : Set E3 := convexHull ℝ ({c0, c2} : Set E3)
abbrev ottaBaseEdge : Set E3 := convexHull ℝ ({o0, o1} : Set E3)
abbrev ottaOtherEdge : Set E3 := convexHull ℝ ({o0, o2} : Set E3)

theorem scambioYZ_cubo_edge :
    (⇑scambioYZ.toAffineIsometryEquiv) '' cuboOtherEdge = cuboBaseEdge := by
  rw [image_convexHull_isom]
  congr 1
  ext z
  simp [scambioYZ_cubo_actions.1, scambioYZ_cubo_actions.2.2.1, eq_comm]

theorem scambioYZ_otta_edge :
    (⇑scambioYZ.toAffineIsometryEquiv) '' ottaOtherEdge = ottaBaseEdge := by
  rw [image_convexHull_isom]
  congr 1
  ext z
  simp [scambioYZ_otta_actions.1, scambioYZ_otta_actions.2.2.1, eq_comm]

/-! ## Bandiere canoniche e transitività -/

structure FlagNormalization {P : ConvexPolytope 3} (F : P.Flag)
    (C0 C1 C2 : Set E3) where
  φ : ConvexPolytope.Isom 3
  symmetry : P.isSymmetry φ
  image_zero : (⇑φ) '' F.face 0 = C0
  image_one : (⇑φ) '' F.face 1 = C1
  image_two : (⇑φ) '' F.face 2 = C2

def finishFlagNormalization {P : ConvexPolytope 3} (F : P.Flag)
    {C0 C1 C2 : Set E3}
    (p : VertexFacetNormalization P (F.face 0) (F.face 2) C0 C2)
    (r : ConvexPolytope.Isom 3) (hr : P.isSymmetry r)
    (hr0 : (⇑r) '' C0 = C0) (hr2 : (⇑r) '' C2 = C2)
    (hr1 : (⇑r) '' ((⇑p.φ) '' F.face 1) = C1) :
    FlagNormalization F C0 C1 C2 where
  φ := p.φ.trans r
  symmetry := symmetry_trans p.symmetry hr
  image_zero := by
    calc
      (⇑(p.φ.trans r)) '' F.face 0 =
          (⇑r) '' ((⇑p.φ) '' F.face 0) := by
        rw [Set.image_image]
        rfl
      _ = C0 := by rw [p.image_zero, hr0]
  image_one := by
    calc
      (⇑(p.φ.trans r)) '' F.face 1 =
          (⇑r) '' ((⇑p.φ) '' F.face 1) := by
        rw [Set.image_image]
        rfl
      _ = C1 := hr1
  image_two := by
    calc
      (⇑(p.φ.trans r)) '' F.face 2 =
          (⇑r) '' ((⇑p.φ) '' F.face 2) := by
        rw [Set.image_image]
        rfl
      _ = C2 := by rw [p.image_two, hr2]

theorem cubo_flag_normalization (F : cuboB.Flag) :
    Nonempty (FlagNormalization F ({c0} : Set E3) cuboBaseEdge cuboBaseFace) := by
  let p := (cubo_vertex_facet_normalization F).some
  have h1face := isFace_image_isom p.φ p.symmetry (F.isFace 1)
  have h1dim : ConvexPolytope.faceDim ((⇑p.φ) '' F.face 1) = 1 := by
    rw [faceDim_image_isom, F.dim_eq]
    norm_num
  have h01 : F.face 0 ⊆ F.face 1 := (F.strict_mono 0 1 (by decide)).1
  have hc0 : c0 ∈ (⇑p.φ) '' F.face 1 := by
    have hc0zero : c0 ∈ (⇑p.φ) '' F.face 0 := by
      rw [p.image_zero]
      exact Set.mem_singleton c0
    exact Set.image_mono h01 hc0zero
  have h12 : F.face 1 ⊆ F.face 2 := (F.strict_mono 1 2 (by decide)).1
  have hsub : (⇑p.φ) '' F.face 1 ⊆ cuboBaseFace := by
    intro x hx
    have := Set.image_mono h12 hx
    rw [p.image_two] at this
    exact this
  rcases cubo_base_edge_cases h1face h1dim hc0 hsub with h | h
  · exact ⟨finishFlagNormalization F p (AffineIsometryEquiv.refl ℝ E3)
      (symmetry_refl cuboB) (Set.image_id _) (Set.image_id _) (by
        rw [h]
        exact Set.image_id _)⟩
  · exact ⟨finishFlagNormalization F p scambioYZ.toAffineIsometryEquiv
      (cuboB_linear_symmetry scambioYZ scambioYZ_cubo_vertset)
      (by simp [scambioYZ_cubo_actions.1]) scambioYZ_cubo_base (by
        rw [h]
        exact scambioYZ_cubo_edge)⟩

theorem otta_flag_normalization (F : ottaedroB.Flag) :
    Nonempty (FlagNormalization F ({o0} : Set E3) ottaBaseEdge ottaBaseFace) := by
  let p := (otta_vertex_facet_normalization F).some
  have h1face := isFace_image_isom p.φ p.symmetry (F.isFace 1)
  have h1dim : ConvexPolytope.faceDim ((⇑p.φ) '' F.face 1) = 1 := by
    rw [faceDim_image_isom, F.dim_eq]
    norm_num
  have h01 : F.face 0 ⊆ F.face 1 := (F.strict_mono 0 1 (by decide)).1
  have ho0 : o0 ∈ (⇑p.φ) '' F.face 1 := by
    have ho0zero : o0 ∈ (⇑p.φ) '' F.face 0 := by
      rw [p.image_zero]
      exact Set.mem_singleton o0
    exact Set.image_mono h01 ho0zero
  have h12 : F.face 1 ⊆ F.face 2 := (F.strict_mono 1 2 (by decide)).1
  have hsub : (⇑p.φ) '' F.face 1 ⊆ ottaBaseFace := by
    intro x hx
    have := Set.image_mono h12 hx
    rw [p.image_two] at this
    exact this
  rcases otta_base_edge_cases h1face h1dim ho0 hsub with h | h
  · exact ⟨finishFlagNormalization F p (AffineIsometryEquiv.refl ℝ E3)
      (symmetry_refl ottaedroB) (Set.image_id _) (Set.image_id _) (by
        rw [h]
        exact Set.image_id _)⟩
  · exact ⟨finishFlagNormalization F p scambioYZ.toAffineIsometryEquiv
      (ottaedroB_linear_symmetry scambioYZ scambioYZ_otta_vertset)
      (by simp [scambioYZ_otta_actions.1]) scambioYZ_otta_base (by
        rw [h]
        exact scambioYZ_otta_edge)⟩

theorem symm_image_eq_of_image_eq (φ : ConvexPolytope.Isom 3)
    {A C : Set E3} (h : (⇑φ) '' A = C) : (⇑φ.symm) '' C = A := by
  calc
    (⇑φ.symm) '' C = (⇑φ.symm) '' ((⇑φ) '' A) := by
      exact congrArg (fun S : Set E3 => (⇑φ.symm) '' S) h.symm
    _ = A := by
      ext x
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        simpa only [AffineIsometryEquiv.symm_apply_apply] using ha
      · intro hx
        exact ⟨φ x, ⟨x, hx, rfl⟩, φ.symm_apply_apply x⟩

theorem image_between_normalizations {φ ψ : ConvexPolytope.Isom 3}
    {A B C : Set E3} (hφ : (⇑φ) '' A = C) (hψ : (⇑ψ) '' B = C) :
    (⇑(φ.trans ψ.symm)) '' A = B := by
  calc
    (⇑(φ.trans ψ.symm)) '' A = (⇑ψ.symm) '' ((⇑φ) '' A) := by
      rw [Set.image_image]
      rfl
    _ = (⇑ψ.symm) '' C := congrArg (fun S : Set E3 => (⇑ψ.symm) '' S) hφ
    _ = B := symm_image_eq_of_image_eq ψ hψ

/-! ## CONSEGNA -/

theorem cuboB_isRegular : cuboB.IsRegular := by
  refine ⟨cuboB_fullDim, ?_⟩
  intro F G
  let f := (cubo_flag_normalization F).some
  let g := (cubo_flag_normalization G).some
  refine ⟨f.φ.trans g.φ.symm, symmetry_trans f.symmetry (symmetry_symm g.symmetry), ?_⟩
  intro k
  fin_cases k
  · exact image_between_normalizations f.image_zero g.image_zero
  · exact image_between_normalizations f.image_one g.image_one
  · exact image_between_normalizations f.image_two g.image_two

theorem ottaedroB_isRegular : ottaedroB.IsRegular := by
  refine ⟨ottaedroB_fullDim, ?_⟩
  intro F G
  let f := (otta_flag_normalization F).some
  let g := (otta_flag_normalization G).some
  refine ⟨f.φ.trans g.φ.symm, symmetry_trans f.symmetry (symmetry_symm g.symmetry), ?_⟩
  intro k
  fin_cases k
  · exact image_between_normalizations f.image_zero g.image_zero
  · exact image_between_normalizations f.image_one g.image_one
  · exact image_between_normalizations f.image_two g.image_two


end F11

namespace F12

open scoped Topology
open ConvexPolytope



def dodecaedroB : ConvexPolytope 3 where
  vertices := verticiDodeca
  vertices_nonempty := dodecaedro.nonempty
  vertices_eq_extremePoints := dodecaedro.vertices_eq_extremePoints

def icosaedroB : ConvexPolytope 3 where
  vertices := verticiIcosa
  vertices_nonempty := icosaedro.nonempty
  vertices_eq_extremePoints := icosaedro.vertices_eq_extremePoints

@[simp] theorem dodecaedroB_vertices : dodecaedroB.vertices = verticiDodeca := rfl
@[simp] theorem icosaedroB_vertices : icosaedroB.vertices = verticiIcosa := rfl

theorem dodecaedroB_toSet : dodecaedroB.toSet = dodecaedro.toSet := rfl
theorem icosaedroB_toSet : icosaedroB.toSet = icosaedro.toSet := rfl

/-! ## Trasporto affine e ponti con i testimoni di fase 1b -/

theorem isExposed_image_isom (φ : ConvexPolytope.Isom 3) {A B : Set E3}
    (h : IsExposed ℝ A B) : IsExposed ℝ ((⇑φ) '' A) ((⇑φ) '' B) := by
  intro hne
  obtain ⟨b, hbB⟩ := hne
  obtain ⟨a, haB, hab⟩ := hbB
  obtain ⟨l, hl⟩ := h ⟨a, haB⟩
  let l' : E3 →L[ℝ] ℝ :=
    l.comp φ.symm.linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
  have hl' (x : E3) : l' (φ x) = l x - l (φ.symm 0) := by
    have hm := φ.symm.map_vsub (φ x) 0
    have hm' : φ.symm.linearIsometryEquiv (φ x) = x - φ.symm 0 := by
      simpa using hm
    simp only [l', ContinuousLinearMap.comp_apply]
    change l (φ.symm.linearIsometryEquiv (φ x)) = _
    rw [hm', map_sub]
  refine ⟨l', Set.ext ?_⟩
  intro x
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [hl] at hb
    refine ⟨⟨b, hb.1, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [hl' y, hl' b]
    exact sub_le_sub_right (hb.2 y hy) _
  · rintro ⟨hxA, hxmax⟩
    obtain ⟨a, ha, rfl⟩ := hxA
    refine ⟨a, ?_, rfl⟩
    rw [hl]
    refine ⟨ha, ?_⟩
    intro y hy
    have hle := hxmax (φ y) ⟨y, hy, rfl⟩
    rw [hl' y, hl' a] at hle
    linarith

theorem faceDim_image_isom (φ : ConvexPolytope.Isom 3) (F : Set E3) :
    ConvexPolytope.faceDim ((⇑φ) '' F) = ConvexPolytope.faceDim F := by
  unfold ConvexPolytope.faceDim
  have hmap := φ.toAffineEquiv.toAffineMap.map_vectorSpan (s := F)
  change Submodule.map (φ.toAffineEquiv.linear : E3 →ₗ[ℝ] E3) (vectorSpan ℝ F) =
    vectorSpan ℝ ((⇑φ) '' F) at hmap
  rw [← hmap]
  exact φ.toAffineEquiv.linear.finrank_map_eq (vectorSpan ℝ F)

theorem isFace_image_isom {P : ConvexPolytope 3} (φ : ConvexPolytope.Isom 3)
    (hφ : P.isSymmetry φ) {F : Set E3} (hF : P.IsFace F) :
    P.IsFace ((⇑φ) '' F) := by
  refine ⟨?_, hF.2.image _⟩
  rw [← hφ]
  exact isExposed_image_isom φ hF.1

theorem symmetry_refl (P : ConvexPolytope 3) :
    P.isSymmetry (AffineIsometryEquiv.refl ℝ E3) := by
  exact Set.image_id _

theorem symmetry_trans {P : ConvexPolytope 3} {φ ψ : ConvexPolytope.Isom 3}
    (hφ : P.isSymmetry φ) (hψ : P.isSymmetry ψ) :
    P.isSymmetry (φ.trans ψ) := by
  unfold ConvexPolytope.isSymmetry at *
  calc
    (⇑(φ.trans ψ)) '' P.toSet = (⇑ψ) '' ((⇑φ) '' P.toSet) := by
      rw [Set.image_image]
      rfl
    _ = P.toSet := by rw [hφ, hψ]

theorem symmetry_symm {P : ConvexPolytope 3} {φ : ConvexPolytope.Isom 3}
    (hφ : P.isSymmetry φ) : P.isSymmetry φ.symm := by
  unfold ConvexPolytope.isSymmetry at *
  calc
    (⇑φ.symm) '' P.toSet = (⇑φ.symm) '' ((⇑φ) '' P.toSet) := by rw [hφ]
    _ = P.toSet := φ.toEquiv.symm_image_image P.toSet

theorem zeroFace_is_vertex {P : ConvexPolytope 3} {F : Set E3}
    (hF : P.IsFace F) (hd : ConvexPolytope.faceDim F = 0) :
    ∃ v : E3, F = {v} ∧ v ∈ P.vertices := by
  obtain ⟨v, hv⟩ := hF.2
  have hspan : vectorSpan ℝ F = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    exact hd
  have hsingle : F = {v} := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxv := vsub_mem_vectorSpan ℝ hx hv
      rw [hspan] at hxv
      have : x - v = 0 := by simpa using hxv
      simpa using sub_eq_zero.mp this
    · exact Set.singleton_subset_iff.mpr hv
  refine ⟨v, hsingle, ?_⟩
  have hexposed : IsExposed ℝ P.toSet ({v} : Set E3) := by
    rw [← hsingle]
    exact hF.1
  have hvext : v ∈ P.toSet.extremePoints ℝ :=
    hexposed.isExtreme.mem_extremePoints
  rw [ConvexPolytope.toSet, ← P.vertices_eq_extremePoints] at hvext
  exact hvext

theorem dodecaedroB_face_to_old {F : Set E3} (hF : dodecaedroB.IsFace F) :
    dodecaedro.IsFace F := by
  simpa only [ConvexPolytope.IsFace, FiniteConvexPolytope.IsFace,
    dodecaedroB_toSet] using hF

theorem icosaedroB_face_to_old {F : Set E3} (hF : icosaedroB.IsFace F) :
    icosaedro.IsFace F := by
  simpa only [ConvexPolytope.IsFace, FiniteConvexPolytope.IsFace,
    icosaedroB_toSet] using hF

theorem dodecaedroB_symmetry {g : E3 ≃ᵃⁱ[ℝ] E3}
    (hg : (⇑g) '' dodecaedro.toSet = dodecaedro.toSet) :
    dodecaedroB.isSymmetry g := by
  simpa only [ConvexPolytope.isSymmetry, dodecaedroB_toSet] using hg

theorem icosaedroB_symmetry {g : E3 ≃ᵃⁱ[ℝ] E3}
    (hg : (⇑g) '' icosaedro.toSet = icosaedro.toSet) :
    icosaedroB.isSymmetry g := by
  simpa only [ConvexPolytope.isSymmetry, icosaedroB_toSet] using hg

theorem dodecaedroB_fullDim : dodecaedroB.IsFullDim := by
  rw [ConvexPolytope.IsFullDim, ConvexPolytope.dim,
    ConvexPolytope.toSet, ← direction_affineSpan,
    affineSpan_convexHull, direction_affineSpan]
  exact dodecaedro_finrank

theorem icosaedroB_fullDim : icosaedroB.IsFullDim := by
  rw [ConvexPolytope.IsFullDim, ConvexPolytope.dim,
    ConvexPolytope.toSet, ← direction_affineSpan,
    affineSpan_convexHull, direction_affineSpan]
  exact icosaedro_finrank

/-! ## Normalizzazione simultanea di vertice e faccetta -/

structure VertexFacetNormalization {P : ConvexPolytope 3} (F : P.Flag)
    (C0 C2 : Set E3) where
  φ : ConvexPolytope.Isom 3
  symmetry : P.isSymmetry φ
  image_zero : (⇑φ) '' F.face 0 = C0
  image_two : (⇑φ) '' F.face 2 = C2

def finishVertexFacetNormalization {P : ConvexPolytope 3} (F : P.Flag)
    {C0 C2 D0 D2 : Set E3}
    (q : ConvexPolytope.Isom 3) (hq : P.isSymmetry q)
    (hq0 : (⇑q) '' F.face 0 = D0) (hq2 : (⇑q) '' F.face 2 = D2)
    (r : ConvexPolytope.Isom 3) (hr : P.isSymmetry r)
    (hr0 : (⇑r) '' D0 = C0) (hr2 : (⇑r) '' D2 = C2) :
    VertexFacetNormalization F C0 C2 where
  φ := q.trans r
  symmetry := symmetry_trans hq hr
  image_zero := by
    calc
      (⇑(q.trans r)) '' F.face 0 = (⇑r) '' ((⇑q) '' F.face 0) := by
        rw [Set.image_image]
        rfl
      _ = C0 := by rw [hq0, hr0]
  image_two := by
    calc
      (⇑(q.trans r)) '' F.face 2 = (⇑r) '' ((⇑q) '' F.face 2) := by
        rw [Set.image_image]
        rfl
      _ = C2 := by rw [hq2, hr2]

theorem symm_image_eq_of_image_eq (φ : ConvexPolytope.Isom 3)
    {A C : Set E3} (h : (⇑φ) '' A = C) : (⇑φ.symm) '' C = A := by
  calc
    (⇑φ.symm) '' C = (⇑φ.symm) '' ((⇑φ) '' A) := by
      exact congrArg (fun S : Set E3 => (⇑φ.symm) '' S) h.symm
    _ = A := φ.toEquiv.symm_image_image A

theorem dodecaedro_vertex_facet_normalization (F : dodecaedroB.Flag) :
    Nonempty (VertexFacetNormalization F ({a7} : Set E3) (fanFace 0)) := by
  obtain ⟨v, hF0, hv⟩ := zeroFace_is_vertex (F.isFace 0) (by
    simpa using F.dim_eq 0)
  obtain ⟨g, hg, hgv⟩ := dodecaedro_vertex_transitive v (by
    change v ∈ verticiDodeca
    exact hv)
  have hgs : (⇑g.symm) '' dodecaedro.toSet = dodecaedro.toSet :=
    FiniteConvexPolytope.preserva_symm g hg
  have hgB : dodecaedroB.isSymmetry g.symm := dodecaedroB_symmetry hgs
  have hg0 : (⇑g.symm) '' F.face 0 = ({a7} : Set E3) := by
    rw [hF0]
    ext z
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, rfl, rfl⟩
      simpa [v₀, a7] using (congrArg g.symm hgv).symm
    · rintro rfl
      refine ⟨v, rfl, ?_⟩
      simpa [v₀, a7] using (congrArg g.symm hgv).symm
  have h2face := isFace_image_isom g.symm hgB (F.isFace 2)
  have h2dim : ConvexPolytope.faceDim ((⇑g.symm) '' F.face 2) = 2 := by
    rw [faceDim_image_isom, F.dim_eq]
    norm_num
  have h2old : dodecaedro.IsFacet ((⇑g.symm) '' F.face 2) :=
    ⟨dodecaedroB_face_to_old h2face, h2dim⟩
  have h02 : F.face 0 ⊆ F.face 2 := (F.strict_mono 0 2 (by decide)).1
  have ha7 : a7 ∈ (⇑g.symm) '' F.face 2 := by
    have : a7 ∈ (⇑g.symm) '' F.face 0 := by rw [hg0]; simp
    exact Set.image_mono h02 this
  obtain ⟨i, hi⟩ := incident_facet_classification h2old ha7
  fin_cases i
  · exact ⟨finishVertexFacetNormalization F g.symm hgB hg0 hi
      (AffineIsometryEquiv.refl ℝ E3) (symmetry_refl dodecaedroB)
      (Set.image_id _) (Set.image_id _)⟩
  · have hsB : dodecaedroB.isSymmetry σ :=
      dodecaedroB_symmetry sigma_preserves_polytope
    have hs0 : (⇑σ.symm) '' ({a7} : Set E3) = ({a7} : Set E3) := by
      have hfix : σ.symm a7 = a7 := by
        exact (Equiv.symm_apply_eq σ.toEquiv).2 sigma_a7.symm
      simp only [Set.image_singleton, hfix]
    have hs2 : (⇑σ.symm) '' fanFace 1 = fanFace 0 := by
      exact symm_image_eq_of_image_eq σ (by simpa using sigma_image_fanFace (0 : Fin 3))
    exact ⟨finishVertexFacetNormalization F g.symm hgB hg0 hi σ.symm
      (symmetry_symm hsB) hs0 hs2⟩
  · have hsB : dodecaedroB.isSymmetry σ :=
      dodecaedroB_symmetry sigma_preserves_polytope
    have hs0 : (⇑σ) '' ({a7} : Set E3) = ({a7} : Set E3) := by
      simp [sigma_a7]
    have hs2 : (⇑σ) '' fanFace 2 = fanFace 0 := by
      simpa using sigma_image_fanFace (2 : Fin 3)
    exact ⟨finishVertexFacetNormalization F g.symm hgB hg0 hi σ hsB hs0 hs2⟩

theorem icosaedro_vertex_facet_normalization (F : icosaedroB.Flag) :
    Nonempty (VertexFacetNormalization F ({a3I} : Set E3) (fanFaceI 0)) := by
  obtain ⟨v, hF0, hv⟩ := zeroFace_is_vertex (F.isFace 0) (by
    simpa using F.dim_eq 0)
  obtain ⟨g, hg, hgv⟩ := icosaedro_vertex_transitive v (by
    change v ∈ verticiIcosa
    exact hv)
  have hgs : (⇑g.symm) '' icosaedro.toSet = icosaedro.toSet :=
    FiniteConvexPolytope.preserva_symm g hg
  have hgB : icosaedroB.isSymmetry g.symm := icosaedroB_symmetry hgs
  have hg0 : (⇑g.symm) '' F.face 0 = ({a3I} : Set E3) := by
    rw [hF0]
    ext z
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, rfl, rfl⟩
      exact (congrArg g.symm hgv).symm.trans (g.symm_apply_apply a3I)
    · rintro rfl
      exact ⟨v, rfl, (congrArg g.symm hgv).symm.trans (g.symm_apply_apply a3I)⟩
  have h2face := isFace_image_isom g.symm hgB (F.isFace 2)
  have h2dim : ConvexPolytope.faceDim ((⇑g.symm) '' F.face 2) = 2 := by
    rw [faceDim_image_isom, F.dim_eq]
    norm_num
  have h2old : icosaedro.IsFacet ((⇑g.symm) '' F.face 2) :=
    ⟨icosaedroB_face_to_old h2face, h2dim⟩
  have h02 : F.face 0 ⊆ F.face 2 := (F.strict_mono 0 2 (by decide)).1
  have ha3 : a3I ∈ (⇑g.symm) '' F.face 2 := by
    have : a3I ∈ (⇑g.symm) '' F.face 0 := by rw [hg0]; simp
    exact Set.image_mono h02 this
  obtain ⟨i, hi⟩ := incident_facet_classificationI h2old ha3
  let r1 : E3 ≃ᵃⁱ[ℝ] E3 := ρI
  let r2 : E3 ≃ᵃⁱ[ℝ] E3 := r1.trans ρI
  let r3 : E3 ≃ᵃⁱ[ℝ] E3 := r2.trans ρI
  let r4 : E3 ≃ᵃⁱ[ℝ] E3 := r3.trans ρI
  have hr1 : icosaedroB.isSymmetry r1 := icosaedroB_symmetry rho_preserves_polytopeI
  have hr2 : icosaedroB.isSymmetry r2 := symmetry_trans hr1 hr1
  have hr3 : icosaedroB.isSymmetry r3 := symmetry_trans hr2 hr1
  have hr4 : icosaedroB.isSymmetry r4 := symmetry_trans hr3 hr1
  have hf1 : (⇑r1) '' fanFaceI 0 = fanFaceI 1 := by
    simpa [r1] using rho_image_fanFace (0 : Fin 5)
  have hf2 : (⇑r2) '' fanFaceI 0 = fanFaceI 2 := by
    calc
      (⇑r2) '' fanFaceI 0 = (⇑ρI) '' ((⇑r1) '' fanFaceI 0) := by
        rw [Set.image_image]
        rfl
      _ = fanFaceI 2 := by rw [hf1]; simpa using rho_image_fanFace (1 : Fin 5)
  have hf3 : (⇑r3) '' fanFaceI 0 = fanFaceI 3 := by
    calc
      (⇑r3) '' fanFaceI 0 = (⇑ρI) '' ((⇑r2) '' fanFaceI 0) := by
        rw [Set.image_image]
        rfl
      _ = fanFaceI 3 := by rw [hf2]; simpa using rho_image_fanFace (2 : Fin 5)
  have hf4 : (⇑r4) '' fanFaceI 0 = fanFaceI 4 := by
    calc
      (⇑r4) '' fanFaceI 0 = (⇑ρI) '' ((⇑r3) '' fanFaceI 0) := by
        rw [Set.image_image]
        rfl
      _ = fanFaceI 4 := by rw [hf3]; simpa using rho_image_fanFace (3 : Fin 5)
  have hr10 : r1 a3I = a3I := by exact rho_a3
  have hr20 : r2 a3I = a3I := by
    change ρI (r1 a3I) = a3I
    rw [hr10, rho_a3]
  have hr30 : r3 a3I = a3I := by
    change ρI (r2 a3I) = a3I
    rw [hr20, rho_a3]
  have hr40 : r4 a3I = a3I := by
    change ρI (r3 a3I) = a3I
    rw [hr30, rho_a3]
  have hr1s0 : r1.symm a3I = a3I := (Equiv.symm_apply_eq r1.toEquiv).2 hr10.symm
  have hr2s0 : r2.symm a3I = a3I := (Equiv.symm_apply_eq r2.toEquiv).2 hr20.symm
  have hr3s0 : r3.symm a3I = a3I := (Equiv.symm_apply_eq r3.toEquiv).2 hr30.symm
  have hr4s0 : r4.symm a3I = a3I := (Equiv.symm_apply_eq r4.toEquiv).2 hr40.symm
  fin_cases i
  · exact ⟨finishVertexFacetNormalization F g.symm hgB hg0 hi
      (AffineIsometryEquiv.refl ℝ E3) (symmetry_refl icosaedroB)
      (Set.image_id _) (Set.image_id _)⟩
  · exact ⟨finishVertexFacetNormalization F g.symm hgB hg0 hi r1.symm
      (symmetry_symm hr1) (by simp only [Set.image_singleton, hr1s0])
      (symm_image_eq_of_image_eq r1 hf1)⟩
  · exact ⟨finishVertexFacetNormalization F g.symm hgB hg0 hi r2.symm
      (symmetry_symm hr2) (by simp only [Set.image_singleton, hr2s0])
      (symm_image_eq_of_image_eq r2 hf2)⟩
  · exact ⟨finishVertexFacetNormalization F g.symm hgB hg0 hi r3.symm
      (symmetry_symm hr3) (by simp only [Set.image_singleton, hr3s0])
      (symm_image_eq_of_image_eq r3 hf3)⟩
  · exact ⟨finishVertexFacetNormalization F g.symm hgB hg0 hi r4.symm
      (symmetry_symm hr4) (by simp only [Set.image_singleton, hr4s0])
      (symm_image_eq_of_image_eq r4 hf4)⟩

/-! ## Classificazione locale degli spigoli -/

def dodecaCornerTriple : Fin 3 → E3 := ![a7, b3, c3D]

theorem dodecaCornerTriple_affineIndependent :
    AffineIndependent ℝ dodecaCornerTriple := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro u v hu hv huv
  funext i
  have hcoord (j : Fin 3) := congrArg (fun z : E3 => z j) huv
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hu),
    Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hv)] at hcoord
  simp [dodecaCornerTriple, a7, b3, c3D, Fin.sum_univ_three] at hcoord
  have h0 := hcoord 0
  have h1 := hcoord 1
  rw [Fin.sum_univ_three] at hu hv
  rw [golden_inv_nf] at h1
  change u 0 * 1 + u 1 * 0 + u 2 * Real.goldenRatio =
    v 0 * 1 + v 1 * 0 + v 2 * Real.goldenRatio at h0
  change u 0 * 1 + u 1 * (Real.goldenRatio - 1) + u 2 * 0 =
    v 0 * 1 + v 1 * (Real.goldenRatio - 1) + v 2 * 0 at h1
  have hp : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hq : 0 < 2 / (1 + Real.sqrt 5) := by positivity
  have hpq : Real.goldenRatio * (Real.goldenRatio - 1) = 1 := by
    nlinarith [Real.goldenRatio_sq]
  have hd1 : Real.goldenRatio * (u 0 - v 0) + (u 1 - v 1) = 0 := by
    have hh : (u 0 - v 0) + (Real.goldenRatio - 1) * (u 1 - v 1) = 0 := by
      linarith [h1]
    calc
      Real.goldenRatio * (u 0 - v 0) + (u 1 - v 1) =
          Real.goldenRatio * (u 0 - v 0) +
            (Real.goldenRatio * (Real.goldenRatio - 1)) * (u 1 - v 1) := by
              rw [hpq]
              ring
      _ = Real.goldenRatio *
            ((u 0 - v 0) + (Real.goldenRatio - 1) * (u 1 - v 1)) := by ring
      _ = 0 := by rw [hh]; ring
  have hd2 : (Real.goldenRatio - 1) * (u 0 - v 0) + (u 2 - v 2) = 0 := by
    have hh : (u 0 - v 0) + Real.goldenRatio * (u 2 - v 2) = 0 := by
      linarith [h0]
    calc
      (Real.goldenRatio - 1) * (u 0 - v 0) + (u 2 - v 2) =
          (Real.goldenRatio - 1) * (u 0 - v 0) +
            (Real.goldenRatio * (Real.goldenRatio - 1)) * (u 2 - v 2) := by
              rw [hpq]
              ring
      _ = (Real.goldenRatio - 1) *
            ((u 0 - v 0) + Real.goldenRatio * (u 2 - v 2)) := by ring
      _ = 0 := by rw [hh]; ring
  have e0 : u 0 = v 0 := by
    nlinarith [Real.one_lt_goldenRatio]
  have e1 : u 1 = v 1 := by
    nlinarith [Real.goldenRatio_sq]
  have e2 : u 2 = v 2 := by
    nlinarith [Real.goldenRatio_sq]
  fin_cases i <;> assumption

theorem dodecaedro_corner_three_rank {H : Set E3}
    (h0 : a7 ∈ H) (h1 : b3 ∈ H) (h2 : c3D ∈ H) :
    2 ≤ ConvexPolytope.faceDim H := by
  have hsub : Set.range dodecaCornerTriple ⊆ H := by
    rintro z ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hrank : Module.finrank ℝ (vectorSpan ℝ (Set.range dodecaCornerTriple)) = 2 :=
    dodecaCornerTriple_affineIndependent.finrank_vectorSpan (n := 2) (by simp)
  unfold ConvexPolytope.faceDim
  calc
    2 = Module.finrank ℝ (vectorSpan ℝ (Set.range dodecaCornerTriple)) := hrank.symm
    _ ≤ Module.finrank ℝ (vectorSpan ℝ H) :=
      Submodule.finrank_mono (vectorSpan_mono ℝ hsub)

theorem dodecaedro_base_three_rank {H : Set E3}
    (h0 : a7 ∈ H) (h1 : b3 ∈ H) (h2 : b1 ∈ H) :
    2 ≤ ConvexPolytope.faceDim H := by
  have hsub : Set.range baseTriple ⊆ H := by
    rintro z ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hrank : Module.finrank ℝ (vectorSpan ℝ (Set.range baseTriple)) = 2 :=
    baseTriple_affineIndependent.finrank_vectorSpan (n := 2) (by simp)
  unfold ConvexPolytope.faceDim
  calc
    2 = Module.finrank ℝ (vectorSpan ℝ (Set.range baseTriple)) := hrank.symm
    _ ≤ Module.finrank ℝ (vectorSpan ℝ H) :=
      Submodule.finrank_mono (vectorSpan_mono ℝ hsub)

abbrev dodecaedroBaseEdge : Set E3 := convexHull ℝ ({a7, b3} : Set E3)
abbrev dodecaedroOtherEdge : Set E3 := convexHull ℝ ({a7, c3D} : Set E3)

theorem dodecaedro_base_edge_cases {H : Set E3} (hH : dodecaedroB.IsFace H)
    (hd : ConvexPolytope.faceDim H = 1) (ha7 : a7 ∈ H)
    (hsubBase : H ⊆ fanFace 0) :
    H = dodecaedroBaseEdge ∨ H = dodecaedroOtherEdge := by
  classical
  have hOld := dodecaedroB_face_to_old hH
  obtain ⟨l, hl⟩ := hOld.1 hOld.2
  have hFS := dodeca_exposedFace_eq_convexHull_vertices hOld
  let S : Finset E3 := dodecaedro.vertices.filter (· ∈ H)
  have ha7P : a7 ∈ dodecaedro.toSet :=
    subset_convexHull ℝ (verticiDodeca : Set E3) (by simp [verticiDodeca])
  have ha7max := ha7
  rw [hl] at ha7max
  have hmaxV (u : E3) (hu : u ∈ (verticiDodeca : Set E3)) : l u ≤ l a7 :=
    ha7max.2 u (subset_convexHull ℝ (verticiDodeca : Set E3) hu)
  have ha7S : a7 ∈ (S : Set E3) := by
    exact_mod_cast Finset.mem_filter.mpr ⟨by simp [dodecaedro, verticiDodeca], ha7⟩
  have hS_cases {u : E3} (hu : u ∈ (S : Set E3)) :
      u = a7 ∨ u = b3 ∨ u = b1 ∨ u = a5 ∨ u = c3D := by
    have huf := Finset.mem_filter.mp (by exact_mod_cast hu)
    have huF0 : u ∈ F₀D := by
      exact hsubBase huf.2
    have heq := supportL_eq_on_F₀ u huF0
    obtain ⟨i, hi⟩ := supportL_eq_imp_faceCycle u huf.1 heq
    rw [← hi]
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have hb1not : b1 ∉ (S : Set E3) := by
    intro hb1S
    have hb1H := (Finset.mem_filter.mp (by exact_mod_cast hb1S)).2
    have hb1max := hb1H
    rw [hl] at hb1max
    have hb1eq : l b1 = l a7 := le_antisymm
      (hmaxV b1 (by simp [verticiDodeca])) (hb1max.2 a7 ha7P)
    have hb3le := hmaxV b3 (by simp [verticiDodeca])
    have hc3le := hmaxV c3D (by simp [verticiDodeca])
    rw [functional_b1, functional_a7] at hb1eq
    rw [functional_b3, functional_a7] at hb3le
    rw [functional_c3, functional_a7] at hc3le
    rw [golden_inv] at hb1eq hb3le hc3le
    have hqpos : 0 < Real.goldenRatio - 1 := sub_pos.mpr Real.one_lt_goldenRatio
    have hBle : l e₁ ≤ 0 := by
      nlinarith
    have hAeq : l e₀ =
        -Real.goldenRatio * l e₁ + (Real.goldenRatio - 1) * l e₂ := by
      nlinarith [hb1eq]
    have hsqB := congrArg (fun t : ℝ => t * l e₁) Real.goldenRatio_sq
    have hsqC := congrArg (fun t : ℝ => t * l e₂) Real.goldenRatio_sq
    have hBge : 0 ≤ l e₁ := by
      rw [hAeq] at hc3le
      nlinarith [hsqB, hsqC]
    have hB : l e₁ = 0 := by
      exact le_antisymm hBle hBge
    have hb3eq : l b3 = l a7 := by
      rw [functional_b3, functional_a7, hB, golden_inv]
      nlinarith [hb1eq]
    have hb3H : b3 ∈ H := by
      rw [hl]
      refine ⟨subset_convexHull ℝ (verticiDodeca : Set E3)
        (by simp [verticiDodeca]), ?_⟩
      intro y hy
      exact (ha7max.2 y hy).trans hb3eq.symm.le
    have hrank := dodecaedro_base_three_rank ha7 hb3H hb1H
    omega
  have ha5not : a5 ∉ (S : Set E3) := by
    intro ha5S
    have ha5H := (Finset.mem_filter.mp (by exact_mod_cast ha5S)).2
    have ha5max := ha5H
    rw [hl] at ha5max
    have ha5eq : l a5 = l a7 := le_antisymm
      (hmaxV a5 (by simp [verticiDodeca])) (ha5max.2 a7 ha7P)
    have hB : l e₁ = 0 := by
      have ha5formula : l a5 = l e₀ - l e₁ + l e₂ := by
        rw [functional_apply_coords]
        simp [a5]
        ring
      rw [ha5formula, functional_a7] at ha5eq
      linarith
    have hb3le := hmaxV b3 (by simp [verticiDodeca])
    have hc3le := hmaxV c3D (by simp [verticiDodeca])
    rw [functional_b3, functional_a7, hB, golden_inv] at hb3le
    rw [functional_c3, functional_a7, hB, golden_inv] at hc3le
    have hqpos : 0 < Real.goldenRatio - 1 := sub_pos.mpr Real.one_lt_goldenRatio
    have hAlow : (Real.goldenRatio - 1) * l e₂ ≤ l e₀ := by
      nlinarith
    have hscaled : (Real.goldenRatio - 1) * l e₀ ≤
        (Real.goldenRatio - 1) ^ 2 * l e₂ := by
      have hsqC := congrArg (fun t : ℝ => t * l e₂) Real.goldenRatio_sq
      nlinarith [hsqC]
    have hAhigh : l e₀ ≤ (Real.goldenRatio - 1) * l e₂ := by
      by_contra hn
      have hgt : (Real.goldenRatio - 1) * l e₂ < l e₀ := lt_of_not_ge hn
      have hmul := mul_lt_mul_of_pos_left hgt hqpos
      nlinarith
    have hA : l e₀ = (Real.goldenRatio - 1) * l e₂ :=
      le_antisymm hAhigh hAlow
    have hb3eq : l b3 = l a7 := by
      rw [functional_b3, functional_a7, hB, golden_inv, hA]
      ring
    have hb1eq : l b1 = l a7 := by
      calc
        l b1 = l b3 := by rw [functional_b1, functional_b3, hB]; ring
        _ = l a7 := hb3eq
    have hb3H : b3 ∈ H := by
      rw [hl]
      refine ⟨subset_convexHull ℝ (verticiDodeca : Set E3)
        (by simp [verticiDodeca]), ?_⟩
      intro y hy
      exact (ha7max.2 y hy).trans hb3eq.symm.le
    have hb1H : b1 ∈ H := by
      rw [hl]
      refine ⟨subset_convexHull ℝ (verticiDodeca : Set E3)
        (by simp [verticiDodeca]), ?_⟩
      intro y hy
      exact (ha7max.2 y hy).trans hb1eq.symm.le
    have hrank := dodecaedro_base_three_rank ha7 hb3H hb1H
    omega
  by_cases hb3S : b3 ∈ (S : Set E3)
  · by_cases hc3S : c3D ∈ (S : Set E3)
    · have hb3H := (Finset.mem_filter.mp (by exact_mod_cast hb3S)).2
      have hc3H := (Finset.mem_filter.mp (by exact_mod_cast hc3S)).2
      have hrank := dodecaedro_corner_three_rank ha7 hb3H hc3H
      omega
    · left
      rw [hFS]
      congr 1
      ext u
      constructor
      · intro hu
        rcases hS_cases hu with rfl | rfl | rfl | rfl | rfl
        · simp
        · simp
        · exact absurd hu hb1not
        · exact absurd hu ha5not
        · exact absurd hu hc3S
      · intro hu
        rcases (by simpa using hu : u = a7 ∨ u = b3) with rfl | rfl
        · exact ha7S
        · exact hb3S
  · by_cases hc3S : c3D ∈ (S : Set E3)
    · right
      rw [hFS]
      congr 1
      ext u
      constructor
      · intro hu
        rcases hS_cases hu with rfl | rfl | rfl | rfl | rfl
        · simp
        · exact absurd hu hb3S
        · exact absurd hu hb1not
        · exact absurd hu ha5not
        · simp
      · intro hu
        rcases (by simpa using hu : u = a7 ∨ u = c3D) with rfl | rfl
        · exact ha7S
        · exact hc3S
    · exfalso
      have hSeq : (S : Set E3) = {a7} := by
        ext u
        constructor
        · intro hu
          rcases hS_cases hu with rfl | rfl | rfl | rfl | rfl
          · simp
          · exact absurd hu hb3S
          · exact absurd hu hb1not
          · exact absurd hu ha5not
          · exact absurd hu hc3S
        · intro hu
          simpa using hu ▸ ha7S
      rw [hFS, hSeq, convexHull_singleton] at hd
      unfold ConvexPolytope.faceDim at hd
      rw [vectorSpan_singleton] at hd
      norm_num at hd

theorem icosaedro_base_three_rank {H : Set E3}
    (h0 : a3I ∈ H) (h1 : b3I ∈ H) (h2 : c3I ∈ H) :
    2 ≤ ConvexPolytope.faceDim H := by
  have hsub : Set.range faceCycleI ⊆ H := by
    rintro z ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hrank : Module.finrank ℝ (vectorSpan ℝ (Set.range faceCycleI)) = 2 :=
    faceCycle_affineIndependent.finrank_vectorSpan (n := 2) (by simp)
  unfold ConvexPolytope.faceDim
  calc
    2 = Module.finrank ℝ (vectorSpan ℝ (Set.range faceCycleI)) := hrank.symm
    _ ≤ Module.finrank ℝ (vectorSpan ℝ H) :=
      Submodule.finrank_mono (vectorSpan_mono ℝ hsub)

abbrev icosaedroBaseEdge : Set E3 := convexHull ℝ ({a3I, b3I} : Set E3)
abbrev icosaedroOtherEdge : Set E3 := convexHull ℝ ({a3I, c3I} : Set E3)

theorem icosaedro_base_edge_cases {H : Set E3} (hH : icosaedroB.IsFace H)
    (hd : ConvexPolytope.faceDim H = 1) (ha3 : a3I ∈ H)
    (hsubBase : H ⊆ fanFaceI 0) :
    H = icosaedroBaseEdge ∨ H = icosaedroOtherEdge := by
  classical
  have hOld := icosaedroB_face_to_old hH
  have hFS := icosa_exposedFace_eq_convexHull_vertices hOld
  let S : Finset E3 := icosaedro.vertices.filter (· ∈ H)
  have ha3S : a3I ∈ (S : Set E3) := by
    exact_mod_cast Finset.mem_filter.mpr ⟨by simp [icosaedro, verticiIcosa], ha3⟩
  have hS_cases {u : E3} (hu : u ∈ (S : Set E3)) :
      u = a3I ∨ u = b3I ∨ u = c3I := by
    have huf := Finset.mem_filter.mp (by exact_mod_cast hu)
    have huF0 : u ∈ F₀I := by
      rw [← fanFace_zero]
      exact hsubBase huf.2
    have heq := supportL_eq_on_F₀I u huF0
    obtain ⟨i, hi⟩ := supportL_eq_imp_faceCycleI u huf.1 heq
    rw [← hi]
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  by_cases hbS : b3I ∈ (S : Set E3)
  · by_cases hcS : c3I ∈ (S : Set E3)
    · have hbH := (Finset.mem_filter.mp (by exact_mod_cast hbS)).2
      have hcH := (Finset.mem_filter.mp (by exact_mod_cast hcS)).2
      have hrank := icosaedro_base_three_rank ha3 hbH hcH
      omega
    · left
      rw [hFS]
      congr 1
      ext u
      constructor
      · intro hu
        rcases hS_cases hu with rfl | rfl | rfl
        · simp
        · simp
        · exact absurd hu hcS
      · intro hu
        rcases (by simpa using hu : u = a3I ∨ u = b3I) with rfl | rfl
        · exact ha3S
        · exact hbS
  · by_cases hcS : c3I ∈ (S : Set E3)
    · right
      rw [hFS]
      congr 1
      ext u
      constructor
      · intro hu
        rcases hS_cases hu with rfl | rfl | rfl
        · simp
        · exact absurd hu hbS
        · simp
      · intro hu
        rcases (by simpa using hu : u = a3I ∨ u = c3I) with rfl | rfl
        · exact ha3S
        · exact hcS
    · exfalso
      have hSeq : (S : Set E3) = {a3I} := by
        ext u
        constructor
        · intro hu
          rcases hS_cases hu with rfl | rfl | rfl
          · simp
          · exact absurd hu hbS
          · exact absurd hu hcS
        · intro hu
          simpa using hu ▸ ha3S
      rw [hFS, hSeq, convexHull_singleton] at hd
      unfold ConvexPolytope.faceDim at hd
      rw [vectorSpan_singleton] at hd
      norm_num at hd

/-! ## Le riflessioni dei due spigoli canonici -/

theorem image_convexHull_isom (φ : ConvexPolytope.Isom 3) (S : Set E3) :
    (⇑φ) '' convexHull ℝ S = convexHull ℝ ((⇑φ) '' S) := by
  simpa only [AffineEquiv.coe_toAffineMap, AffineIsometryEquiv.coe_toAffineEquiv] using
    φ.toAffineEquiv.toAffineMap.image_convexHull S

def dodecaEdgeFlip : E3 ≃ᵃⁱ[ℝ] E3 := τy.trans (ρ.trans ρ)

theorem dodecaEdgeFlip_symmetry : dodecaedroB.isSymmetry dodecaEdgeFlip := by
  exact symmetry_trans (dodecaedroB_symmetry tauY_preserves_polytope)
    (symmetry_trans (dodecaedroB_symmetry rho_preserves_polytope)
      (dodecaedroB_symmetry rho_preserves_polytope))

theorem dodeca_tauY_face_actions :
    τy x0 = x3 ∧ τy x1 = x2 ∧ τy x2 = x1 ∧ τy x3 = x0 ∧ τy x4 = x4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals apply E3_ext
  all_goals simp [x0, x1, x2, x3, x4, a7, b3, b1, a5, c3D]

theorem dodecaEdgeFlip_actions :
    dodecaEdgeFlip x0 = x0 ∧ dodecaEdgeFlip x1 = x4 ∧
      dodecaEdgeFlip x2 = x3 ∧ dodecaEdgeFlip x3 = x2 ∧
        dodecaEdgeFlip x4 = x1 := by
  rcases dodeca_tauY_face_actions with ⟨h0, h1, h2, h3, h4⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change ρ (ρ (τy x0)) = x0
    rw [h0, rho_x3, rho_x4]
  · change ρ (ρ (τy x1)) = x4
    rw [h1, rho_x2, rho_x3]
  · change ρ (ρ (τy x2)) = x3
    rw [h2, rho_x1, rho_x2]
  · change ρ (ρ (τy x3)) = x2
    rw [h3, rho_x0, rho_x1]
  · change ρ (ρ (τy x4)) = x1
    rw [h4, rho_x4, rho_x0]

theorem dodecaEdgeFlip_zero : dodecaEdgeFlip a7 = a7 := by
  simpa [x0] using dodecaEdgeFlip_actions.1

theorem dodecaEdgeFlip_b3 : dodecaEdgeFlip b3 = c3D := by
  simpa [x1, x4] using dodecaEdgeFlip_actions.2.1

theorem dodecaEdgeFlip_c3 : dodecaEdgeFlip c3D = b3 := by
  simpa [x1, x4] using dodecaEdgeFlip_actions.2.2.2.2

theorem dodecaEdgeFlip_base :
    (⇑dodecaEdgeFlip) '' fanFace 0 = fanFace 0 := by
  change (⇑dodecaEdgeFlip) '' F₀D = F₀D
  rw [F₀D, image_convexHull_isom]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    fin_cases i
    · exact ⟨0, dodecaEdgeFlip_actions.1.symm⟩
    · exact ⟨4, dodecaEdgeFlip_actions.2.1.symm⟩
    · exact ⟨3, dodecaEdgeFlip_actions.2.2.1.symm⟩
    · exact ⟨2, dodecaEdgeFlip_actions.2.2.2.1.symm⟩
    · exact ⟨1, dodecaEdgeFlip_actions.2.2.2.2.symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨faceCycle 0, ⟨0, rfl⟩, dodecaEdgeFlip_actions.1⟩
    · exact ⟨faceCycle 4, ⟨4, rfl⟩, dodecaEdgeFlip_actions.2.2.2.2⟩
    · exact ⟨faceCycle 3, ⟨3, rfl⟩, dodecaEdgeFlip_actions.2.2.2.1⟩
    · exact ⟨faceCycle 2, ⟨2, rfl⟩, dodecaEdgeFlip_actions.2.2.1⟩
    · exact ⟨faceCycle 1, ⟨1, rfl⟩, dodecaEdgeFlip_actions.2.1⟩

theorem dodecaEdgeFlip_edge :
    (⇑dodecaEdgeFlip) '' dodecaedroOtherEdge = dodecaedroBaseEdge := by
  rw [image_convexHull_isom]
  congr 1
  ext z
  simp [dodecaEdgeFlip_zero, dodecaEdgeFlip_c3, eq_comm]

def icosaEdgeFlip : E3 ≃ᵃⁱ[ℝ] E3 := τyI.trans (ρI.trans ρI)

theorem icosaEdgeFlip_symmetry : icosaedroB.isSymmetry icosaEdgeFlip := by
  exact symmetry_trans (icosaedroB_symmetry tauY_preserves_polytopeI)
    (symmetry_trans (icosaedroB_symmetry rho_preserves_polytopeI)
      (icosaedroB_symmetry rho_preserves_polytopeI))

theorem icosa_tauY_actions :
    τyI a3I = a3I ∧ τyI b3I = b2I ∧ τyI c3I = c1I := by
  refine ⟨?_, ?_, ?_⟩
  all_goals apply E3_extI
  all_goals simp [a3I, b3I, b2I, c3I, c1I]

theorem icosaEdgeFlip_actions :
    icosaEdgeFlip a3I = a3I ∧ icosaEdgeFlip b3I = c3I ∧
      icosaEdgeFlip c3I = b3I := by
  have hb2 : ρI b2I = b3I := by
    simpa [neighbor] using rho_neighbor (4 : Fin 5)
  have hb3 : ρI b3I = c3I := by
    simpa [neighbor] using rho_neighbor (0 : Fin 5)
  have hc1 : ρI c1I = b2I := by
    simpa [neighbor] using rho_neighbor (3 : Fin 5)
  rcases icosa_tauY_actions with ⟨h0, h1, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · change ρI (ρI (τyI a3I)) = a3I
    rw [h0, rho_a3, rho_a3]
  · change ρI (ρI (τyI b3I)) = c3I
    rw [h1, hb2, hb3]
  · change ρI (ρI (τyI c3I)) = b3I
    rw [h2, hc1, hb2]

theorem icosaEdgeFlip_zero : icosaEdgeFlip a3I = a3I :=
  icosaEdgeFlip_actions.1

theorem icosaEdgeFlip_base :
    (⇑icosaEdgeFlip) '' fanFaceI 0 = fanFaceI 0 := by
  rw [fanFace_zero, F₀I, image_convexHull_isom]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    fin_cases i
    · exact ⟨0, icosaEdgeFlip_actions.1.symm⟩
    · exact ⟨2, icosaEdgeFlip_actions.2.1.symm⟩
    · exact ⟨1, icosaEdgeFlip_actions.2.2.symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨faceCycleI 0, ⟨0, rfl⟩, icosaEdgeFlip_actions.1⟩
    · exact ⟨faceCycleI 2, ⟨2, rfl⟩, icosaEdgeFlip_actions.2.2⟩
    · exact ⟨faceCycleI 1, ⟨1, rfl⟩, icosaEdgeFlip_actions.2.1⟩

theorem icosaEdgeFlip_edge :
    (⇑icosaEdgeFlip) '' icosaedroOtherEdge = icosaedroBaseEdge := by
  rw [image_convexHull_isom]
  congr 1
  ext z
  simp [icosaEdgeFlip_actions.1, icosaEdgeFlip_actions.2.2, eq_comm]

/-! ## Normalizzazione completa delle bandiere -/

structure FlagNormalization {P : ConvexPolytope 3} (F : P.Flag)
    (C0 C1 C2 : Set E3) where
  φ : ConvexPolytope.Isom 3
  symmetry : P.isSymmetry φ
  image_zero : (⇑φ) '' F.face 0 = C0
  image_one : (⇑φ) '' F.face 1 = C1
  image_two : (⇑φ) '' F.face 2 = C2

def finishFlagNormalization {P : ConvexPolytope 3} (F : P.Flag)
    {C0 C1 C2 : Set E3}
    (p : VertexFacetNormalization F C0 C2)
    (r : ConvexPolytope.Isom 3) (hr : P.isSymmetry r)
    (hr0 : (⇑r) '' C0 = C0) (hr2 : (⇑r) '' C2 = C2)
    (hr1 : (⇑r) '' ((⇑p.φ) '' F.face 1) = C1) :
    FlagNormalization F C0 C1 C2 where
  φ := p.φ.trans r
  symmetry := symmetry_trans p.symmetry hr
  image_zero := by
    calc
      (⇑(p.φ.trans r)) '' F.face 0 = (⇑r) '' ((⇑p.φ) '' F.face 0) := by
        rw [Set.image_image]
        rfl
      _ = C0 := by rw [p.image_zero, hr0]
  image_one := by
    calc
      (⇑(p.φ.trans r)) '' F.face 1 = (⇑r) '' ((⇑p.φ) '' F.face 1) := by
        rw [Set.image_image]
        rfl
      _ = C1 := hr1
  image_two := by
    calc
      (⇑(p.φ.trans r)) '' F.face 2 = (⇑r) '' ((⇑p.φ) '' F.face 2) := by
        rw [Set.image_image]
        rfl
      _ = C2 := by rw [p.image_two, hr2]

theorem dodecaedro_flag_normalization (F : dodecaedroB.Flag) :
    Nonempty (FlagNormalization F ({a7} : Set E3)
      dodecaedroBaseEdge (fanFace 0)) := by
  let p := (dodecaedro_vertex_facet_normalization F).some
  have h1face := isFace_image_isom p.φ p.symmetry (F.isFace 1)
  have h1dim : ConvexPolytope.faceDim ((⇑p.φ) '' F.face 1) = 1 := by
    rw [faceDim_image_isom, F.dim_eq]
    norm_num
  have h01 : F.face 0 ⊆ F.face 1 := (F.strict_mono 0 1 (by decide)).1
  have ha7 : a7 ∈ (⇑p.φ) '' F.face 1 := by
    have ha70 : a7 ∈ (⇑p.φ) '' F.face 0 := by
      rw [p.image_zero]
      exact Set.mem_singleton a7
    exact Set.image_mono h01 ha70
  have h12 : F.face 1 ⊆ F.face 2 := (F.strict_mono 1 2 (by decide)).1
  have hsub : (⇑p.φ) '' F.face 1 ⊆ fanFace 0 := by
    intro x hx
    have := Set.image_mono h12 hx
    rw [p.image_two] at this
    exact this
  rcases dodecaedro_base_edge_cases h1face h1dim ha7 hsub with h | h
  · exact ⟨finishFlagNormalization F p (AffineIsometryEquiv.refl ℝ E3)
      (symmetry_refl dodecaedroB) (Set.image_id _) (Set.image_id _) (by
        rw [h]
        exact Set.image_id _)⟩
  · exact ⟨finishFlagNormalization F p dodecaEdgeFlip
      dodecaEdgeFlip_symmetry (by simp [dodecaEdgeFlip_zero])
      dodecaEdgeFlip_base (by rw [h]; exact dodecaEdgeFlip_edge)⟩

theorem icosaedro_flag_normalization (F : icosaedroB.Flag) :
    Nonempty (FlagNormalization F ({a3I} : Set E3)
      icosaedroBaseEdge (fanFaceI 0)) := by
  let p := (icosaedro_vertex_facet_normalization F).some
  have h1face := isFace_image_isom p.φ p.symmetry (F.isFace 1)
  have h1dim : ConvexPolytope.faceDim ((⇑p.φ) '' F.face 1) = 1 := by
    rw [faceDim_image_isom, F.dim_eq]
    norm_num
  have h01 : F.face 0 ⊆ F.face 1 := (F.strict_mono 0 1 (by decide)).1
  have ha3 : a3I ∈ (⇑p.φ) '' F.face 1 := by
    have ha30 : a3I ∈ (⇑p.φ) '' F.face 0 := by
      rw [p.image_zero]
      exact Set.mem_singleton a3I
    exact Set.image_mono h01 ha30
  have h12 : F.face 1 ⊆ F.face 2 := (F.strict_mono 1 2 (by decide)).1
  have hsub : (⇑p.φ) '' F.face 1 ⊆ fanFaceI 0 := by
    intro x hx
    have := Set.image_mono h12 hx
    rw [p.image_two] at this
    exact this
  rcases icosaedro_base_edge_cases h1face h1dim ha3 hsub with h | h
  · exact ⟨finishFlagNormalization F p (AffineIsometryEquiv.refl ℝ E3)
      (symmetry_refl icosaedroB) (Set.image_id _) (Set.image_id _) (by
        rw [h]
        exact Set.image_id _)⟩
  · exact ⟨finishFlagNormalization F p icosaEdgeFlip
      icosaEdgeFlip_symmetry (by simp [icosaEdgeFlip_zero])
      icosaEdgeFlip_base (by rw [h]; exact icosaEdgeFlip_edge)⟩

theorem image_between_normalizations {φ ψ : ConvexPolytope.Isom 3}
    {A B C : Set E3} (hφ : (⇑φ) '' A = C) (hψ : (⇑ψ) '' B = C) :
    (⇑(φ.trans ψ.symm)) '' A = B := by
  calc
    (⇑(φ.trans ψ.symm)) '' A = (⇑ψ.symm) '' ((⇑φ) '' A) := by
      rw [Set.image_image]
      rfl
    _ = (⇑ψ.symm) '' C := congrArg (fun S : Set E3 => (⇑ψ.symm) '' S) hφ
    _ = B := symm_image_eq_of_image_eq ψ hψ

/-! ## CONSEGNA -/

theorem dodecaedroB_isRegular : dodecaedroB.IsRegular := by
  refine ⟨dodecaedroB_fullDim, ?_⟩
  intro F G
  let f := (dodecaedro_flag_normalization F).some
  let g := (dodecaedro_flag_normalization G).some
  refine ⟨f.φ.trans g.φ.symm,
    symmetry_trans f.symmetry (symmetry_symm g.symmetry), ?_⟩
  intro k
  fin_cases k
  · exact image_between_normalizations f.image_zero g.image_zero
  · exact image_between_normalizations f.image_one g.image_one
  · exact image_between_normalizations f.image_two g.image_two

theorem icosaedroB_isRegular : icosaedroB.IsRegular := by
  refine ⟨icosaedroB_fullDim, ?_⟩
  intro F G
  let f := (icosaedro_flag_normalization F).some
  let g := (icosaedro_flag_normalization G).some
  refine ⟨f.φ.trans g.φ.symm,
    symmetry_trans f.symmetry (symmetry_symm g.symmetry), ?_⟩
  intro k
  fin_cases k
  · exact image_between_normalizations f.image_zero g.image_zero
  · exact image_between_normalizations f.image_one g.image_one
  · exact image_between_normalizations f.image_two g.image_two


end F12


/-! ## IL TEOREMA FINALE DELLA FASE 2 -/

theorem tetraedroBM_isRegular : tetraedroBM.IsRegular := F10.tetraedroB_isRegular
theorem cuboBM_isRegular : cuboBM.IsRegular := F11.cuboB_isRegular
theorem ottaedroBM_isRegular : ottaedroBM.IsRegular := F11.ottaedroB_isRegular
theorem dodecaedroBM_isRegular : dodecaedroBM.IsRegular := F12.dodecaedroB_isRegular
theorem icosaedroBM_isRegular : icosaedroBM.IsRegular := F12.icosaedroB_isRegular

/-- `5 ≤ platonicCount 3`, sul contratto del benchmark lean-eval. -/
theorem cinque_le_platonicCount3 : 5 ≤ platonicCount 3 :=
  cinque_le_platonicCount3_di tetraedroBM_isRegular cuboBM_isRegular
    ottaedroBM_isRegular dodecaedroBM_isRegular icosaedroBM_isRegular

end LeanEval.Geometry.PlatonicClassification
