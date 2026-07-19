import Mathlib
import UnicoProofs.Platonici.Benchmark

/-!
L'ortoplesse in dimensione arbitraria: i vertici sono `±eᵢ`.
La parte costruttiva fino a `verticiOrto_eq_extremePoints` riprende
`BOZZA_Ortoplesse.lean` (fascicolo 51).
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Il vertice `±eᵢ` dell'ortoplesse. -/
noncomputable def vertOrto {d : ℕ} (p : Fin d × Bool) : E d :=
  EuclideanSpace.single p.1 (if p.2 then (1 : ℝ) else (-1 : ℝ))

theorem vertOrto_apply {d : ℕ} (p : Fin d × Bool) (k : Fin d) :
    vertOrto p k = if k = p.1 then (if p.2 then (1 : ℝ) else (-1 : ℝ))
      else 0 := by
  unfold vertOrto
  rw [EuclideanSpace.single_apply]

@[simp] theorem vertOrto_self {d : ℕ} (p : Fin d × Bool) :
    vertOrto p p.1 = if p.2 then (1 : ℝ) else (-1 : ℝ) := by
  simp [vertOrto_apply]

theorem vertOrto_injective {d : ℕ} :
    Function.Injective (vertOrto (d := d)) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ hpq
  have hval := congrArg (fun x : E d => x i) hpq
  simp only [vertOrto_apply] at hval
  have hidx : i = j := by
    by_contra hne
    rcases s <;> simp [hne] at hval
  subst j
  have hbool : s = t := by
    cases s <;> cases t
    · rfl
    · norm_num at hval
    · norm_num at hval
    · rfl
  subst t
  rfl

noncomputable def verticiOrto (d : ℕ) : Finset (E d) :=
  (Finset.univ : Finset (Fin d × Bool)).image vertOrto

theorem mem_verticiOrto {d : ℕ} {x : E d} :
    x ∈ verticiOrto d ↔ ∃ p : Fin d × Bool, vertOrto p = x := by
  simp [verticiOrto]

theorem card_verticiOrto (d : ℕ) : (verticiOrto d).card = 2 * d := by
  rw [verticiOrto, Finset.card_image_of_injective _ vertOrto_injective]
  simp [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  omega

theorem verticiOrto_nonempty {d : ℕ} (hd : 0 < d) :
    (verticiOrto d).Nonempty := by
  refine ⟨vertOrto (⟨0, hd⟩, true), ?_⟩
  exact mem_verticiOrto.mpr ⟨(⟨0, hd⟩, true), rfl⟩

theorem norm_vertOrto {d : ℕ} (p : Fin d × Bool) : ‖vertOrto p‖ = 1 := by
  rw [vertOrto]
  rw [EuclideanSpace.norm_single]
  split <;> norm_num

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

theorem verticiOrto_eq_extremePoints (d : ℕ) :
    ((verticiOrto d : Finset (E d)) : Set (E d)) =
      Set.extremePoints ℝ
        (convexHull ℝ ((verticiOrto d : Finset (E d)) : Set (E d))) := by
  by_cases hd : d = 0
  · subst d
    simp [verticiOrto]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    let i : Fin d := ⟨0, hdpos⟩
    have hne : (0 : E d) ≠ vertOrto (i, true) := by
      intro h
      have hi := congrArg (fun x : E d => x i) h
      simp [vertOrto_apply] at hi
    haveI : Nontrivial (E d) := ⟨⟨0, vertOrto (i, true), hne⟩⟩
    symm
    apply cosferico_extremePoints 0 1
    intro v hv
    rw [mem_sphere_zero_iff_norm]
    have hv' : v ∈ verticiOrto d := by exact_mod_cast hv
    rw [mem_verticiOrto] at hv'
    obtain ⟨p, rfl⟩ := hv'
    exact norm_vertOrto p

/-- L'ortoplesse, sul dominio corretto `d ≥ 1`. -/
noncomputable def ortoplesse (d : ℕ) (hd : 1 ≤ d) : ConvexPolytope d :=
  ⟨verticiOrto d, verticiOrto_nonempty hd, verticiOrto_eq_extremePoints d⟩

theorem card_ortoplesse (d : ℕ) (hd : 1 ≤ d) :
    (ortoplesse d hd).vertices.card = 2 * d := by
  exact card_verticiOrto d

/-- L'ortoplesse genera affineamente tutto `E d`. -/
theorem ortoplesse_isFullDim (d : ℕ) (hd : 1 ≤ d) :
    (ortoplesse d hd).IsFullDim := by
  let W : Submodule ℝ (E d) := vectorSpan ℝ (ortoplesse d hd).toSet
  have hbasis : ∀ i : Fin d, (EuclideanSpace.basisFun (Fin d) ℝ) i ∈ W := by
    intro i
    have hpV : vertOrto (i, true) ∈ verticiOrto d :=
      mem_verticiOrto.mpr ⟨(i, true), rfl⟩
    have hnV : vertOrto (i, false) ∈ verticiOrto d :=
      mem_verticiOrto.mpr ⟨(i, false), rfl⟩
    have hp : vertOrto (i, true) ∈ (ortoplesse d hd).toSet := by
      exact subset_convexHull ℝ _ (by exact_mod_cast hpV)
    have hn : vertOrto (i, false) ∈ (ortoplesse d hd).toSet := by
      exact subset_convexHull ℝ _ (by exact_mod_cast hnV)
    have hdiff : vertOrto (i, true) - vertOrto (i, false) ∈ W :=
      vsub_mem_vectorSpan ℝ hp hn
    change EuclideanSpace.single i 1 - EuclideanSpace.single i (-1) ∈ W at hdiff
    rw [EuclideanSpace.basisFun_apply]
    have htwice : (2 : ℝ) • EuclideanSpace.single i 1 ∈ W := by
      simpa only [PiLp.single_neg, sub_neg_eq_add, two_smul] using hdiff
    exact (W.smul_mem_iff (by norm_num : (2 : ℝ) ≠ 0)).mp htwice
  have hW : W = ⊤ := by
    apply (Submodule.eq_top_iff').2
    intro x
    rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x]
    exact Submodule.sum_mem W fun i _ => W.smul_mem _ (hbasis i)
  rw [ConvexPolytope.IsFullDim, ConvexPolytope.dim]
  change Module.finrank ℝ W = d
  rw [hW, finrank_top, finrank_euclideanSpace]
  simp

/-- L'isometria di `ℝ` data da un segno in `{ -1, 1 }`. -/
noncomputable def isometriaSegno (s : ({-1, 1} : Set ℝ)) : ℝ ≃ₗᵢ[ℝ] ℝ :=
  if (s : ℝ) = 1 then LinearIsometryEquiv.refl ℝ ℝ
  else LinearIsometryEquiv.neg ℝ

@[simp] theorem isometriaSegno_apply (s : ({-1, 1} : Set ℝ)) (x : ℝ) :
    isometriaSegno s x = (s : ℝ) * x := by
  unfold isometriaSegno
  split_ifs with h
  · rw [h]
    simp
  · have hs : (s : ℝ) = -1 := by
      have hm := s.property
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with hm | hm
      · exact hm
      · exact (h hm).elim
    rw [hs]
    simp

/-- La parte lineare della permutazione firmata: prima cambia il segno
della coordinata `i`, poi la porta nella coordinata `σ i`. -/
noncomputable def segnoLinear (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) : E d ≃ₗᵢ[ℝ] E d :=
  (LinearIsometryEquiv.piLpCongrRight 2 (fun i => isometriaSegno (ε i))).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ)

/-- La permutazione firmata delle coordinate, come isometria affine. -/
noncomputable def segnoPerm (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) : Isom d :=
  (segnoLinear d σ ε).toAffineIsometryEquiv

@[simp] theorem segnoLinear_single (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) (i : Fin d) (a : ℝ) :
    segnoLinear d σ ε (EuclideanSpace.single i a) =
      EuclideanSpace.single (σ i) ((ε i : ℝ) * a) := by
  simp [segnoLinear]

@[simp] theorem segnoPerm_apply (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) (x : E d) :
    segnoPerm d σ ε x = segnoLinear d σ ε x := rfl

theorem segnoPerm_mem_verticiOrto (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) {v : E d}
    (hv : v ∈ verticiOrto d) : segnoPerm d σ ε v ∈ verticiOrto d := by
  rw [mem_verticiOrto] at hv
  obtain ⟨⟨i, b⟩, rfl⟩ := hv
  have hs := (ε i).property
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with hs | hs <;> cases b
  · apply mem_verticiOrto.mpr
    refine ⟨(σ i, true), ?_⟩
    simp [vertOrto, hs]
  · apply mem_verticiOrto.mpr
    refine ⟨(σ i, false), ?_⟩
    simp [vertOrto, hs]
  · apply mem_verticiOrto.mpr
    refine ⟨(σ i, false), ?_⟩
    simp [vertOrto, hs]
  · apply mem_verticiOrto.mpr
    refine ⟨(σ i, true), ?_⟩
    simp [vertOrto, hs]

theorem segnoPerm_image_verticiOrto (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) :
    (segnoPerm d σ ε : E d → E d) '' (verticiOrto d : Set (E d)) =
      (verticiOrto d : Set (E d)) := by
  have hfin : Finset.image (segnoPerm d σ ε : E d → E d) (verticiOrto d) =
      verticiOrto d := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact segnoPerm_mem_verticiOrto d σ ε hu
    · rw [Finset.card_image_of_injective _ (segnoPerm d σ ε).injective]
  rw [← Finset.coe_image, hfin]

theorem segnoPerm_isSymmetry (d : ℕ) (hd : 1 ≤ d)
    (σ : Equiv.Perm (Fin d)) (ε : Fin d → ({-1, 1} : Set ℝ)) :
    (ortoplesse d hd).isSymmetry (segnoPerm d σ ε) := by
  rw [ConvexPolytope.isSymmetry, ConvexPolytope.toSet]
  calc
    (segnoPerm d σ ε : E d → E d) ''
        convexHull ℝ ((ortoplesse d hd).vertices : Set (E d)) =
      convexHull ℝ ((segnoPerm d σ ε : E d → E d) ''
        ((ortoplesse d hd).vertices : Set (E d))) := by
          exact (segnoPerm d σ ε).toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ ((ortoplesse d hd).vertices : Set (E d)) := by
      rw [show ((ortoplesse d hd).vertices : Set (E d)) =
          (verticiOrto d : Set (E d)) by rfl,
        segnoPerm_image_verticiOrto]

end LeanEval.Geometry.PlatonicClassification
