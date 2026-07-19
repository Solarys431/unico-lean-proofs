import UnicoProofs.Platonici.OrtoplesseFacce

/-!
L'ipercubo regolare in dimensione arbitraria.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Un vertice dell'ipercubo, codificato dai suoi segni. -/
noncomputable def vertIper {d : ℕ} (s : Fin d → Bool) : E d :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => if s i then 1 else -1)

@[simp] theorem vertIper_apply {d : ℕ} (s : Fin d → Bool) (i : Fin d) :
    vertIper s i = if s i then (1 : ℝ) else -1 := by
  simp [vertIper]

theorem vertIper_injective {d : ℕ} :
    Function.Injective (vertIper (d := d)) := by
  intro s t h
  funext i
  have hi := congrArg (fun x : E d => x i) h
  simp only [vertIper_apply] at hi
  cases hsi : s i <;> cases hti : t i <;> simp_all <;> norm_num at hi

/-- I `2^d` vertici dell'ipercubo. -/
noncomputable def verticiIper (d : ℕ) : Finset (E d) :=
  (Finset.univ : Finset (Fin d → Bool)).image vertIper

theorem mem_verticiIper {d : ℕ} {x : E d} :
    x ∈ verticiIper d ↔ ∃ s : Fin d → Bool, vertIper s = x := by
  simp [verticiIper]

theorem card_verticiIper (d : ℕ) : (verticiIper d).card = 2 ^ d := by
  rw [verticiIper, Finset.card_image_of_injective _ vertIper_injective]
  simp

theorem norm_sq_vertIper {d : ℕ} (s : Fin d → Bool) :
    ‖vertIper s‖ ^ 2 = d := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [vertIper_apply]
  have hone : ∀ i : Fin d,
      ‖(if s i = true then (1 : ℝ) else -1)‖ ^ 2 = 1 := by
    intro i
    cases s i <;> norm_num
  simp_rw [hone]
  simp

theorem norm_vertIper {d : ℕ} (s : Fin d → Bool) :
    ‖vertIper s‖ = Real.sqrt d := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), norm_sq_vertIper]
  simp

theorem verticiIper_eq_extremePoints (d : ℕ) :
    ((verticiIper d : Finset (E d)) : Set (E d)) =
      Set.extremePoints ℝ
        (convexHull ℝ ((verticiIper d : Finset (E d)) : Set (E d))) := by
  by_cases hd : d = 0
  · subst d
    have hsingle : ((verticiIper 0 : Finset (E 0)) : Set (E 0)) = {0} := by
      ext x
      constructor
      · intro _
        exact Subsingleton.elim x 0
      · rintro rfl
        exact_mod_cast (mem_verticiIper.mpr ⟨fun i => i.elim0, Subsingleton.elim _ _⟩)
    rw [hsingle]
    simp
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    let i : Fin d := ⟨0, hdpos⟩
    have hne : (0 : E d) ≠ vertIper (fun _ => true) := by
      intro h
      have hi := congrArg (fun x : E d => x i) h
      simp at hi
    haveI : Nontrivial (E d) := ⟨⟨0, vertIper (fun _ => true), hne⟩⟩
    symm
    apply cosferico_extremePoints 0 (Real.sqrt d)
    intro v hv
    rw [mem_sphere_zero_iff_norm]
    have hv' : v ∈ verticiIper d := by exact_mod_cast hv
    rw [mem_verticiIper] at hv'
    obtain ⟨s, rfl⟩ := hv'
    exact norm_vertIper s

theorem verticiIper_nonempty (d : ℕ) : (verticiIper d).Nonempty := by
  refine ⟨vertIper (fun _ => true), mem_verticiIper.mpr ?_⟩
  exact ⟨fun _ => true, rfl⟩

/-- L'ipercubo, sul dominio non degenere `d ≥ 1`. -/
noncomputable def ipercubo (d : ℕ) (_hd : 1 ≤ d) : ConvexPolytope d :=
  ⟨verticiIper d, verticiIper_nonempty d, verticiIper_eq_extremePoints d⟩

theorem card_ipercubo (d : ℕ) (hd : 1 ≤ d) :
    (ipercubo d hd).vertices.card = 2 ^ d :=
  card_verticiIper d

/-- Cambia il segno della sola coordinata `i`. -/
def boolFlip {d : ℕ} (s : Fin d → Bool) (i : Fin d) : Fin d → Bool :=
  Function.update s i (!s i)

@[simp] theorem boolFlip_same {d : ℕ} (s : Fin d → Bool) (i : Fin d) :
    boolFlip s i i = !s i := by
  simp [boolFlip]

@[simp] theorem boolFlip_ne {d : ℕ} (s : Fin d → Bool) {i j : Fin d} (h : j ≠ i) :
    boolFlip s i j = s j := by
  simp [boolFlip, h]

theorem vertIper_sub_flip {d : ℕ} (s : Fin d → Bool) (i : Fin d) :
    vertIper s - vertIper (boolFlip s i) =
      (if s i then (2 : ℝ) else -2) •
        (EuclideanSpace.basisFun (Fin d) ℝ) i := by
  ext j
  by_cases hji : j = i
  · subst j
    cases hsi : s i <;>
      simp [hsi, EuclideanSpace.basisFun_apply] <;> norm_num
  · cases s i <;> simp [hji, EuclideanSpace.basisFun_apply]

theorem ipercubo_isFullDim (d : ℕ) (hd : 1 ≤ d) :
    (ipercubo d hd).IsFullDim := by
  let W : Submodule ℝ (E d) := vectorSpan ℝ (ipercubo d hd).toSet
  let s : Fin d → Bool := fun _ => true
  have hbasis : ∀ i : Fin d, (EuclideanSpace.basisFun (Fin d) ℝ) i ∈ W := by
    intro i
    have hsV : vertIper s ∈ verticiIper d := mem_verticiIper.mpr ⟨s, rfl⟩
    have hfV : vertIper (boolFlip s i) ∈ verticiIper d :=
      mem_verticiIper.mpr ⟨boolFlip s i, rfl⟩
    have hs : vertIper s ∈ (ipercubo d hd).toSet :=
      subset_convexHull ℝ _ (by exact_mod_cast hsV)
    have hf : vertIper (boolFlip s i) ∈ (ipercubo d hd).toSet :=
      subset_convexHull ℝ _ (by exact_mod_cast hfV)
    have hdiff : vertIper s - vertIper (boolFlip s i) ∈ W :=
      vsub_mem_vectorSpan ℝ hs hf
    rw [vertIper_sub_flip] at hdiff
    simp only [s, if_true] at hdiff
    exact (W.smul_mem_iff (by norm_num : (2 : ℝ) ≠ 0)).mp hdiff
  have hW : W = ⊤ := by
    apply (Submodule.eq_top_iff').2
    intro x
    rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x]
    exact Submodule.sum_mem W fun i _ => W.smul_mem _ (hbasis i)
  rw [ConvexPolytope.IsFullDim, ConvexPolytope.dim]
  change Module.finrank ℝ W = d
  rw [hW, finrank_top, finrank_euclideanSpace]
  simp

theorem mem_verticiIper_iff {d : ℕ} {x : E d} :
    x ∈ verticiIper d ↔ ∀ i : Fin d, x i = 1 ∨ x i = -1 := by
  constructor
  · intro hx i
    obtain ⟨s, rfl⟩ := mem_verticiIper.mp hx
    cases hsi : s i
    · right
      rw [vertIper_apply, hsi]
      simp
    · left
      rw [vertIper_apply, hsi]
      simp
  · intro hx
    let s : Fin d → Bool := fun i => decide (x i = 1)
    apply mem_verticiIper.mpr
    refine ⟨s, ?_⟩
    ext i
    rcases hx i with hi | hi
    · have hs : s i = true := by simp [s, hi]
      rw [vertIper_apply, hs, hi]
      simp
    · have hne : x i ≠ 1 := by linarith
      have hs : s i = false := by simp [s, hne]
      rw [vertIper_apply, hs, hi]
      simp

@[simp] theorem segnoLinear_apply_coord (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) (x : E d) (i : Fin d) :
    segnoLinear d σ ε x (σ i) = (ε i : ℝ) * x i := by
  simp [segnoLinear]

theorem segnoPerm_mem_verticiIper (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) {v : E d}
    (hv : v ∈ verticiIper d) : segnoPerm d σ ε v ∈ verticiIper d := by
  rw [mem_verticiIper_iff] at hv ⊢
  intro j
  let i : Fin d := σ.symm j
  have hj : σ i = j := σ.apply_symm_apply j
  have hcoord : segnoPerm d σ ε v j = (ε i : ℝ) * v i := by
    rw [← hj]
    exact segnoLinear_apply_coord d σ ε v i
  rw [hcoord]
  have hs := (ε i).property
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with hs | hs <;> rcases hv i with hv | hv <;>
    rw [hs, hv] <;> norm_num

theorem segnoPerm_image_verticiIper (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) :
    (segnoPerm d σ ε : E d → E d) '' (verticiIper d : Set (E d)) =
      (verticiIper d : Set (E d)) := by
  have hfin : Finset.image (segnoPerm d σ ε : E d → E d) (verticiIper d) =
      verticiIper d := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact segnoPerm_mem_verticiIper d σ ε hu
    · rw [Finset.card_image_of_injective _ (segnoPerm d σ ε).injective]
  rw [← Finset.coe_image, hfin]

theorem segnoPerm_isSymmetry_ipercubo (d : ℕ) (hd : 1 ≤ d)
    (σ : Equiv.Perm (Fin d)) (ε : Fin d → ({-1, 1} : Set ℝ)) :
    (ipercubo d hd).isSymmetry (segnoPerm d σ ε) := by
  rw [ConvexPolytope.isSymmetry, ConvexPolytope.toSet]
  calc
    (segnoPerm d σ ε : E d → E d) ''
        convexHull ℝ ((ipercubo d hd).vertices : Set (E d)) =
      convexHull ℝ ((segnoPerm d σ ε : E d → E d) ''
        ((ipercubo d hd).vertices : Set (E d))) := by
          exact (segnoPerm d σ ε).toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ ((ipercubo d hd).vertices : Set (E d)) := by
      rw [show ((ipercubo d hd).vertices : Set (E d)) =
          (verticiIper d : Set (E d)) by rfl,
        segnoPerm_image_verticiIper]

/-- Mescola, coordinata per coordinata, due codici di vertice. -/
def boolMix {d : ℕ} (a b m : Fin d → Bool) : Fin d → Bool :=
  fun i => if m i then a i else b i

@[simp] theorem boolMix_apply {d : ℕ} (a b m : Fin d → Bool) (i : Fin d) :
    boolMix a b m i = if m i then a i else b i := rfl

theorem vertIper_mix_add {d : ℕ} (a b m : Fin d → Bool) :
    vertIper (boolMix a b m) + vertIper (boolMix a b (fun i => !(m i))) =
      vertIper a + vertIper b := by
  ext i
  cases hmi : m i
  · simp [hmi]
    ring
  · simp [hmi]

open Classical in
/-- Le facce dell'ipercubo sono chiuse rispetto al mescolamento indipendente
delle coordinate di due loro vertici. -/
theorem ipercubo_face_mix (d : ℕ) (hd : 1 ≤ d) {f : Set (E d)}
    (hf : (ipercubo d hd).IsFace f) {a b : Fin d → Bool}
    (haF : vertIper a ∈ f) (hbF : vertIper b ∈ f) (m : Fin d → Bool) :
    vertIper (boolMix a b m) ∈ f := by
  let P := ipercubo d hd
  let u := vertIper (boolMix a b m)
  let u' := vertIper (boolMix a b (fun i => !(m i)))
  have haP : vertIper a ∈ P.toSet :=
    subset_convexHull ℝ _ (by
      exact_mod_cast (mem_verticiIper.mpr ⟨a, rfl⟩))
  have hbP : vertIper b ∈ P.toSet :=
    subset_convexHull ℝ _ (by
      exact_mod_cast (mem_verticiIper.mpr ⟨b, rfl⟩))
  have huP : u ∈ P.toSet :=
    subset_convexHull ℝ _ (by
      exact_mod_cast (mem_verticiIper.mpr ⟨boolMix a b m, rfl⟩))
  have hu'P : u' ∈ P.toSet :=
    subset_convexHull ℝ _ (by
      exact_mod_cast
        (mem_verticiIper.mpr ⟨boolMix a b (fun i => !(m i)), rfl⟩))
  obtain ⟨l, hmem, hchar⟩ := espositore_di_faccia P hf
  have ha := hmem (vertIper a) haF
  have hb := hmem (vertIper b) hbF
  have hab : l (vertIper a) = l (vertIper b) :=
    le_antisymm (hb.2 _ haP) (ha.2 _ hbP)
  have hsum : u + u' = vertIper a + vertIper b :=
    vertIper_mix_add a b m
  have hlsum := congrArg l hsum
  simp only [map_add] at hlsum
  have hlu_le : l u ≤ l (vertIper a) := ha.2 _ huP
  have hlu'_le : l u' ≤ l (vertIper a) := ha.2 _ hu'P
  have hlu : l u = l (vertIper a) := by linarith
  apply hchar u huP
  intro z hz
  rw [hlu]
  exact ha.2 z hz

open Classical in
/-- Coordinate che possono variare in una faccia, rispetto a un suo vertice base. -/
noncomputable def iperFaceFree {d : ℕ} (f : Set (E d)) (s : Fin d → Bool) :
    Finset (Fin d) :=
  Finset.univ.filter (fun i => ∃ t : Fin d → Bool, vertIper t ∈ f ∧ t i ≠ s i)

open Classical in
theorem mem_iperFaceFree {d : ℕ} {f : Set (E d)} {s : Fin d → Bool} {i : Fin d} :
    i ∈ iperFaceFree f s ↔
      ∃ t : Fin d → Bool, vertIper t ∈ f ∧ t i ≠ s i := by
  simp [iperFaceFree]

open Classical in
theorem ipercubo_face_singleFlip (d : ℕ) (hd : 1 ≤ d) {f : Set (E d)}
    (hf : (ipercubo d hd).IsFace f) {s : Fin d → Bool} (hs : vertIper s ∈ f)
    {i : Fin d} (hi : i ∈ iperFaceFree f s) :
    vertIper (boolFlip s i) ∈ f := by
  obtain ⟨t, htF, hti⟩ := mem_iperFaceFree.mp hi
  have hit : t i = !s i := by
    cases hsi : s i <;> cases hti' : t i <;> simp_all
  let m : Fin d → Bool := fun j => decide (j = i)
  have hmix := ipercubo_face_mix d hd hf htF hs m
  convert hmix using 1
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp [boolMix, boolFlip, m, hit]
  · simp [boolMix, boolFlip, m, hji]

/-- Sostituisce in `s` con i valori di `t` le coordinate di `A`. -/
def boolPatch {d : ℕ} (s t : Fin d → Bool) (A : Finset (Fin d)) : Fin d → Bool :=
  fun i => if i ∈ A then t i else s i

@[simp] theorem boolPatch_apply {d : ℕ} (s t : Fin d → Bool)
    (A : Finset (Fin d)) (i : Fin d) :
    boolPatch s t A i = if i ∈ A then t i else s i := rfl

open Classical in
theorem ipercubo_face_patch (d : ℕ) (hd : 1 ≤ d) {f : Set (E d)}
    (hf : (ipercubo d hd).IsFace f) {s : Fin d → Bool} (hs : vertIper s ∈ f)
    (t : Fin d → Bool) {A : Finset (Fin d)} (hA : A ⊆ iperFaceFree f s) :
    vertIper (boolPatch s t A) ∈ f := by
  induction A using Finset.induction_on with
  | empty =>
      have hpatch : boolPatch s t ∅ = s := by
        funext i
        simp [boolPatch]
      rw [hpatch]
      exact hs
  | @insert i A hi ih =>
      have hAsub : A ⊆ iperFaceFree f s :=
        fun j hj => hA (Finset.mem_insert_of_mem hj)
      have hprev := ih hAsub
      by_cases hti : t i = s i
      · convert hprev using 1
        congr 1
        funext j
        by_cases hji : j = i
        · subst j
          simp [boolPatch, hti]
        · simp [boolPatch, hji]
      · have hiFree : i ∈ iperFaceFree f s := hA (by simp)
        have hflip := ipercubo_face_singleFlip d hd hf hs hiFree
        let m : Fin d → Bool := fun j => decide (j = i)
        have hmix := ipercubo_face_mix d hd hf hflip hprev m
        convert hmix using 1
        congr 1
        funext j
        by_cases hji : j = i
        · subst j
          have hnot : (!s i) = t i := by
            cases hsi : s i <;> cases hti' : t i <;> simp_all
          simp [boolMix, boolPatch, boolFlip, m, hnot]
        · simp [boolMix, boolPatch, m, hji]

open Classical in
/-- Classificazione dei vertici di una faccia: fuori dalle coordinate libere
tutti i segni coincidono con quelli del vertice base. -/
theorem vertIper_mem_face_iff (d : ℕ) (hd : 1 ≤ d) {f : Set (E d)}
    (hf : (ipercubo d hd).IsFace f) {s : Fin d → Bool} (hs : vertIper s ∈ f)
    (t : Fin d → Bool) :
    vertIper t ∈ f ↔ ∀ i ∉ iperFaceFree f s, t i = s i := by
  constructor
  · intro ht i hi
    by_contra hne
    exact hi (mem_iperFaceFree.mpr ⟨t, ht, hne⟩)
  · intro ht
    have hp := ipercubo_face_patch d hd hf hs t
      (show iperFaceFree f s ⊆ iperFaceFree f s from fun _ h => h)
    convert hp using 1
    congr 1
    funext i
    by_cases hi : i ∈ iperFaceFree f s
    · simp [boolPatch, hi]
    · simp [boolPatch, hi, ht i hi]

/-- Sottospazio generato dagli assi di un insieme di coordinate. -/
noncomputable def iperCoordSpan {d : ℕ} (A : Finset (Fin d)) : Submodule ℝ (E d) :=
  Submodule.span ℝ
    ((fun i : Fin d => (EuclideanSpace.basisFun (Fin d) ℝ) i) '' (A : Set (Fin d)))

theorem basis_mem_iperCoordSpan {d : ℕ} {A : Finset (Fin d)} {i : Fin d}
    (hi : i ∈ A) :
    (EuclideanSpace.basisFun (Fin d) ℝ) i ∈ iperCoordSpan A := by
  apply Submodule.subset_span
  exact ⟨i, by exact_mod_cast hi, rfl⟩

theorem mem_iperCoordSpan_of_eq_zero {d : ℕ} {A : Finset (Fin d)} {x : E d}
    (hx : ∀ i ∉ A, x i = 0) : x ∈ iperCoordSpan A := by
  rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i ∈ A
  · exact (iperCoordSpan A).smul_mem _ (basis_mem_iperCoordSpan hi)
  · have hrepr : ((EuclideanSpace.basisFun (Fin d) ℝ).repr x) i = 0 := by
      rw [EuclideanSpace.basisFun_repr]
      exact hx i hi
    rw [hrepr, zero_smul]
    exact (iperCoordSpan A).zero_mem

theorem finrank_iperCoordSpan {d : ℕ} (A : Finset (Fin d)) :
    Module.finrank ℝ (iperCoordSpan A) = A.card := by
  let b : {i : Fin d // i ∈ A} → E d :=
    fun i => (EuclideanSpace.basisFun (Fin d) ℝ) i.1
  have hb : LinearIndependent ℝ b := by
    exact (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.linearIndependent.comp
      (fun i : {i : Fin d // i ∈ A} => i.1) Subtype.val_injective
  have hrange : Set.range b =
      (fun i : Fin d => (EuclideanSpace.basisFun (Fin d) ℝ) i) ''
        (A : Set (Fin d)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, by exact_mod_cast i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, by exact_mod_cast hi⟩, rfl⟩
  unfold iperCoordSpan
  rw [← hrange, finrank_span_eq_card hb]
  simp

open Classical in
/-- Il sottospazio direttore di una faccia dell'ipercubo è generato
esattamente dagli assi delle sue coordinate libere. -/
theorem ipercubo_face_vectorSpan (d : ℕ) (hd : 1 ≤ d) {f : Set (E d)}
    (hf : (ipercubo d hd).IsFace f) {s : Fin d → Bool} (hs : vertIper s ∈ f) :
    vectorSpan ℝ f = iperCoordSpan (iperFaceFree f s) := by
  let S : Finset (E d) := (ipercubo d hd).vertices.filter (· ∈ f)
  have hsS : vertIper s ∈ (S : Set (E d)) := by
    exact_mod_cast (Finset.mem_filter.mpr
      ⟨mem_verticiIper.mpr ⟨s, rfl⟩, hs⟩)
  have hFS : f = convexHull ℝ (S : Set (E d)) :=
    face_eq_hull_vertices _ hf
  have hspan : vectorSpan ℝ f = vectorSpan ℝ (S : Set (E d)) := by
    rw [hFS, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
  rw [hspan]
  apply le_antisymm
  · rw [vectorSpan_eq_span_vsub_set_right ℝ hsS, Submodule.span_le]
    rintro y ⟨x, hxS, rfl⟩
    have hxV : x ∈ (ipercubo d hd).vertices :=
      (Finset.mem_filter.mp (by exact_mod_cast hxS)).1
    have hxF : x ∈ f :=
      (Finset.mem_filter.mp (by exact_mod_cast hxS)).2
    obtain ⟨t, rfl⟩ := mem_verticiIper.mp hxV
    apply mem_iperCoordSpan_of_eq_zero
    intro i hi
    have hit := (vertIper_mem_face_iff d hd hf hs t).mp hxF i hi
    simp [hit]
  · unfold iperCoordSpan
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i ∈ iperFaceFree f s := by exact_mod_cast hi
    have hflipF := ipercubo_face_singleFlip d hd hf hs hi'
    have hflipS : vertIper (boolFlip s i) ∈ (S : Set (E d)) := by
      exact_mod_cast (Finset.mem_filter.mpr
        ⟨mem_verticiIper.mpr ⟨boolFlip s i, rfl⟩, hflipF⟩)
    have hdiff : vertIper s - vertIper (boolFlip s i) ∈
        vectorSpan ℝ (S : Set (E d)) :=
      vsub_mem_vectorSpan ℝ hsS hflipS
    rw [vertIper_sub_flip] at hdiff
    by_cases hsi : s i
    · simp [hsi] at hdiff
      simpa [EuclideanSpace.basisFun_apply] using hdiff
    · simp [hsi] at hdiff
      simpa [EuclideanSpace.basisFun_apply] using hdiff

theorem ipercubo_face_free_card (d : ℕ) (hd : 1 ≤ d) {f : Set (E d)}
    (hf : (ipercubo d hd).IsFace f) {s : Fin d → Bool} (hs : vertIper s ∈ f) :
    (iperFaceFree f s).card = faceDim f := by
  unfold faceDim
  rw [ipercubo_face_vectorSpan d hd hf hs, finrank_iperCoordSpan]

open Classical in
theorem ipercubo_face_vertices_nonempty (d : ℕ) (hd : 1 ≤ d) {f : Set (E d)}
    (hf : (ipercubo d hd).IsFace f) :
    ((ipercubo d hd).vertices.filter (· ∈ f)).Nonempty := by
  let S : Finset (E d) := (ipercubo d hd).vertices.filter (· ∈ f)
  have hFS : f = convexHull ℝ (S : Set (E d)) := face_eq_hull_vertices _ hf
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hS : S = ∅ := by simpa [S] using h
  have hne := hf.2
  rw [hFS, hS] at hne
  simp at hne

open Classical in
/-- Codice del vertice iniziale di una bandiera. -/
noncomputable def ipercuboFlagBaseCode (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) : Fin d → Bool := by
  let z : Fin d := ⟨0, hd⟩
  let v := (ipercubo_face_vertices_nonempty d hd (F.isFace z)).choose
  have hv : v ∈ verticiIper d :=
    (Finset.mem_filter.mp
      (ipercubo_face_vertices_nonempty d hd (F.isFace z)).choose_spec).1
  exact (mem_verticiIper.mp hv).choose

open Classical in
theorem ipercuboFlagBaseCode_spec (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) :
    vertIper (ipercuboFlagBaseCode d hd F) ∈ F.face ⟨0, hd⟩ := by
  let z : Fin d := ⟨0, hd⟩
  let v := (ipercubo_face_vertices_nonempty d hd (F.isFace z)).choose
  have hvS := (ipercubo_face_vertices_nonempty d hd (F.isFace z)).choose_spec
  have hvV : v ∈ verticiIper d := (Finset.mem_filter.mp hvS).1
  have hvF : v ∈ F.face z := (Finset.mem_filter.mp hvS).2
  have hcode : vertIper (ipercuboFlagBaseCode d hd F) = v := by
    exact (mem_verticiIper.mp hvV).choose_spec
  rwa [hcode]

theorem ipercuboFlagBaseCode_mem (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    vertIper (ipercuboFlagBaseCode d hd F) ∈ F.face k := by
  let z : Fin d := ⟨0, hd⟩
  have hz := ipercuboFlagBaseCode_spec d hd F
  by_cases hk : k.val = 0
  · have hkz : k = z := by ext; simpa [z] using hk
    simpa [hkz, z] using hz
  · have hzk : z < k := by
      apply Fin.mk_lt_mk.mpr
      omega
    exact (F.strict_mono z k hzk).1 hz

open Classical in
/-- Coordinate libere nella faccia di rango `k` di una bandiera. -/
noncomputable def ipercuboFlagFree (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) : Finset (Fin d) :=
  iperFaceFree (F.face k) (ipercuboFlagBaseCode d hd F)

theorem ipercuboFlagFree_card (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    (ipercuboFlagFree d hd F k).card = k.val := by
  rw [ipercuboFlagFree, ipercubo_face_free_card d hd (F.isFace k)
    (ipercuboFlagBaseCode_mem d hd F k), F.dim_eq]

open Classical in
theorem ipercuboFlagFree_mono (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) {i j : Fin d} (hij : i ≤ j) :
    ipercuboFlagFree d hd F i ⊆ ipercuboFlagFree d hd F j := by
  intro q hq
  obtain ⟨t, htF, htq⟩ := mem_iperFaceFree.mp hq
  apply mem_iperFaceFree.mpr
  refine ⟨t, ?_, htq⟩
  rcases hij.eq_or_lt with rfl | hij
  · exact htF
  · exact (F.strict_mono i j hij).1 htF

open Classical in
/-- Stadio successivo delle coordinate libere; dopo l'ultima faccia è `univ`. -/
noncomputable def ipercuboFlagNextFree (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) : Finset (Fin d) :=
  if hk : k.val + 1 < d then
    ipercuboFlagFree d hd F ⟨k.val + 1, hk⟩
  else Finset.univ

open Classical in
theorem ipercuboFlagFree_subset_next (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    ipercuboFlagFree d hd F k ⊆ ipercuboFlagNextFree d hd F k := by
  by_cases hk : k.val + 1 < d
  · simp only [ipercuboFlagNextFree, dif_pos hk]
    apply ipercuboFlagFree_mono d hd F
    exact Fin.mk_le_mk.mpr (Nat.le_succ k.val)
  · simp [ipercuboFlagNextFree, hk]

open Classical in
theorem ipercuboFlagNextFree_card (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    (ipercuboFlagNextFree d hd F k).card = k.val + 1 := by
  by_cases hk : k.val + 1 < d
  · simp [ipercuboFlagNextFree, hk, ipercuboFlagFree_card]
  · have heq : d = k.val + 1 := by omega
    simp [ipercuboFlagNextFree, heq]

open Classical in
theorem ipercuboFlagStep_card (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    (ipercuboFlagNextFree d hd F k \ ipercuboFlagFree d hd F k).card = 1 := by
  rw [Finset.card_sdiff_of_subset (ipercuboFlagFree_subset_next d hd F k),
    ipercuboFlagNextFree_card, ipercuboFlagFree_card]
  omega

open Classical in
noncomputable def ipercuboFlagCoord (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) : Fin d :=
  (Finset.card_pos.mp (by rw [ipercuboFlagStep_card d hd F k]; omega)).choose

open Classical in
theorem ipercuboFlagCoord_mem_next (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    ipercuboFlagCoord d hd F k ∈ ipercuboFlagNextFree d hd F k :=
  (Finset.mem_sdiff.mp
    (Finset.card_pos.mp (by rw [ipercuboFlagStep_card d hd F k]; omega)).choose_spec).1

open Classical in
theorem ipercuboFlagCoord_not_free (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    ipercuboFlagCoord d hd F k ∉ ipercuboFlagFree d hd F k :=
  (Finset.mem_sdiff.mp
    (Finset.card_pos.mp (by rw [ipercuboFlagStep_card d hd F k]; omega)).choose_spec).2

open Classical in
theorem ipercuboFlagCoord_mem_free_of_lt (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) {i j : Fin d} (hij : i < j) :
    ipercuboFlagCoord d hd F i ∈ ipercuboFlagFree d hd F j := by
  have hisucc : i.val + 1 < d := by omega
  have hmem : ipercuboFlagCoord d hd F i ∈
      ipercuboFlagFree d hd F ⟨i.val + 1, hisucc⟩ := by
    simpa [ipercuboFlagNextFree, hisucc] using
      ipercuboFlagCoord_mem_next d hd F i
  apply ipercuboFlagFree_mono d hd F (i := ⟨i.val + 1, hisucc⟩) (j := j)
  · exact Fin.mk_le_mk.mpr (by omega)
  · exact hmem

open Classical in
theorem ipercuboFlagCoord_injective (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) :
    Function.Injective (ipercuboFlagCoord d hd F) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · exact (ipercuboFlagCoord_not_free d hd F j)
      (hij ▸ ipercuboFlagCoord_mem_free_of_lt d hd F hijlt)
  · exact (ipercuboFlagCoord_not_free d hd F i)
      (hij.symm ▸ ipercuboFlagCoord_mem_free_of_lt d hd F hjilt)

open Classical in
noncomputable def ipercuboFlagCoordEquiv (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) : Equiv.Perm (Fin d) :=
  Equiv.ofBijective (ipercuboFlagCoord d hd F)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨ipercuboFlagCoord_injective d hd F, rfl⟩)

@[simp] theorem ipercuboFlagCoordEquiv_apply (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    ipercuboFlagCoordEquiv d hd F k = ipercuboFlagCoord d hd F k := rfl

open Classical in
theorem ipercuboFlagFree_eq_image_Iio (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    ipercuboFlagFree d hd F k =
      (Finset.Iio k).image (ipercuboFlagCoord d hd F) := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    exact ipercuboFlagCoord_mem_free_of_lt d hd F (Finset.mem_Iio.mp hi)
  · rw [Finset.card_image_of_injective _ (ipercuboFlagCoord_injective d hd F),
      ipercuboFlagFree_card]
    simp

open Classical in
/-- Restrizione alle coordinate di `A` dei codici che coincidono con `s`
fuori da `A`. -/
noncomputable def iperAgreeEquiv {d : ℕ} (A : Finset (Fin d)) (s : Fin d → Bool) :
    {t : Fin d → Bool // ∀ i, i ∉ A → t i = s i} ≃ ({i : Fin d // i ∈ A} → Bool) where
  toFun t i := t.1 i.1
  invFun u := ⟨fun i => if hi : i ∈ A then u ⟨i, hi⟩ else s i, by
    intro i hi
    simp [hi]⟩
  left_inv t := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ A
    · simp [hi]
    · simp [hi, t.2 i hi]
  right_inv u := by
    funext i
    simp [i.2]

open Classical in
theorem card_signs_agree {d : ℕ} (A : Finset (Fin d)) (s : Fin d → Bool) :
    ((Finset.univ : Finset (Fin d → Bool)).filter
      (fun t => ∀ i, i ∉ A → t i = s i)).card = 2 ^ A.card := by
  calc
    ((Finset.univ : Finset (Fin d → Bool)).filter
        (fun t => ∀ i, i ∉ A → t i = s i)).card =
        (Finset.univ : Finset ({i : Fin d // i ∈ A} → Bool)).card := by
      refine Finset.card_bij'
        (fun t _ i => t i.1)
        (fun u _ i => if hi : i ∈ A then u ⟨i, hi⟩ else s i)
        (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro u _
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro i hi
        simp [hi]
      · intro t ht
        funext i
        by_cases hi : i ∈ A
        · simp [hi]
        · have hit := (Finset.mem_filter.mp ht).2 i hi
          simp [hi, hit]
      · intro u _
        funext i
        simp [i.2]
    _ = 2 ^ A.card := by simp

open Classical in
noncomputable def ipercuboFlagVertices (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) : Finset (E d) :=
  (ipercubo d hd).vertices.filter (· ∈ F.face k)

open Classical in
theorem ipercuboFlagVertices_eq_image_codes (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    ipercuboFlagVertices d hd F k =
      ((Finset.univ : Finset (Fin d → Bool)).filter
        (fun t => vertIper t ∈ F.face k)).image vertIper := by
  ext x
  constructor
  · intro hx
    have hx' := Finset.mem_filter.mp hx
    obtain ⟨t, rfl⟩ := mem_verticiIper.mp hx'.1
    exact Finset.mem_image.mpr ⟨t, by simp [hx'.2], rfl⟩
  · intro hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    have htF : vertIper t ∈ F.face k := by simpa using (Finset.mem_filter.mp ht).2
    exact Finset.mem_filter.mpr ⟨mem_verticiIper.mpr ⟨t, rfl⟩, htF⟩

open Classical in
theorem ipercuboFlagVertices_card (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    (ipercuboFlagVertices d hd F k).card = 2 ^ k.val := by
  rw [ipercuboFlagVertices_eq_image_codes,
    Finset.card_image_of_injective _ vertIper_injective]
  have hfilter :
      (Finset.univ : Finset (Fin d → Bool)).filter
          (fun t => vertIper t ∈ F.face k) =
        (Finset.univ : Finset (Fin d → Bool)).filter
          (fun t => ∀ i, i ∉ ipercuboFlagFree d hd F k →
            t i = ipercuboFlagBaseCode d hd F i) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact vertIper_mem_face_iff d hd (F.isFace k)
      (ipercuboFlagBaseCode_mem d hd F k) t
  rw [hfilter, card_signs_agree, ipercuboFlagFree_card]

open Classical in
noncomputable def ipercuboFlagPerm (d : ℕ) (hd : 1 ≤ d)
    (F G : (ipercubo d hd).Flag) : Equiv.Perm (Fin d) :=
  (ipercuboFlagCoordEquiv d hd F).symm.trans
    (ipercuboFlagCoordEquiv d hd G)

@[simp] theorem ipercuboFlagPerm_coord (d : ℕ) (hd : 1 ≤ d)
    (F G : (ipercubo d hd).Flag) (k : Fin d) :
    ipercuboFlagPerm d hd F G (ipercuboFlagCoord d hd F k) =
      ipercuboFlagCoord d hd G k := by
  change ipercuboFlagCoordEquiv d hd G
    ((ipercuboFlagCoordEquiv d hd F).symm
      (ipercuboFlagCoordEquiv d hd F k)) = _
  rw [(ipercuboFlagCoordEquiv d hd F).symm_apply_apply]
  rfl

open Classical in
theorem ipercuboFlagPerm_mem_free_iff (d : ℕ) (hd : 1 ≤ d)
    (F G : (ipercubo d hd).Flag) (k : Fin d) (i : Fin d) :
    ipercuboFlagPerm d hd F G i ∈ ipercuboFlagFree d hd G k ↔
      i ∈ ipercuboFlagFree d hd F k := by
  rw [ipercuboFlagFree_eq_image_Iio, ipercuboFlagFree_eq_image_Iio]
  constructor
  · intro hi
    obtain ⟨r, hr, hir⟩ := Finset.mem_image.mp hi
    apply Finset.mem_image.mpr
    refine ⟨r, hr, ?_⟩
    apply (ipercuboFlagPerm d hd F G).injective
    rw [ipercuboFlagPerm_coord]
    exact hir
  · intro hi
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_image.mpr
    exact ⟨r, hr, (ipercuboFlagPerm_coord d hd F G r).symm⟩

open Classical in
/-- Segni che mandano il vertice base di `F` in quello di `G`. -/
noncomputable def ipercuboFlagSign (d : ℕ) (hd : 1 ≤ d)
    (F G : (ipercubo d hd).Flag) (i : Fin d) : ({-1, 1} : Set ℝ) :=
  if ipercuboFlagBaseCode d hd F i =
      ipercuboFlagBaseCode d hd G (ipercuboFlagPerm d hd F G i) then
    ⟨1, by simp⟩ else ⟨-1, by simp⟩

open Classical in
theorem ipercuboFlagIsom_base (d : ℕ) (hd : 1 ≤ d)
    (F G : (ipercubo d hd).Flag) :
    segnoPerm d (ipercuboFlagPerm d hd F G) (ipercuboFlagSign d hd F G)
        (vertIper (ipercuboFlagBaseCode d hd F)) =
      vertIper (ipercuboFlagBaseCode d hd G) := by
  let σ := ipercuboFlagPerm d hd F G
  let ε := ipercuboFlagSign d hd F G
  ext j
  let i : Fin d := σ.symm j
  have hj : σ i = j := σ.apply_symm_apply j
  rw [← hj]
  change segnoLinear d (ipercuboFlagPerm d hd F G)
      (ipercuboFlagSign d hd F G)
        (vertIper (ipercuboFlagBaseCode d hd F))
          (ipercuboFlagPerm d hd F G i) =
    vertIper (ipercuboFlagBaseCode d hd G) (ipercuboFlagPerm d hd F G i)
  rw [segnoLinear_apply_coord]
  unfold ipercuboFlagSign
  dsimp only
  cases hF : ipercuboFlagBaseCode d hd F i <;>
    cases hG : ipercuboFlagBaseCode d hd G (ipercuboFlagPerm d hd F G i) <;>
      simp [hF, hG]

open Classical in
theorem ipercuboFlagIsom_mem_vertices (d : ℕ) (hd : 1 ≤ d)
    (F G : (ipercubo d hd).Flag) (k : Fin d) {v : E d}
    (hv : v ∈ ipercuboFlagVertices d hd F k) :
    segnoPerm d (ipercuboFlagPerm d hd F G) (ipercuboFlagSign d hd F G) v ∈
      ipercuboFlagVertices d hd G k := by
  let σ := ipercuboFlagPerm d hd F G
  let ε := ipercuboFlagSign d hd F G
  have hv' := Finset.mem_filter.mp hv
  obtain ⟨t, rfl⟩ := mem_verticiIper.mp hv'.1
  have hyV : segnoPerm d σ ε (vertIper t) ∈ verticiIper d :=
    segnoPerm_mem_verticiIper d σ ε (mem_verticiIper.mpr ⟨t, rfl⟩)
  obtain ⟨u, hu⟩ := mem_verticiIper.mp hyV
  have htfree := (vertIper_mem_face_iff d hd (F.isFace k)
    (ipercuboFlagBaseCode_mem d hd F k) t).mp hv'.2
  have hufree : ∀ j ∉ ipercuboFlagFree d hd G k,
      u j = ipercuboFlagBaseCode d hd G j := by
    intro j hj
    let i : Fin d := σ.symm j
    have hji : σ i = j := σ.apply_symm_apply j
    have hi : i ∉ ipercuboFlagFree d hd F k := by
      intro hiF
      apply hj
      rw [← hji]
      exact (ipercuboFlagPerm_mem_free_iff d hd F G k i).mpr hiF
    have hti := htfree i hi
    have hcoord : vertIper u j =
        vertIper (ipercuboFlagBaseCode d hd G) j := by
      calc
        vertIper u j = segnoPerm d σ ε (vertIper t) j := by rw [hu]
        _ = segnoPerm d σ ε
            (vertIper (ipercuboFlagBaseCode d hd F)) j := by
              rw [← hji]
              change segnoLinear d σ ε (vertIper t) (σ i) =
                segnoLinear d σ ε
                  (vertIper (ipercuboFlagBaseCode d hd F)) (σ i)
              rw [segnoLinear_apply_coord, segnoLinear_apply_coord]
              simp only [vertIper_apply]
              rw [hti]
        _ = vertIper (ipercuboFlagBaseCode d hd G) j := by
              rw [ipercuboFlagIsom_base d hd F G]
    cases huj : u j <;>
      cases hGj : ipercuboFlagBaseCode d hd G j <;>
        simp [huj, hGj] at hcoord ⊢ <;> norm_num at hcoord
  apply Finset.mem_filter.mpr
  refine ⟨hyV, ?_⟩
  rw [← hu]
  exact (vertIper_mem_face_iff d hd (G.isFace k)
    (ipercuboFlagBaseCode_mem d hd G k) u).mpr hufree

open Classical in
theorem ipercuboFlagIsom_image_vertices (d : ℕ) (hd : 1 ≤ d)
    (F G : (ipercubo d hd).Flag) (k : Fin d) :
    Finset.image
        (segnoPerm d (ipercuboFlagPerm d hd F G) (ipercuboFlagSign d hd F G))
        (ipercuboFlagVertices d hd F k) =
      ipercuboFlagVertices d hd G k := by
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact ipercuboFlagIsom_mem_vertices d hd F G k hu
  · rw [Finset.card_image_of_injective _
      (segnoPerm d (ipercuboFlagPerm d hd F G)
        (ipercuboFlagSign d hd F G)).injective,
      ipercuboFlagVertices_card, ipercuboFlagVertices_card]

open Classical in
theorem ipercuboFlagIsom_image_face (d : ℕ) (hd : 1 ≤ d)
    (F G : (ipercubo d hd).Flag) (k : Fin d) :
    (segnoPerm d (ipercuboFlagPerm d hd F G) (ipercuboFlagSign d hd F G) :
        E d → E d) '' F.face k = G.face k := by
  let φ := segnoPerm d (ipercuboFlagPerm d hd F G) (ipercuboFlagSign d hd F G)
  calc
    (φ : E d → E d) '' F.face k =
        (φ : E d → E d) '' convexHull ℝ
          ((ipercuboFlagVertices d hd F k : Finset (E d)) : Set (E d)) := by
      rw [face_eq_hull_vertices (ipercubo d hd) (F.isFace k)]
      rfl
    _ = convexHull ℝ ((φ : E d → E d) ''
          ((ipercuboFlagVertices d hd F k : Finset (E d)) : Set (E d))) := by
      exact φ.toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ
          ((ipercuboFlagVertices d hd G k : Finset (E d)) : Set (E d)) := by
      rw [← Finset.coe_image, ipercuboFlagIsom_image_vertices d hd F G k]
    _ = G.face k := by
      rw [face_eq_hull_vertices (ipercubo d hd) (G.isFace k)]
      rfl

open Classical in
theorem ipercubo_isRegular (d : ℕ) (hd : 1 ≤ d) :
    (ipercubo d hd).IsRegular := by
  refine ⟨ipercubo_isFullDim d hd, ?_⟩
  intro F G
  refine ⟨segnoPerm d (ipercuboFlagPerm d hd F G) (ipercuboFlagSign d hd F G),
    segnoPerm_isSymmetry_ipercubo d hd _ _, ?_⟩
  exact ipercuboFlagIsom_image_face d hd F G

theorem ipercubo_mem_regularPolytopes (d : ℕ) (hd : 1 ≤ d) :
    ipercubo d hd ∈ regularPolytopes d :=
  ipercubo_isRegular d hd

end LeanEval.Geometry.PlatonicClassification
