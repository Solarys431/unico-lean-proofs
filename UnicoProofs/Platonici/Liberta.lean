import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.PerturbazioneFinita
import UnicoProofs.Platonici.SottoPolitopo
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.BandieraCompagna
import UnicoProofs.Platonici.Diamante
import UnicoProofs.Platonici.InvarianteSimilarita

/-!
FASE 3A, F1 — LA LIBERTÀ (18 lug 2026).

Una simmetria che fissa (insiemisticamente) tutte le facce di una bandiera
di un politopo full-dim di ℝ³ è l'identità. Strumento: i baricentri dei
vertici delle facce della bandiera e del corpo. La simmetria permuta i
vertici di ogni faccia fissata, quindi fissa i quattro baricentri; i tre
spostamenti b₁−b₀, b₂−b₀, b₃−b₀ sono linearmente indipendenti (gli
espositori delle facce li uccidono a scala: ogni lᵏ annulla i primi k e
morde strettamente il successivo, perché la media dei vertici con un
testimone fuori faccia sta strettamente sotto il massimo); dunque generano
ℝ³ e la simmetria, fissando b₀ e i tre spostamenti, fissa tutto.

COROLLARIO CHIAVE: il trasportatore tra due bandiere è UNICO. Il
quantificatore «per ogni trasportatore» del certificato d'orbita del fan
collassa sul trasportatore costruito.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Una simmetria manda i vertici nei vertici. -/
theorem simmetria_immagine_vertici (P : ConvexPolytope n) {σ : Isom n}
    (hσ : P.isSymmetry σ) :
    (σ : E n → E n) '' (P.vertices : Set (E n)) = (P.vertices : Set (E n)) := by
  have hv : (P.vertices : Set (E n)) = Set.extremePoints ℝ P.toSet :=
    P.vertices_eq_extremePoints
  have hcoe : (⇑σ.toAffineEquiv : E n → E n) = (σ : E n → E n) := by
    ext x
    simp
  have himg : (⇑σ.toAffineEquiv) '' P.toSet = P.toSet := by
    rw [hcoe]
    exact hσ
  calc (σ : E n → E n) '' (P.vertices : Set (E n))
      = (⇑σ.toAffineEquiv) '' (Set.extremePoints ℝ P.toSet) := by rw [hv, hcoe]
    _ = Set.extremePoints ℝ ((⇑σ.toAffineEquiv) '' P.toSet) :=
        (extremePoints_image_affineEquiv σ.toAffineEquiv P.toSet).symm
    _ = Set.extremePoints ℝ P.toSet := by rw [himg]
    _ = (P.vertices : Set (E n)) := hv.symm

/-- Una simmetria che fissa un insieme finito ne fissa il baricentro. -/
theorem centroide_fisso {σ : Isom n} {W : Finset (E n)}
    (himg : (σ : E n → E n) '' (W : Set (E n)) = (W : Set (E n)))
    (hWne : W.Nonempty) :
    σ (W.centroid ℝ id) = W.centroid ℝ id := by
  classical
  have hw1 : W.sum (W.centroidWeights ℝ) = 1 :=
    W.sum_centroidWeights_eq_one_of_nonempty ℝ hWne
  have hcoeA : (⇑σ.toAffineEquiv.toAffineMap : E n → E n) = (σ : E n → E n) := by
    ext x
    simp
  have hmap := W.map_affineCombination id (W.centroidWeights ℝ) hw1
    σ.toAffineEquiv.toAffineMap
  have heq : W.centroid ℝ (⇑σ.toAffineEquiv.toAffineMap ∘ id) =
      W.centroid ℝ id := by
    apply Finset.centroid_eq_of_inj_on_of_image_eq
    · intro i _ j _ hij
      have h1 : σ i = σ j := by
        simpa [hcoeA] using hij
      exact σ.injective h1
    · intro i _ j _ hij
      exact hij
    · rw [Set.image_comp]
      simp only [Set.image_id, Function.comp_id]
      rw [hcoeA]
      exact himg
  calc σ (W.centroid ℝ id)
      = σ.toAffineEquiv.toAffineMap (W.affineCombination ℝ id
          (W.centroidWeights ℝ)) := by
        rw [Finset.centroid_def]
        rw [show σ.toAffineEquiv.toAffineMap (W.affineCombination ℝ id
          (W.centroidWeights ℝ)) = σ (W.affineCombination ℝ id
          (W.centroidWeights ℝ)) from congrFun hcoeA _]
    _ = W.affineCombination ℝ (⇑σ.toAffineEquiv.toAffineMap ∘ id)
          (W.centroidWeights ℝ) := hmap
    _ = W.centroid ℝ (⇑σ.toAffineEquiv.toAffineMap ∘ id) :=
        (Finset.centroid_def _ _ _).symm
    _ = W.centroid ℝ id := heq

/-- La media dei valori di un espositore su un insieme di punti del corpo
con un testimone fuori dalla faccia sta strettamente sotto il massimo. -/
theorem media_sotto_il_massimo (P : ConvexPolytope n) {f : Set (E n)}
    {l : E n →L[ℝ] ℝ}
    (hmem : ∀ y ∈ f, y ∈ P.toSet ∧ ∀ z ∈ P.toSet, l z ≤ l y)
    (hmax : ∀ q ∈ P.toSet, (∀ z ∈ P.toSet, l z ≤ l q) → q ∈ f)
    {V : Finset (E n)} (hVsub : (V : Set (E n)) ⊆ P.toSet) (hVne : V.Nonempty)
    {u : E n} (huV : u ∈ V) (huf : u ∉ f)
    {v₀ : E n} (hv₀ : v₀ ∈ f) :
    l (V.centroid ℝ id) < l v₀ := by
  classical
  have hw1 : V.sum (V.centroidWeights ℝ) = 1 :=
    V.sum_centroidWeights_eq_one_of_nonempty ℝ hVne
  -- l del centroide = somma pesata dei valori
  have hmap := V.map_affineCombination id (V.centroidWeights ℝ) hw1
    l.toLinearMap.toAffineMap
  have hval : l (V.centroid ℝ id) =
      ∑ w ∈ V, (V.centroidWeights ℝ) w * l w := by
    rw [Finset.centroid_def]
    calc l (V.affineCombination ℝ id (V.centroidWeights ℝ))
        = l.toLinearMap.toAffineMap (V.affineCombination ℝ id
            (V.centroidWeights ℝ)) := rfl
      _ = V.affineCombination ℝ (⇑l.toLinearMap.toAffineMap ∘ id)
            (V.centroidWeights ℝ) := hmap
      _ = ∑ w ∈ V, (V.centroidWeights ℝ) w •
            (⇑l.toLinearMap.toAffineMap ∘ id) w :=
          V.affineCombination_eq_linear_combination _ _ hw1
      _ = ∑ w ∈ V, (V.centroidWeights ℝ) w * l w := by
          simp [smul_eq_mul]
  have hcard : (0 : ℝ) < (V.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hVne
  have hNpos : (0 : ℝ) < ((V.card : ℝ))⁻¹ := by positivity
  have hstrict : l u < l v₀ := by
    rcases lt_or_eq_of_le ((hmem v₀ hv₀).2 u (hVsub huV)) with h | h
    · exact h
    · exfalso
      exact huf (hmax u (hVsub huV)
        (fun z hz => le_trans ((hmem v₀ hv₀).2 z hz) (le_of_eq h.symm)))
  have hbound : ∑ w ∈ V, (V.centroidWeights ℝ) w * l w <
      ∑ w ∈ V, (V.centroidWeights ℝ) w * l v₀ := by
    apply Finset.sum_lt_sum
    · intro i hi
      rw [Finset.centroidWeights_apply]
      exact mul_le_mul_of_nonneg_left ((hmem v₀ hv₀).2 i (hVsub hi))
        (le_of_lt hNpos)
    · refine ⟨u, huV, ?_⟩
      rw [Finset.centroidWeights_apply]
      exact mul_lt_mul_of_pos_left hstrict hNpos
  have hconst : ∑ w ∈ V, (V.centroidWeights ℝ) w * l v₀ = l v₀ := by
    simp only [Finset.centroidWeights_apply]
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [hval]
  rw [hconst] at hbound
  exact hbound

/-- **LA LIBERTÀ**: una simmetria che fissa tutte le facce di una bandiera
di un politopo full-dim in ℝ³ è l'identità. -/
theorem simmetria_fissa_bandiera (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {σ : Isom 3} (hσ : P.isSymmetry σ) (F : P.Flag)
    (hfix : ∀ k : Fin 3, (σ : E 3 → E 3) '' F.face k = F.face k) :
    ∀ z : E 3, σ z = z := by
  classical
  -- i quattro baricentri
  have hface : ∀ k : Fin 3, P.IsFace (F.face k) := F.isFace
  set V0 : Finset (E 3) := (facePolytope P (hface 0)).vertices with hV0
  set V1 : Finset (E 3) := (facePolytope P (hface 1)).vertices with hV1
  set V2 : Finset (E 3) := (facePolytope P (hface 2)).vertices with hV2
  set b0 : E 3 := V0.centroid ℝ id with hb0
  set b1 : E 3 := V1.centroid ℝ id with hb1
  set b2 : E 3 := V2.centroid ℝ id with hb2
  set b3 : E 3 := P.vertices.centroid ℝ id with hb3
  have hV0ne : V0.Nonempty := (facePolytope P (hface 0)).vertices_nonempty
  have hV1ne : V1.Nonempty := (facePolytope P (hface 1)).vertices_nonempty
  have hV2ne : V2.Nonempty := (facePolytope P (hface 2)).vertices_nonempty
  -- i baricentri stanno nelle rispettive facce
  have hbmem : ∀ (k : Fin 3) (V : Finset (E 3)),
      V = (facePolytope P (hface k)).vertices → V.Nonempty →
      V.centroid ℝ id ∈ F.face k := by
    intro k V hV hne
    have h1 : V.centroid ℝ id ∈ convexHull ℝ (V : Set (E 3)) :=
      V.centroid_mem_convexHull hne
    have h2 : convexHull ℝ (V : Set (E 3)) = F.face k := by
      rw [hV]
      exact (face_eq_hull_vertices P (hface k)).symm
    rw [h2] at h1
    exact h1
  have hb0f : b0 ∈ F.face 0 := hbmem 0 V0 rfl hV0ne
  have hb1f : b1 ∈ F.face 1 := hbmem 1 V1 rfl hV1ne
  have hb2f : b2 ∈ F.face 2 := hbmem 2 V2 rfl hV2ne
  -- inclusioni della catena
  have h01 : F.face 0 ⊆ F.face 1 := (F.strict_mono 0 1 (by decide)).subset
  have h12 : F.face 1 ⊆ F.face 2 := (F.strict_mono 1 2 (by decide)).subset
  have h02 : F.face 0 ⊆ F.face 2 := h01.trans h12
  -- vertici di faccia dentro il corpo
  have hVsub : ∀ (k : Fin 3), ((facePolytope P (hface k)).vertices : Set (E 3))
      ⊆ P.toSet := by
    intro k
    intro x hx
    have h1 : x ∈ (facePolytope P (hface k)).toSet := subset_convexHull ℝ _ hx
    rw [facePolytope_toSet P (hface k)] at h1
    exact face_subset_toSet P (hface k) h1
  have hVtop : (P.vertices : Set (E 3)) ⊆ P.toSet := subset_convexHull ℝ _
  -- gli espositori delle tre facce
  obtain ⟨l0, hmem0, hmax0⟩ := espositore_di_faccia P (hface 0)
  obtain ⟨l1, hmem1, hmax1⟩ := espositore_di_faccia P (hface 1)
  obtain ⟨l2, hmem2, hmax2⟩ := espositore_di_faccia P (hface 2)
  -- testimoni fuori faccia
  have hw1 : ∃ u ∈ V1, u ∉ F.face 0 := by
    have hne : F.face 0 ≠ (facePolytope P (hface 1)).toSet := by
      intro h
      have ha : faceDim (F.face 0) = 0 := F.dim_eq 0
      have hb : faceDim (F.face 0) = 1 := by
        rw [h, facePolytope_toSet P (hface 1)]
        exact F.dim_eq 1
      omega
    obtain ⟨u, hu, hunf⟩ := exists_vertex_notMem_of_ne_toSet
      (facePolytope P (hface 1))
      (facePolytope_isFace_of P (hface 1) (hface 0) h01) hne
    exact ⟨u, hu, hunf⟩
  have hw2 : ∃ u ∈ V2, u ∉ F.face 1 := by
    have hne : F.face 1 ≠ (facePolytope P (hface 2)).toSet := by
      intro h
      have ha : faceDim (F.face 1) = 1 := F.dim_eq 1
      have hb : faceDim (F.face 1) = 2 := by
        rw [h, facePolytope_toSet P (hface 2)]
        exact F.dim_eq 2
      omega
    obtain ⟨u, hu, hunf⟩ := exists_vertex_notMem_of_ne_toSet
      (facePolytope P (hface 2))
      (facePolytope_isFace_of P (hface 2) (hface 1) h12) hne
    exact ⟨u, hu, hunf⟩
  have hw3 : ∃ u ∈ P.vertices, u ∉ F.face 2 := by
    have hne : F.face 2 ≠ P.toSet := by
      intro h
      have ha : faceDim (F.face 2) = 2 := F.dim_eq 2
      have hb : faceDim (F.face 2) = 3 := by
        show Module.finrank ℝ (vectorSpan ℝ (F.face 2)) = 3
        rw [h]
        exact hfull
      omega
    exact exists_vertex_notMem_of_ne_toSet P (hface 2) hne
  obtain ⟨u1, hu1V, hu1f⟩ := hw1
  obtain ⟨u2, hu2V, hu2f⟩ := hw2
  obtain ⟨u3, hu3V, hu3f⟩ := hw3
  -- le tre strette: l_k (b_{k+1}) < l_k (b0)
  have hs0 : l0 b1 < l0 b0 := media_sotto_il_massimo P hmem0 hmax0
    (hVsub 1) hV1ne hu1V hu1f hb0f
  have hs1 : l1 b2 < l1 b0 := media_sotto_il_massimo P hmem1 hmax1
    (hVsub 2) hV2ne hu2V hu2f (h01 hb0f)
  have hs2 : l2 b3 < l2 b0 := media_sotto_il_massimo P hmem2 hmax2
    hVtop P.vertices_nonempty hu3V hu3f (h02 hb0f)
  -- gli azzeramenti a scala
  have costanza : ∀ {D : Set (E 3)} {lD : E 3 →L[ℝ] ℝ},
      (∀ y ∈ D, y ∈ P.toSet ∧ ∀ z ∈ P.toSet, lD z ≤ lD y) →
      ∀ {y y' : E 3}, y ∈ D → y' ∈ D → lD y = lD y' := by
    intro D lD hmem y y' hy hy'
    exact le_antisymm ((hmem y' hy').2 y (hmem y hy).1)
      ((hmem y hy).2 y' (hmem y' hy').1)
  have hz11 : l1 b1 = l1 b0 := costanza hmem1 hb1f (h01 hb0f)
  have hz21 : l2 b1 = l2 b0 := costanza hmem2 (h12 hb1f) (h02 hb0f)
  have hz22 : l2 b2 = l2 b0 := costanza hmem2 hb2f (h02 hb0f)
  -- la famiglia degli spostamenti
  set M : Fin 3 → E 3 := fun i =>
    if i.val = 0 then b1 - b0 else if i.val = 1 then b2 - b0 else b3 - b0
    with hM
  -- indipendenza lineare a scala
  have hLI : LinearIndependent ℝ M := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsum : c 0 • (b1 - b0) + c 1 • (b2 - b0) + c 2 • (b3 - b0) = 0 := by
      rw [Fin.sum_univ_three] at hc
      exact hc
    -- l2 uccide i primi due e morde il terzo
    have happ2 := congrArg (fun w => l2 w) hsum
    simp only [map_add, map_smul, map_zero, smul_eq_mul] at happ2
    have he1 : l2 (b1 - b0) = 0 := by
      rw [map_sub]
      linarith [hz21]
    have he2 : l2 (b2 - b0) = 0 := by
      rw [map_sub]
      linarith [hz22]
    have he3 : l2 (b3 - b0) < 0 := by
      rw [map_sub]
      linarith [hs2]
    have hc2 : c 2 = 0 := by
      rw [he1, he2] at happ2
      rcases mul_eq_zero.mp (by linarith : c 2 * l2 (b3 - b0) = 0) with h | h
      · exact h
      · exact absurd h (ne_of_lt he3)
    -- l1 uccide il primo e morde il secondo
    have happ1 := congrArg (fun w => l1 w) hsum
    simp only [map_add, map_smul, map_zero, smul_eq_mul] at happ1
    have hf1 : l1 (b1 - b0) = 0 := by
      rw [map_sub]
      linarith [hz11]
    have hf2 : l1 (b2 - b0) < 0 := by
      rw [map_sub]
      linarith [hs1]
    have hc1 : c 1 = 0 := by
      rw [hf1, hc2] at happ1
      simp only [zero_mul, add_zero, zero_add, mul_zero] at happ1
      rcases mul_eq_zero.mp (by linarith : c 1 * l1 (b2 - b0) = 0) with h | h
      · exact h
      · exact absurd h (ne_of_lt hf2)
    -- l0 morde il primo
    have happ0 := congrArg (fun w => l0 w) hsum
    simp only [map_add, map_smul, map_zero, smul_eq_mul] at happ0
    have hg1 : l0 (b1 - b0) < 0 := by
      rw [map_sub]
      linarith [hs0]
    have hc0 : c 0 = 0 := by
      rw [hc1, hc2] at happ0
      simp only [zero_mul, add_zero, mul_zero] at happ0
      rcases mul_eq_zero.mp (by linarith : c 0 * l0 (b1 - b0) = 0) with h | h
      · exact h
      · exact absurd h (ne_of_lt hg1)
    intro i
    rcases i with ⟨iv, hi⟩
    interval_cases iv
    · exact hc0
    · exact hc1
    · exact hc2
  -- lo span degli spostamenti è tutto ℝ³
  have hspan : Submodule.span ℝ (Set.range M) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hLI, Fintype.card_fin, finrank_euclideanSpace]
    simp
  -- σ fissa i quattro baricentri
  have himgk : ∀ k : Fin 3,
      (σ : E 3 → E 3) '' (((facePolytope P (hface k)).vertices : Finset (E 3)) :
        Set (E 3)) = (((facePolytope P (hface k)).vertices : Finset (E 3)) :
        Set (E 3)) := by
    intro k
    have hfil : (((facePolytope P (hface k)).vertices : Finset (E 3)) :
        Set (E 3)) = (P.vertices : Set (E 3)) ∩ F.face k := by
      show ((P.vertices.filter (· ∈ F.face k) : Finset (E 3)) : Set (E 3)) = _
      ext x
      simp [Finset.mem_filter]
    rw [hfil, Set.image_inter σ.injective,
      simmetria_immagine_vertici P hσ, hfix k]
  have hfix0 : σ b0 = b0 := centroide_fisso (himgk 0) hV0ne
  have hfix1 : σ b1 = b1 := centroide_fisso (himgk 1) hV1ne
  have hfix2 : σ b2 = b2 := centroide_fisso (himgk 2) hV2ne
  have hfix3 : σ b3 = b3 :=
    centroide_fisso (simmetria_immagine_vertici P hσ) P.vertices_nonempty
  -- la parte lineare fissa gli spostamenti
  have hcoeA : ∀ x, σ.toAffineEquiv.toAffineMap x = σ x := by
    intro x
    simp
  have hlinfix : ∀ i : Fin 3,
      σ.toAffineEquiv.toAffineMap.linear (M i) = M i := by
    intro i
    have hgen : ∀ b : E 3, σ b = b →
        σ.toAffineEquiv.toAffineMap.linear (b - b0) = b - b0 := by
      intro b hb
      have h1 : σ.toAffineEquiv.toAffineMap.linear (b - b0) = σ b - σ b0 :=
        σ.toAffineEquiv.toAffineMap.linearMap_vsub b b0
      rw [h1, hb, hfix0]
    rcases i with ⟨iv, hi⟩
    interval_cases iv
    · exact hgen b1 hfix1
    · exact hgen b2 hfix2
    · exact hgen b3 hfix3
  -- conclusione: σ fissa ogni punto
  intro z
  have hzmem : z - b0 ∈ Submodule.span ℝ (Set.range M) := by
    rw [hspan]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp hzmem
  have hlin : σ.toAffineEquiv.toAffineMap.linear (z - b0) = z - b0 := by
    rw [← hc]
    rw [map_sum]
    congr 1
    funext i
    rw [map_smul, hlinfix i]
  have h1 : σ.toAffineEquiv.toAffineMap.linear (z - b0) = σ z - σ b0 :=
    σ.toAffineEquiv.toAffineMap.linearMap_vsub z b0
  have h3 : σ z - σ b0 = z - b0 := by
    rw [← h1, hlin]
  rw [hfix0] at h3
  have h6 := congrArg (fun w => w + b0) h3
  simpa using h6

/-- **UNICITÀ DEL TRASPORTATORE**: due simmetrie che trasportano la stessa
bandiera sulla stessa bandiera coincidono. -/
theorem trasportatore_unico (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {σ τ : Isom 3} (hσ : P.isSymmetry σ) (hτ : P.isSymmetry τ)
    (F G : P.Flag)
    (hσF : ∀ k : Fin 3, (σ : E 3 → E 3) '' F.face k = G.face k)
    (hτF : ∀ k : Fin 3, (τ : E 3 → E 3) '' F.face k = G.face k) :
    ∀ z : E 3, σ z = τ z := by
  classical
  -- φ = τ⁻¹ ∘ σ è una simmetria che fissa la bandiera F
  set φ : Isom 3 := σ.trans τ.symm with hφ
  have hφcoe : (φ : E 3 → E 3) = (τ.symm : E 3 → E 3) ∘ (σ : E 3 → E 3) := rfl
  have hτsymm : ∀ s t : Set (E 3), (τ : E 3 → E 3) '' s = t →
      (τ.symm : E 3 → E 3) '' t = s := by
    intro s t h
    rw [← h, ← Set.image_comp]
    have : (τ.symm : E 3 → E 3) ∘ (τ : E 3 → E 3) = id := by
      funext x
      simp
    rw [this, Set.image_id]
  have hφsym : P.isSymmetry φ := by
    show (φ : E 3 → E 3) '' P.toSet = P.toSet
    rw [hφcoe, Set.image_comp]
    rw [hσ]
    exact hτsymm _ _ hτ
  have hφfix : ∀ k : Fin 3, (φ : E 3 → E 3) '' F.face k = F.face k := by
    intro k
    rw [hφcoe, Set.image_comp, hσF k]
    exact hτsymm _ _ (hτF k)
  have hid := simmetria_fissa_bandiera P hfull hφsym F hφfix
  intro z
  have h1 : τ.symm (σ z) = z := hid z
  have h2 := congrArg (fun w => τ w) h1
  simpa using h2

end LeanEval.Geometry.PlatonicClassification
