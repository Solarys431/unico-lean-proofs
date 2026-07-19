import Mathlib
import UnicoProofs.Platonici.SottoPolitopo
import UnicoProofs.Platonici.Diamante
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.Equivarianza
import UnicoProofs.Platonici.DiamanteRelativo
import UnicoProofs.Platonici.Muovi

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Una simmetria del politopo ne permuta l'insieme dei vertici. -/
theorem simmetria_permuta_vertici (P : ConvexPolytope n) {φ : Isom n}
    (hφ : P.isSymmetry φ) :
    (⇑φ) '' (P.vertices : Set (E n)) = (P.vertices : Set (E n)) := by
  rw [P.vertices_eq_extremePoints]
  change (⇑φ.toAffineEquiv) '' Set.extremePoints ℝ P.toSet =
    Set.extremePoints ℝ P.toSet
  rw [← extremePoints_image_affineEquiv φ.toAffineEquiv P.toSet]
  change Set.extremePoints ℝ ((⇑φ) '' P.toSet) =
    Set.extremePoints ℝ P.toSet
  rw [hφ]

open Classical in
/-- Su una faccia fissata, una simmetria permuta i vertici della faccia. -/
theorem simmetria_permuta_vertici_faccia (P : ConvexPolytope n)
    {φ : Isom n} (hφ : P.isSymmetry φ) {f : Set (E n)}
    (hfix : (⇑φ) '' f = f) :
    (⇑φ) '' ((P.vertices.filter (fun x => x ∈ f) : Finset (E n)) : Set (E n)) =
      ((P.vertices.filter (fun x => x ∈ f) : Finset (E n)) : Set (E n)) := by
  classical
  have hV := simmetria_permuta_vertici P hφ
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx ⊢
    refine ⟨?_, ?_⟩
    · have : φ x ∈ (P.vertices : Set (E n)) := by
        rw [← hV]
        exact ⟨x, by exact_mod_cast hx.1, rfl⟩
      exact_mod_cast this
    · rw [← hfix]
      exact ⟨x, hx.2, rfl⟩
  · intro hy
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hy
    have hyV : y ∈ (⇑φ) '' (P.vertices : Set (E n)) := hV.symm ▸ hy.1
    obtain ⟨x, hxV, hxy⟩ := hyV
    have hyf : y ∈ (⇑φ) '' f := hfix.symm ▸ hy.2
    obtain ⟨x', hx'f, hx'y⟩ := hyf
    have hxx' : x = x' := φ.injective (hxy.trans hx'y.symm)
    subst x'
    refine ⟨x, ?_, hxy⟩
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨hxV, hx'f⟩

open Classical in
/-- Il centroide dei vertici di una faccia fissata è un punto fisso. -/
theorem centroide_di_faccia_fissato (P : ConvexPolytope n)
    {φ : Isom n} (hφ : P.isSymmetry φ) {f : Set (E n)}
    (hf : P.IsFace f) (hfix : (⇑φ) '' f = f) :
    φ (Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ f)) id) =
      Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ f)) id := by
  classical
  let s : Finset (E n) := P.vertices.filter (fun x => x ∈ f)
  have hs : s.Nonempty := (facePolytope P hf).vertices_nonempty
  have hw : ∑ i ∈ s, s.centroidWeights ℝ i = 1 :=
    s.sum_centroidWeights_eq_one_of_nonempty ℝ hs
  have hmap :
      φ (s.centroid ℝ id) = s.centroid ℝ (fun x => φ x) := by
    rw [Finset.centroid_def, Finset.centroid_def]
    exact s.map_affineCombination id (s.centroidWeights ℝ) hw
      φ.toAffineEquiv.toAffineMap
  rw [show P.vertices.filter (fun x => x ∈ f) = s from rfl]
  rw [hmap]
  apply Finset.centroid_eq_of_inj_on_of_image_eq ℝ s s
  · intro i _ j _ hij
    exact φ.injective hij
  · intro i _ j _ hij
    exact hij
  · simpa [s] using simmetria_permuta_vertici_faccia P hφ hfix

open Classical in
/-- Il centroide dei vertici di una faccia appartiene alla faccia. -/
theorem centroide_mem_faccia (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) :
    Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ f)) id ∈ f := by
  let s : Finset (E n) := P.vertices.filter (fun x => x ∈ f)
  have hs : s.Nonempty := (facePolytope P hf).vertices_nonempty
  change s.centroid ℝ id ∈ f
  rw [face_eq_hull_vertices P hf]
  exact Finset.centroid_mem_convexHull (R := ℝ) s hs

open Classical in
/-- Il centroide di una faccia non appartiene allo span affine di una
sottofaccia propria. -/
theorem centroide_fuori_da_span_sottofaccia (P : ConvexPolytope n)
    {g f : Set (E n)} (hg : P.IsFace g) (hf : P.IsFace f)
    (hgf : g ⊂ f) :
    Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ f)) id ∉
      affineSpan ℝ g := by
  let s : Finset (E n) := P.vertices.filter (fun x => x ∈ f)
  have hs : s.Nonempty := (facePolytope P hf).vertices_nonempty
  have hgconv : Convex ℝ g := hg.1.convex (convex_convexHull ℝ _)
  have hout : ∃ v ∈ s, v ∉ g := by
    by_contra hall
    push Not at hall
    have hfg : f ⊆ g := by
      rw [face_eq_hull_vertices P hf]
      apply convexHull_min
      · intro v hv
        exact hall v hv
      · exact hgconv
    exact hgf.2 hfg
  obtain ⟨v₀, hv₀s, hv₀g⟩ := hout
  obtain ⟨l, hlg, hchar⟩ := espositore_di_faccia P hg
  obtain ⟨p₀, hp₀g⟩ := hg.2
  let M : ℝ := l p₀
  have hp₀max : ∀ z ∈ P.toSet, l z ≤ M := by
    simpa [M] using (hlg p₀ hp₀g).2
  have hlgval : ∀ z ∈ g, l z = M := by
    intro z hz
    apply le_antisymm
    · exact hp₀max z (hlg z hz).1
    · exact (hlg z hz).2 p₀ (hlg p₀ hp₀g).1
  have hsP : ∀ v ∈ s, v ∈ P.toSet := by
    intro v hv
    have hvV : v ∈ P.vertices := (Finset.mem_filter.mp hv).1
    exact subset_convexHull ℝ _ (by exact_mod_cast hvV)
  have hlstrict : ∀ v ∈ s, v ∉ g → l v < M := by
    intro v hv hvnot
    have hvle := hp₀max v (hsP v hv)
    rcases lt_or_eq_of_le hvle with hlt | heq
    · exact hlt
    · exfalso
      apply hvnot
      apply hchar v (hsP v hv)
      intro z hz
      simpa [heq] using hp₀max z hz
  let c : E n := s.centroid ℝ id
  have hw : ∑ v ∈ s, s.centroidWeights ℝ v = 1 :=
    s.sum_centroidWeights_eq_one_of_nonempty ℝ hs
  have hlc : l c = ∑ v ∈ s, s.centroidWeights ℝ v * l v := by
    change l.toLinearMap.toAffineMap c = _
    rw [show c = s.centroid ℝ id from rfl, Finset.centroid_def]
    rw [s.map_affineCombination id (s.centroidWeights ℝ) hw
      l.toLinearMap.toAffineMap]
    rw [← Finset.centroid_def]
    rw [Finset.centroid_eq_centerMass s hs]
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw]
    simp
  have hwpos : ∀ v, 0 < s.centroidWeights ℝ v := by
    intro v
    simp only [Finset.centroidWeights_apply]
    positivity
  have hsumlt :
      (∑ v ∈ s, s.centroidWeights ℝ v * l v) <
        ∑ v ∈ s, s.centroidWeights ℝ v * M := by
    apply Finset.sum_lt_sum
    · intro v hv
      exact mul_le_mul_of_nonneg_left (hp₀max v (hsP v hv))
        (le_of_lt (hwpos v))
    · exact ⟨v₀, hv₀s, mul_lt_mul_of_pos_left (hlstrict v₀ hv₀s hv₀g)
        (hwpos v₀)⟩
  have hlc_lt : l c < M := by
    calc
      l c = ∑ v ∈ s, s.centroidWeights ℝ v * l v := hlc
      _ < ∑ v ∈ s, s.centroidWeights ℝ v * M := hsumlt
      _ = M := by rw [← Finset.sum_mul, hw, one_mul]
  intro hc
  let A : AffineSubspace ℝ (E n) :=
    AffineSubspace.mk' p₀ (LinearMap.ker l.toLinearMap)
  have hgA : g ⊆ (A : Set (E n)) := by
    intro z hz
    change z - p₀ ∈ LinearMap.ker l.toLinearMap
    rw [LinearMap.mem_ker]
    simp [hlgval z hz, M]
  have hcA : c ∈ A := (affineSpan_le.mpr hgA) hc
  rw [AffineSubspace.mem_mk', LinearMap.mem_ker] at hcA
  have hzero : l c - l p₀ = 0 := by simpa using hcA
  change l c < l p₀ at hlc_lt
  linarith

/-- Criterio triangolare di indipendenza affine per una famiglia finita
ordinata: ogni nuovo punto è fuori dallo span dei precedenti. -/
theorem affineIndependent_fin_of_not_mem_span_lt {m : ℕ}
    (p : Fin m → E n)
    (h : ∀ i, p i ∉ affineSpan ℝ (p '' {j | j < i})) :
    AffineIndependent ℝ p := by
  induction m with
  | zero =>
      exact affineIndependent_of_subsingleton ℝ p
  | succ m ih =>
      apply AffineIndependent.affineIndependent_of_notMem_span
        (i := Fin.last m)
      · let e : {j : Fin (m + 1) // j ≠ Fin.last m} ↪ Fin m :=
          ⟨fun j => Fin.castPred j.1 j.2, by
            intro a b hab
            have hv := congrArg Fin.val hab
            change a.1.val = b.1.val at hv
            exact Subtype.ext (Fin.ext hv)⟩
        have ha : AffineIndependent ℝ (fun j : Fin m => p j.castSucc) := by
          apply ih
          intro i
          have hi := h i.castSucc
          intro hmem
          apply hi
          apply (affineSpan_mono ℝ ?_) hmem
          rintro x ⟨j, hj, rfl⟩
          refine ⟨j.castSucc, ?_, rfl⟩
          exact hj
        have hefun : (fun x : {j : Fin (m + 1) // j ≠ Fin.last m} => p x) =
            (fun j : Fin m => p j.castSucc) ∘ e := by
          funext x
          simp [e, Fin.castSucc_castPred]
        rw [hefun]
        exact ha.comp_embedding e
      · have hlast := h (Fin.last m)
        have hsets :
            p '' {x : Fin (m + 1) | x ≠ Fin.last m} =
              p '' {x : Fin (m + 1) | x < Fin.last m} := by
          congr 1
          ext x
          exact Fin.lt_last_iff_ne_last.symm
        rw [hsets]
        exact hlast

open Classical in
/-- Una simmetria che fissa tutte le facce di una bandiera è l'identità. -/
theorem bandiera_fissata_id (P : ConvexPolytope n) (hfull : P.IsFullDim)
    {φ : Isom n} (hφ : P.isSymmetry φ) (F : P.Flag)
    (hfix : ∀ k : Fin n, (⇑φ) '' F.face k = F.face k) :
    ∀ x : E n, φ x = x := by
  let cf : Fin n → E n := fun k =>
    Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ F.face k)) id
  let ct : E n :=
    Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ P.toSet)) id
  let pts : Fin (n + 1) → E n := Fin.lastCases ct cf
  have hface_mono : ∀ {i j : Fin n}, i ≤ j → F.face i ⊆ F.face j := by
    intro i j hij
    rcases eq_or_lt_of_le hij with heq | hlt
    · subst j
      exact Set.Subset.rfl
    · exact (F.strict_mono i j hlt).1
  have hnotbot : ∀ x : E n, x ∉ (⊥ : AffineSubspace ℝ (E n)) := by
    intro x hx
    have hne : (⊥ : AffineSubspace ℝ (E n)) ≠ ⊥ :=
      (AffineSubspace.nonempty_iff_ne_bot _).mp ⟨x, hx⟩
    exact hne rfl
  have htrans : ∀ i, pts i ∉ affineSpan ℝ (pts '' {j | j < i}) := by
    intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · by_cases hn : n = 0
      · subst n
        have hempty : pts '' {j | j < Fin.last 0} = ∅ := by
          ext x
          simp
        simp only [pts, Fin.lastCases_last]
        rw [hempty, AffineSubspace.span_empty]
        exact hnotbot ct
      · let klast : Fin n := ⟨n - 1, by omega⟩
        have hsubtop : F.face klast ⊆ P.toSet :=
          face_subset_toSet P (F.isFace klast)
        have hproper : F.face klast ⊂ P.toSet := by
          refine ⟨hsubtop, ?_⟩
          intro hrev
          have heq : F.face klast = P.toSet :=
            Set.Subset.antisymm hsubtop hrev
          have hdim := congrArg faceDim heq
          have htopdim : faceDim P.toSet = n := hfull
          rw [F.dim_eq klast, htopdim] at hdim
          change n - 1 = n at hdim
          omega
        have hout := centroide_fuori_da_span_sottofaccia P
          (F.isFace klast) (toSet_isFace P) hproper
        change ct ∉ affineSpan ℝ (F.face klast) at hout
        simp only [pts, Fin.lastCases_last]
        change ct ∉ affineSpan ℝ (pts '' {j | j < Fin.last n})
        intro hc
        apply hout
        apply (affineSpan_mono ℝ ?_) hc
        rintro x ⟨j, hj, rfl⟩
        have hjn : j.val < n := by
          change j.val < n at hj
          exact hj
        let j' : Fin n := ⟨j.val, hjn⟩
        have hj_eq : j = j'.castSucc := by
          apply Fin.ext
          rfl
        rw [hj_eq]
        simp only [pts, Fin.lastCases_castSucc]
        change cf j' ∈ F.face klast
        apply hface_mono
        · change j'.val ≤ klast.val
          dsimp [j', klast]
          omega
        · change Finset.centroid ℝ
              (P.vertices.filter (fun x => x ∈ F.face j')) id ∈ F.face j'
          exact centroide_mem_faccia P (F.isFace j')
    · simp only [pts, Fin.lastCases_castSucc]
      change cf k ∉ affineSpan ℝ (pts '' {j | j < k.castSucc})
      by_cases hk : k.val = 0
      · have hempty : pts '' {j | j < k.castSucc} = ∅ := by
          ext x
          constructor
          · rintro ⟨j, hj, rfl⟩
            have : j.val < k.val := hj
            omega
          · simp
        rw [hempty]
        rw [AffineSubspace.span_empty]
        exact hnotbot (cf k)
      · let km : Fin n := ⟨k.val - 1, by omega⟩
        have hmk : km < k := by
          change k.val - 1 < k.val
          omega
        have hout := centroide_fuori_da_span_sottofaccia P
          (F.isFace km) (F.isFace k) (F.strict_mono km k hmk)
        change cf k ∉ affineSpan ℝ (F.face km) at hout
        intro hc
        apply hout
        apply (affineSpan_mono ℝ ?_) hc
        rintro x ⟨j, hj, rfl⟩
        have hjn : j.val < n := lt_trans hj k.isLt
        let j' : Fin n := ⟨j.val, hjn⟩
        have hj_eq : j = j'.castSucc := by
          apply Fin.ext
          rfl
        have hjk : j'.val < k.val := by
          change j.val < k.val
          exact hj
        rw [hj_eq]
        simp only [pts, Fin.lastCases_castSucc]
        change cf j' ∈ F.face km
        apply hface_mono (i := j') (j := km)
        · have hp : j'.val ≤ k.val.pred := Nat.le_pred_of_lt hjk
          apply Fin.le_iff_val_le_val.mpr
          simpa only [km, Nat.pred_eq_sub_one] using hp
        · change Finset.centroid ℝ
              (P.vertices.filter (fun x => x ∈ F.face j')) id ∈ F.face j'
          exact centroide_mem_faccia P (F.isFace j')
  have hAI : AffineIndependent ℝ pts :=
    affineIndependent_fin_of_not_mem_span_lt pts htrans
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := by
    apply (hAI.affineSpan_eq_top_iff_card_eq_finrank_add_one).2
    simp
  have hcf : ∀ k, φ (cf k) = cf k := by
    intro k
    exact centroide_di_faccia_fissato P hφ (F.isFace k) (hfix k)
  have hct : φ ct = ct := by
    exact centroide_di_faccia_fissato P hφ (toSet_isFace P) hφ
  have hpts : ∀ i, φ (pts i) = pts i := by
    intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simpa only [pts, Fin.lastCases_last] using hct
    · simpa only [pts, Fin.lastCases_castSucc] using hcf k
  have hagree : Set.EqOn (⇑φ.toAffineEquiv)
      (⇑(AffineEquiv.refl ℝ (E n))) (Set.range pts) := by
    rintro x ⟨i, rfl⟩
    simpa using hpts i
  have heq : φ.toAffineEquiv = AffineEquiv.refl ℝ (E n) :=
    AffineEquiv.ext_on hspan φ.toAffineEquiv
      (AffineEquiv.refl ℝ (E n)) hagree
  intro x
  exact DFunLike.congr_fun heq x

end LeanEval.Geometry.PlatonicClassification
