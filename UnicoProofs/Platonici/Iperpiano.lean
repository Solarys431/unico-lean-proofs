import UnicoProofs.Platonici.RelazioniCoxeter

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

theorem simpleReflection_fissa_facce (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) {k : Fin n} (hk : k ≠ i) :
    (⇑(simpleReflection P hreg F i)) '' F.face k = F.face k := by
  have hmap := congrArg (fun G : P.Flag => G.face k)
    (simpleReflection_mapFlag P hreg F i)
  calc
    (⇑(simpleReflection P hreg F i)) '' F.face k =
        (adjacentFlag P hreg.1 F i).face k := by
          simpa only [mapFlag_face] using hmap
    _ = F.face k := (adjacentFlag_isAdjacent P hreg.1 F i).1 k hk

/-- I centroidi delle facce di una bandiera, seguiti dal centroide del
corpo, nell'ordine naturale dei ranghi. -/
noncomputable def centroidiBandieraCorpo (P : ConvexPolytope n) (F : P.Flag) :
    Fin (n + 1) → E n := by
  classical
  exact Fin.lastCases
    (Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ P.toSet)) id)
    (fun k =>
      Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ F.face k)) id)

open Classical in
@[simp] theorem centroidiBandieraCorpo_last (P : ConvexPolytope n) (F : P.Flag) :
    centroidiBandieraCorpo P F (Fin.last n) =
      Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ P.toSet)) id := by
  simp [centroidiBandieraCorpo]

open Classical in
@[simp] theorem centroidiBandieraCorpo_castSucc (P : ConvexPolytope n)
    (F : P.Flag) (k : Fin n) :
    centroidiBandieraCorpo P F k.castSucc =
      Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ F.face k)) id := by
  simp [centroidiBandieraCorpo]

/-- La famiglia completa dei centroidi associata a una bandiera è
affinemente indipendente. -/
theorem centroidiBandieraCorpo_affineIndependent (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) :
    AffineIndependent ℝ (centroidiBandieraCorpo P F) := by
  classical
  let cf : Fin n → E n := fun k =>
    Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ F.face k)) id
  let ct : E n :=
    Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ P.toSet)) id
  let pts : Fin (n + 1) → E n := Fin.lastCases ct cf
  have hpts : pts = centroidiBandieraCorpo P F := by
    rfl
  have hface_mono : ∀ {a b : Fin n}, a ≤ b → F.face a ⊆ F.face b := by
    intro a b hab
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact Set.Subset.rfl
    · exact (F.strict_mono a b hlt).1
  have hnotbot : ∀ x : E n, x ∉ (⊥ : AffineSubspace ℝ (E n)) := by
    intro x hx
    have hne : (⊥ : AffineSubspace ℝ (E n)) ≠ ⊥ :=
      (AffineSubspace.nonempty_iff_ne_bot _).mp ⟨x, hx⟩
    exact hne rfl
  have htrans : ∀ a, pts a ∉ affineSpan ℝ (pts '' {b | b < a}) := by
    intro a
    refine Fin.lastCases ?_ (fun k => ?_) a
    · by_cases hn : n = 0
      · subst n
        have hempty : pts '' {b | b < Fin.last 0} = ∅ := by
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
        change Finset.centroid ℝ
          (P.vertices.filter (fun x => x ∈ P.toSet)) id ∉
            affineSpan ℝ (F.face klast) at hout
        simp only [pts, Fin.lastCases_last]
        change ct ∉ affineSpan ℝ (pts '' {b | b < Fin.last n})
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
        rw [hempty, AffineSubspace.span_empty]
        exact hnotbot (cf k)
      · let km : Fin n := ⟨k.val - 1, by omega⟩
        have hmk : km < k := by
          change k.val - 1 < k.val
          omega
        have hout := centroide_fuori_da_span_sottofaccia P
          (F.isFace km) (F.isFace k) (F.strict_mono km k hmk)
        change Finset.centroid ℝ
          (P.vertices.filter (fun x => x ∈ F.face k)) id ∉
            affineSpan ℝ (F.face km) at hout
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
        apply hface_mono (a := j') (b := km)
        · have hp : j'.val ≤ k.val.pred := Nat.le_pred_of_lt hjk
          apply Fin.le_iff_val_le_val.mpr
          simpa only [km, Nat.pred_eq_sub_one] using hp
        · change Finset.centroid ℝ
              (P.vertices.filter (fun x => x ∈ F.face j')) id ∈ F.face j'
          exact centroide_mem_faccia P (F.isFace j')
  rw [← hpts]
  exact affineIndependent_fin_of_not_mem_span_lt pts htrans

set_option maxHeartbeats 800000 in
theorem centroidi_fissi_indipendenti (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) :
    ∃ p : Fin n → E n, AffineIndependent ℝ p ∧
      ∀ t : Fin n, simpleReflection P hreg F i (p t) = p t := by
  classical
  let q : Fin (n + 1) → E n := centroidiBandieraCorpo P F
  let p : Fin n → E n := fun t => q (i.castSucc.succAbove t)
  have hqAI : AffineIndependent ℝ q := by
    simpa only [q] using centroidiBandieraCorpo_affineIndependent P hreg.1 F
  have hpAI : AffineIndependent ℝ p := by
    change AffineIndependent ℝ
      (fun t => q (i.castSucc.succAboveEmb t))
    exact hqAI.comp_embedding (Fin.succAboveEmb i.castSucc)
  have hsym : P.isSymmetry (simpleReflection P hreg F i) :=
    simpleReflection_isSymmetry P hreg F i
  have hqfix : ∀ j : Fin (n + 1), j ≠ i.castSucc →
      simpleReflection P hreg F i (q j) = q j := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · intro _
      simp only [q, centroidiBandieraCorpo_last]
      exact centroide_di_faccia_fissato P hsym (toSet_isFace P) hsym
    · intro hj
      have hki : k ≠ i := by
        intro h
        subst k
        exact hj rfl
      simp only [q, centroidiBandieraCorpo_castSucc]
      exact centroide_di_faccia_fissato P hsym (F.isFace k)
        (simpleReflection_fissa_facce P hreg F i hki)
  refine ⟨p, hpAI, ?_⟩
  intro t
  exact hqfix (i.castSucc.succAbove t) (Fin.succAbove_ne i.castSucc t)

theorem simpleReflection_iperpiano (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) :
    ∃ H : AffineSubspace ℝ (E n),
      (∀ x, x ∈ H → simpleReflection P hreg F i x = x) ∧
      Module.finrank ℝ H.direction + 1 = n := by
  obtain ⟨p, hpAI, hpfix⟩ := centroidi_fissi_indipendenti P hreg F i
  let H : AffineSubspace ℝ (E n) := affineSpan ℝ (Set.range p)
  haveI : Nonempty (Fin n) := ⟨i⟩
  refine ⟨H, ?_, ?_⟩
  · intro x hx
    have hagree : Set.EqOn
        (⇑(simpleReflection P hreg F i).toAffineEquiv.toAffineMap)
        (⇑(AffineEquiv.refl ℝ (E n)).toAffineMap) (Set.range p) := by
      rintro y ⟨t, rfl⟩
      simpa using hpfix t
    have hext := AffineMap.eqOn_affineSpan (k := ℝ) hagree
    have hh := hext hx
    exact (congrFun (AffineIsometryEquiv.coe_toAffineEquiv
      (simpleReflection P hreg F i)) x).symm.trans
        (hh.trans (by rfl))
  · rw [show H = affineSpan ℝ (Set.range p) from rfl,
      direction_affineSpan ℝ (Set.range p)]
    simpa using hpAI.finrank_vectorSpan_add_one

theorem simpleReflection_fix_eq_hyperplane (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n) :
    ∃ H : AffineSubspace ℝ (E n),
      Module.finrank ℝ H.direction + 1 = n ∧
      (∀ x, simpleReflection P hreg F i x = x ↔ x ∈ H) := by
  obtain ⟨p, hpAI, hpfix⟩ := centroidi_fissi_indipendenti P hreg F i
  let H : AffineSubspace ℝ (E n) := affineSpan ℝ (Set.range p)
  haveI : Nonempty (Fin n) := ⟨i⟩
  have hdim : Module.finrank ℝ H.direction + 1 = n := by
    rw [show H = affineSpan ℝ (Set.range p) from rfl,
      direction_affineSpan ℝ (Set.range p)]
    simpa using hpAI.finrank_vectorSpan_add_one
  refine ⟨H, hdim, fun x => ⟨?_, ?_⟩⟩
  · intro hxfix
    by_contra hxH
    let q : Fin (n + 1) → E n := Fin.lastCases x p
    have hsubAI : AffineIndependent ℝ
        (fun z : {y : Fin (n + 1) // y ≠ Fin.last n} => q z) := by
      rw [← affineIndependent_equiv (finSuccAboveEquiv (Fin.last n))]
      have hfun :
          (fun t : Fin n =>
            (fun z : {y : Fin (n + 1) // y ≠ Fin.last n} => q z)
              (finSuccAboveEquiv (Fin.last n) t)) = p := by
        funext t
        rw [finSuccAboveEquiv_apply]
        change q ((Fin.last n).succAbove t) = p t
        rw [Fin.succAbove_last_apply]
        simp only [q, Fin.lastCases_castSucc]
      change AffineIndependent ℝ
        (fun t : Fin n =>
          (fun z : {y : Fin (n + 1) // y ≠ Fin.last n} => q z)
            (finSuccAboveEquiv (Fin.last n) t))
      rw [hfun]
      exact hpAI
    have himage : q '' {y : Fin (n + 1) | y ≠ Fin.last n} = Set.range p := by
      ext y
      constructor
      · rintro ⟨j, hj, rfl⟩
        let t : Fin n := j.castPred hj
        refine ⟨t, ?_⟩
        have hj_eq : j = t.castSucc := by
          apply Fin.ext
          rfl
        rw [hj_eq]
        simp only [q, Fin.lastCases_castSucc]
      · rintro ⟨t, rfl⟩
        refine ⟨t.castSucc, Fin.ne_of_lt (Fin.castSucc_lt_last t), ?_⟩
        simp only [q, Fin.lastCases_castSucc]
    have hqAI : AffineIndependent ℝ q := by
      apply hsubAI.affineIndependent_of_notMem_span (i := Fin.last n)
      simp only [q, Fin.lastCases_last]
      rw [himage]
      exact hxH
    have hqfix : ∀ j : Fin (n + 1),
        simpleReflection P hreg F i (q j) = q j := by
      intro j
      refine Fin.lastCases ?_ (fun t => ?_) j
      · simpa only [q, Fin.lastCases_last] using hxfix
      · simpa only [q, Fin.lastCases_castSucc] using hpfix t
    have hspan : affineSpan ℝ (Set.range q) = ⊤ := by
      apply (hqAI.affineSpan_eq_top_iff_card_eq_finrank_add_one).2
      simp
    have hagree : Set.EqOn (⇑(simpleReflection P hreg F i).toAffineEquiv)
        (⇑(AffineEquiv.refl ℝ (E n))) (Set.range q) := by
      rintro y ⟨j, rfl⟩
      simpa using hqfix j
    have heq : (simpleReflection P hreg F i).toAffineEquiv =
        AffineEquiv.refl ℝ (E n) :=
      AffineEquiv.ext_on hspan (simpleReflection P hreg F i).toAffineEquiv
        (AffineEquiv.refl ℝ (E n)) hagree
    apply simpleReflection_ne_id P hreg F i
    intro y
    exact DFunLike.congr_fun heq y
  · intro hxH
    have hagree : Set.EqOn
        (⇑(simpleReflection P hreg F i).toAffineEquiv.toAffineMap)
        (⇑(AffineEquiv.refl ℝ (E n)).toAffineMap) (Set.range p) := by
      rintro y ⟨t, rfl⟩
      simpa using hpfix t
    have hext := AffineMap.eqOn_affineSpan (k := ℝ) hagree
    have hh := hext hxH
    exact (congrFun (AffineIsometryEquiv.coe_toAffineEquiv
      (simpleReflection P hreg F i)) x).symm.trans
        (hh.trans (by rfl))

end LeanEval.Geometry.PlatonicClassification
