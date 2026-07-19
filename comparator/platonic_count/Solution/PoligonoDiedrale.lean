import Solution.PoligonoRegolare
import Solution.ConoVertice

open Set Metric

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

set_option maxHeartbeats 200000

theorem E2_ext {u v : E2} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  ext i
  fin_cases i
  exact h0
  exact h1

def rotFormula (theta : Real) (z : E2) : E2 :=
  WithLp.toLp 2 ![
    Real.cos theta * z 0 - Real.sin theta * z 1,
    Real.sin theta * z 0 + Real.cos theta * z 1]

def rotLinearMap (theta : Real) : LinearMap (RingHom.id Real) E2 E2 where
  toFun := rotFormula theta
  map_add' u v := by
    apply E2_ext <;> simp [rotFormula] <;> ring
  map_smul' c u := by
    apply E2_ext <;> simp [rotFormula] <;> ring

def rotLinearIsometry (theta : Real) :
    LinearIsometry (RingHom.id Real) E2 E2 where
  toLinearMap := rotLinearMap theta
  norm_map' z := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Real.norm_eq_abs, sq_abs]
    change
      (Real.cos theta * z 0 - Real.sin theta * z 1) ^ 2 +
          (Real.sin theta * z 0 + Real.cos theta * z 1) ^ 2 =
        z 0 ^ 2 + z 1 ^ 2
    nlinarith [Real.sin_sq_add_cos_sq theta]

def rotLinear (theta : Real) :
    LinearIsometryEquiv (RingHom.id Real) E2 E2 :=
  (rotLinearIsometry theta).toLinearIsometryEquiv rfl

def rotIsom (theta : Real) : Isom 2 :=
  (rotLinear theta).toAffineIsometryEquiv

@[simp] theorem rotIsom_apply (theta : Real) (z : E2) :
    rotIsom theta z = rotFormula theta z := by
  change rotLinear theta z = rotFormula theta z
  rw [rotLinear, LinearIsometry.toLinearIsometryEquiv_apply]
  rfl

theorem poligonoAngolo_add {n : Nat} (hn : Not (n = 0)) (k j : Fin n) :
    poligonoAngolo n (k + j) =
        poligonoAngolo n k + poligonoAngolo n j \/
      poligonoAngolo n (k + j) =
        poligonoAngolo n k + poligonoAngolo n j - 2 * Real.pi := by
  have hnR : Not ((n : Real) = 0) := by exact_mod_cast hn
  by_cases hwrap : n <= k.val + j.val
  case pos =>
    right
    unfold poligonoAngolo
    rw [Fin.val_add_eq_ite, if_pos hwrap]
    push_cast [Nat.cast_sub hwrap]
    field_simp
  case neg =>
    left
    unfold poligonoAngolo
    rw [Fin.val_add_eq_ite, if_neg hwrap]
    push_cast
    field_simp

theorem rotIsom_vertex_add {n : Nat} (hn : Not (n = 0)) (j k : Fin n) :
    rotIsom (poligonoAngolo n j) (poligonoVertice n k) =
      poligonoVertice n (k + j) := by
  apply E2_ext
  all_goals simp only [rotIsom_apply, rotFormula, poligonoVertice,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals rcases poligonoAngolo_add hn k j with h | h
  all_goals rw [h]
  all_goals simp [Real.cos_add, Real.sin_add, Real.cos_sub_two_pi,
    Real.sin_sub_two_pi]
  all_goals ring

def reflFormula (z : E2) : E2 :=
  WithLp.toLp 2 ![z 0, -z 1]

def reflLinearMap : LinearMap (RingHom.id Real) E2 E2 where
  toFun := reflFormula
  map_add' u v := by
    apply E2_ext <;> simp [reflFormula] <;> ring
  map_smul' c u := by
    apply E2_ext <;> simp [reflFormula]

def reflLinearIsometry : LinearIsometry (RingHom.id Real) E2 E2 where
  toLinearMap := reflLinearMap
  norm_map' z := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Real.norm_eq_abs, sq_abs]
    change z 0 ^ 2 + (-z 1) ^ 2 = z 0 ^ 2 + z 1 ^ 2
    ring

def reflLinear : LinearIsometryEquiv (RingHom.id Real) E2 E2 :=
  reflLinearIsometry.toLinearIsometryEquiv rfl

def refl2 : Isom 2 := reflLinear.toAffineIsometryEquiv

@[simp] theorem refl2_apply (z : E2) : refl2 z = reflFormula z := by
  change reflLinear z = reflFormula z
  rw [reflLinear, LinearIsometry.toLinearIsometryEquiv_apply]
  rfl

theorem poligonoAngolo_neg {n : Nat} (hn : Not (n = 0)) (k : Fin n) :
    poligonoAngolo n (-k) = -poligonoAngolo n k \/
      poligonoAngolo n (-k) = 2 * Real.pi - poligonoAngolo n k := by
  letI : NeZero n := { out := hn }
  have hnR : Not ((n : Real) = 0) := by exact_mod_cast hn
  by_cases hk : k = 0
  case pos =>
    left
    subst k
    simp [poligonoAngolo]
  case neg =>
    right
    have hkpos : 0 < k.val := Nat.pos_of_ne_zero (by
      intro h
      apply hk
      exact Fin.ext h)
    have hsub : n - k.val < n := Nat.sub_lt (Nat.pos_of_ne_zero hn) hkpos
    unfold poligonoAngolo
    rw [Fin.val_neg', Nat.mod_eq_of_lt hsub]
    push_cast [Nat.cast_sub (Nat.le_of_lt k.isLt)]
    field_simp

theorem refl2_vertex_neg {n : Nat} (hn : Not (n = 0)) (k : Fin n) :
    refl2 (poligonoVertice n k) = poligonoVertice n (-k) := by
  apply E2_ext
  all_goals simp only [refl2_apply, reflFormula, poligonoVertice,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals rcases poligonoAngolo_neg hn k with h | h
  all_goals rw [h]
  all_goals simp [Real.cos_sub, Real.sin_sub]

theorem verticiPoligono_eq_range {n : Nat} (hn : Not (n = 0)) :
    (verticiPoligono n : Set E2) = Set.range (poligonoVertice n) := by
  ext x
  simp [verticiPoligono, hn]

theorem affineIsom_image_convexHull (g : Isom 2) (S : Set E2) :
    (g : E2 -> E2) '' convexHull Real S =
      convexHull Real ((g : E2 -> E2) '' S) := by
  simpa only [AffineEquiv.coe_toAffineMap, AffineIsometryEquiv.coe_toAffineEquiv] using
    g.toAffineEquiv.toAffineMap.image_convexHull S

theorem rotIsom_image_vertices {n : Nat} (hn : Not (n = 0)) (j : Fin n) :
    (rotIsom (poligonoAngolo n j) : E2 -> E2) ''
        (verticiPoligono n : Set E2) =
      (verticiPoligono n : Set E2) := by
  letI : NeZero n := { out := hn }
  rw [verticiPoligono_eq_range hn]
  ext x
  constructor
  case mp =>
    intro hx
    cases hx with
    | intro y hy =>
      cases hy with
      | intro hyr hyx =>
        cases hyr with
        | intro k hk =>
          subst y
          subst x
          rw [rotIsom_vertex_add hn]
          exact Set.mem_range_self (k + j)
  case mpr =>
    intro hx
    cases hx with
    | intro k hk =>
      subst x
      refine Exists.intro (poligonoVertice n (k - j)) ?_
      exact And.intro (Set.mem_range_self _) (by
        rw [rotIsom_vertex_add hn]
        have hkj : k - j + j = k := sub_add_cancel k j
        rw [hkj])

theorem refl2_image_vertices {n : Nat} (hn : Not (n = 0)) :
    (refl2 : E2 -> E2) '' (verticiPoligono n : Set E2) =
      (verticiPoligono n : Set E2) := by
  letI : NeZero n := { out := hn }
  rw [verticiPoligono_eq_range hn]
  ext x
  constructor
  case mp =>
    intro hx
    cases hx with
    | intro y hy =>
      cases hy with
      | intro hyr hyx =>
        cases hyr with
        | intro k hk =>
          subst y
          subst x
          rw [refl2_vertex_neg hn]
          exact Set.mem_range_self (-k)
  case mpr =>
    intro hx
    cases hx with
    | intro k hk =>
      subst x
      refine Exists.intro (poligonoVertice n (-k)) ?_
      exact And.intro (Set.mem_range_self _) (by
        rw [refl2_vertex_neg hn, neg_neg])

theorem rotIsom_symmetry {n : Nat} (hn : Not (n = 0)) (j : Fin n) :
    (poligono n).isSymmetry (rotIsom (poligonoAngolo n j)) := by
  change (rotIsom (poligonoAngolo n j) : E2 -> E2) ''
      convexHull Real (verticiPoligono n : Set E2) =
    convexHull Real (verticiPoligono n : Set E2)
  rw [affineIsom_image_convexHull, rotIsom_image_vertices hn]

theorem refl2_symmetry {n : Nat} (hn : Not (n = 0)) :
    (poligono n).isSymmetry refl2 := by
  change (refl2 : E2 -> E2) '' convexHull Real (verticiPoligono n : Set E2) =
    convexHull Real (verticiPoligono n : Set E2)
  rw [affineIsom_image_convexHull, refl2_image_vertices hn]

theorem zeroFace_is_vertex2 {P : ConvexPolytope 2} {F : Set E2}
    (hF : P.IsFace F) (hd : faceDim F = 0) :
    Exists fun v : E2 => And (F = {v}) (Membership.mem P.vertices v) := by
  cases hF.2 with
  | intro v hv =>
    have hspan : vectorSpan Real F = (Bot.bot : Submodule Real E2) := by
      apply Submodule.finrank_eq_zero.mp
      exact hd
    have hsingle : F = {v} := by
      apply Set.Subset.antisymm
      next =>
        intro x hx
        have hxv := vsub_mem_vectorSpan Real hx hv
        rw [hspan] at hxv
        have hzero : x - v = 0 := by simpa using hxv
        have hxvEq : x = v := sub_eq_zero.mp hzero
        simpa using hxvEq
      next => exact Set.singleton_subset_iff.mpr hv
    refine Exists.intro v (And.intro hsingle ?_)
    have hexposed : IsExposed Real P.toSet ({v} : Set E2) := by
      rw [hsingle.symm]
      exact hF.1
    have hvext : Membership.mem (P.toSet.extremePoints Real) v :=
      hexposed.isExtreme.mem_extremePoints
    rw [ConvexPolytope.toSet] at hvext
    apply Finset.mem_coe.mp
    rw [P.vertices_eq_extremePoints]
    exact hvext

structure PolygonFlagData (n : Nat) (F : (poligono n).Flag) where
  i : Fin n
  j : Fin n
  index_ne : Not (i = j)
  face_zero : F.face 0 = {poligonoVertice n i}
  face_one : F.face 1 = segment Real
    (poligonoVertice n i) (poligonoVertice n j)

theorem polygon_flag_data (n : Nat) (hn : 3 <= n)
    (F : (poligono n).Flag) : Nonempty (PolygonFlagData n F) := by
  have hn0 : Not (n = 0) := by omega
  have hz := zeroFace_is_vertex2 (F.isFace 0) (F.dim_eq 0)
  cases hz with
  | intro w hw =>
    have hw1 : Membership.mem (F.face 1) w := by
      apply (F.strict_mono 0 1 (by decide)).1
      rw [hw.1]
      exact Set.mem_singleton w
    have hsp := spigolo_segmento (poligono n) (F.isFace 1) (F.dim_eq 1)
      hw.2 hw1
    cases hsp with
    | intro a ha =>
      have hwi : Membership.mem (verticiPoligono n : Set E2) w :=
        Finset.mem_coe.mpr hw.2
      rw [verticiPoligono_eq_range hn0] at hwi
      cases hwi with
      | intro i hi =>
        have haj : Membership.mem (verticiPoligono n : Set E2) a :=
          Finset.mem_coe.mpr ha.1
        rw [verticiPoligono_eq_range hn0] at haj
        cases haj with
        | intro j hj =>
          have hij : Not (i = j) := by
            intro hij
            apply ha.2.2.1
            subst j
            exact hj.symm.trans hi
          refine Nonempty.intro {
            i := i
            j := j
            index_ne := hij
            face_zero := ?_
            face_one := ?_ }
          next =>
            rw [hi]
            exact hw.1
          next =>
            rw [hi, hj]
            exact ha.2.2.2

theorem isExposed_image_isom2 (g : Isom 2) {A B : Set E2}
    (h : IsExposed Real A B) :
    IsExposed Real ((g : E2 -> E2) '' A) ((g : E2 -> E2) '' B) := by
  intro hne
  cases hne with
  | intro b hbB =>
    cases hbB with
    | intro a ha =>
      have haB := ha.1
      have hab := ha.2
      cases h (Exists.intro a haB) with
      | intro l hl =>
        let l' : StrongDual Real E2 :=
          l.comp g.symm.linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
        have hl' (x : E2) : l' (g x) = l x - l (g.symm 0) := by
          have hm := g.symm.map_vsub (g x) 0
          have hm' : g.symm.linearIsometryEquiv (g x) = x - g.symm 0 := by
            simpa using hm
          simp only [l', ContinuousLinearMap.comp_apply]
          change l (g.symm.linearIsometryEquiv (g x)) = _
          rw [hm', map_sub]
        refine Exists.intro l' (Set.ext ?_)
        intro x
        constructor
        case mp =>
          intro hx
          cases hx with
          | intro b hb =>
            have hbmem := hb.1
            have hbx := hb.2
            subst x
            rw [hl] at hbmem
            constructor
            case left =>
              exact Exists.intro b (And.intro hbmem.1 rfl)
            case right =>
              intro z hz
              cases hz with
              | intro y hy =>
                have hyA := hy.1
                have hyz := hy.2
                subst z
                rw [hl' y, hl' b]
                exact sub_le_sub_right (hbmem.2 y hyA) _
        case mpr =>
          intro hx
          have hxA := hx.1
          have hxmax := hx.2
          cases hxA with
          | intro a ha =>
            have haA := ha.1
            have hax := ha.2
            subst x
            refine Exists.intro a (And.intro ?_ rfl)
            rw [hl]
            constructor
            case left => exact haA
            case right =>
              intro y hy
              have hle := hxmax (g y) (Exists.intro y (And.intro hy rfl))
              rw [hl' y, hl' a] at hle
              linarith

theorem isFace_image_isom2 {P : ConvexPolytope 2} (g : Isom 2)
    (hg : P.isSymmetry g) {F : Set E2} (hF : P.IsFace F) :
    P.IsFace ((g : E2 -> E2) '' F) := by
  constructor
  case left =>
    rw [show P.toSet = (g : E2 -> E2) '' P.toSet by exact hg.symm]
    exact isExposed_image_isom2 g hF.1
  case right =>
    exact hF.2.image _

theorem symmetry_trans2 {P : ConvexPolytope 2} {g h : Isom 2}
    (hg : P.isSymmetry g) (hh : P.isSymmetry h) :
    P.isSymmetry (g.trans h) := by
  unfold ConvexPolytope.isSymmetry at *
  calc
    ((g.trans h : Isom 2) : E2 -> E2) '' P.toSet =
        (h : E2 -> E2) '' ((g : E2 -> E2) '' P.toSet) := by
      rw [Set.image_image]
      rfl
    _ = P.toSet := by rw [hg, hh]

def dihIsom (n : Nat) (j : Fin n) : Isom 2 :=
  refl2.trans (rotIsom (poligonoAngolo n j))

theorem dihIsom_vertex {n : Nat} (hn : Not (n = 0)) (j k : Fin n) :
    dihIsom n j (poligonoVertice n k) =
      poligonoVertice n (-k + j) := by
  letI : NeZero n := { out := hn }
  change rotIsom (poligonoAngolo n j)
      (refl2 (poligonoVertice n k)) = _
  rw [refl2_vertex_neg hn, rotIsom_vertex_add hn]

theorem dihIsom_symmetry {n : Nat} (hn : Not (n = 0)) (j : Fin n) :
    (poligono n).isSymmetry (dihIsom n j) := by
  exact symmetry_trans2 (refl2_symmetry hn) (rotIsom_symmetry hn j)

theorem isom_image_singleton (g : Isom 2) (a : E2) :
    (g : E2 -> E2) '' ({a} : Set E2) = {g a} := by
  ext x
  simp

theorem isom_image_segment (g : Isom 2) (a b : E2) :
    (g : E2 -> E2) '' segment Real a b = segment Real (g a) (g b) := by
  simpa only [AffineEquiv.coe_toAffineMap, AffineIsometryEquiv.coe_toAffineEquiv] using
    image_segment Real g.toAffineEquiv.toAffineMap a b

theorem vertex_mem_extremePoints2 {P : ConvexPolytope 2} {v : E2}
    (hv : Membership.mem P.vertices v) :
    Membership.mem (P.toSet.extremePoints Real) v := by
  have hv' : Membership.mem (P.vertices : Set E2) v := Finset.mem_coe.mpr hv
  rw [P.vertices_eq_extremePoints] at hv'
  exact hv'

theorem segment_other_endpoint_eq {P : ConvexPolytope 2} {a b c : E2}
    (ha : Membership.mem P.vertices a) (hb : Membership.mem P.vertices b)
    (hc : Membership.mem P.vertices c) (hca : Not (c = a))
    (hseg : segment Real a b = segment Real a c) : b = c := by
  have hcmem : Membership.mem (segment Real a b) c := by
    rw [hseg]
    exact right_mem_segment Real a c
  have hext := vertex_mem_extremePoints2 hc
  have haT : Membership.mem P.toSet a := subset_convexHull Real _
    (Finset.mem_coe.mpr ha)
  have hbT : Membership.mem P.toSet b := subset_convexHull Real _
    (Finset.mem_coe.mpr hb)
  have hend := (mem_extremePoints_iff_forall_segment.mp hext).2
    a haT b hbT hcmem
  cases hend with
  | inl hac => exact False.elim (hca hac.symm)
  | inr hbc => exact hbc

theorem fin_eq_of_double_eq_zero {n : Nat} [NeZero n] (x y : Fin n)
    (hx : x + x = 0) (hy : y + y = 0)
    (hx0 : Not (x = 0)) (hy0 : Not (y = 0)) : x = y := by
  have hval (z : Fin n) (hz : z + z = 0) (hz0 : Not (z = 0)) :
      z.val + z.val = n := by
    have hzv0 : (z + z).val = 0 := congrArg Fin.val hz
    have hzv : (if n <= z.val + z.val then z.val + z.val - n
        else z.val + z.val) = 0 :=
      (Fin.val_add_eq_ite z z).symm.trans hzv0
    by_cases hwrap : n <= z.val + z.val
    case pos =>
      rw [if_pos hwrap] at hzv
      omega
    case neg =>
      rw [if_neg hwrap] at hzv
      exfalso
      apply hz0
      apply Fin.ext
      omega
  apply Fin.ext
  have hxv := hval x hx hx0
  have hyv := hval y hy hy0
  omega

def reflIndex {n : Nat} (c k : Fin n) : Fin n :=
  -k + (c + c)

theorem reflIndex_center {n : Nat} [NeZero n] (c : Fin n) :
    reflIndex c c = c := by
  unfold reflIndex
  abel

theorem reflIndex_involutive {n : Nat} [NeZero n] (c k : Fin n) :
    reflIndex c (reflIndex c k) = k := by
  unfold reflIndex
  abel

def centerRefl (n : Nat) (c : Fin n) : Isom 2 :=
  dihIsom n (c + c)

theorem centerRefl_vertex {n : Nat} (hn : Not (n = 0)) (c k : Fin n) :
    centerRefl n c (poligonoVertice n k) =
      poligonoVertice n (reflIndex c k) := by
  letI : NeZero n := { out := hn }
  exact dihIsom_vertex hn (c + c) k

theorem centerRefl_symmetry {n : Nat} (hn : Not (n = 0)) (c : Fin n) :
    (poligono n).isSymmetry (centerRefl n c) :=
  dihIsom_symmetry hn (c + c)

theorem faceDim_segment_eq_one {a b : E2} (hab : Not (a = b)) :
    faceDim (segment Real a b) = 1 := by
  unfold faceDim
  rw [vectorSpan_segment]
  apply finrank_span_singleton
  exact vsub_ne_zero.mpr (Ne.symm hab)

theorem centerRefl_moves_edge (n : Nat) (hn : 3 <= n) (c d : Fin n)
    (hcd : Not (c = d))
    (he : (poligono n).IsFace
      (segment Real (poligonoVertice n c) (poligonoVertice n d))) :
    Not ((centerRefl n c : E2 -> E2) ''
      segment Real (poligonoVertice n c) (poligonoVertice n d) =
      segment Real (poligonoVertice n c) (poligonoVertice n d)) := by
  have hn0 : Not (n = 0) := by omega
  letI : NeZero n := { out := hn0 }
  intro hedgeFixed
  have hinj := poligonoVertice_injective hn0
  have hcV : Membership.mem (poligono n).vertices (poligonoVertice n c) := by
    change Membership.mem (verticiPoligono n) (poligonoVertice n c)
    simp [verticiPoligono, hn0]
  have hdV : Membership.mem (poligono n).vertices (poligonoVertice n d) := by
    change Membership.mem (verticiPoligono n) (poligonoVertice n d)
    simp [verticiPoligono, hn0]
  have hcdV : Not (poligonoVertice n c = poligonoVertice n d) :=
    hinj.ne hcd
  have hedim : faceDim
      (segment Real (poligonoVertice n c) (poligonoVertice n d)) = 1 :=
    faceDim_segment_eq_one hcdV
  have hdim : Module.finrank Real (vectorSpan Real (poligono n).toSet) = 2 :=
    poligono_isFullDim n hn
  have hrd : reflIndex c d = d := by
    have hseg := hedgeFixed
    rw [isom_image_segment, centerRefl_vertex hn0,
      centerRefl_vertex hn0, reflIndex_center] at hseg
    apply hinj
    exact segment_other_endpoint_eq hcV
      (by
        change Membership.mem (verticiPoligono n)
          (poligonoVertice n (reflIndex c d))
        simp [verticiPoligono, hn0]) hdV (hinj.ne (Ne.symm hcd)) hseg
  have hs := secondo_spigolo (poligono n) hdim hcV he hedim
    (left_mem_segment Real (poligonoVertice n c) (poligonoVertice n d))
  cases hs with
  | intro q hq =>
    have hsq := spigolo_segmento (poligono n) hq.1 hq.2.1 hcV hq.2.2.1
    cases hsq with
    | intro a ha =>
      have haSet : Membership.mem (verticiPoligono n : Set E2) a :=
        Finset.mem_coe.mpr ha.1
      rw [verticiPoligono_eq_range hn0] at haSet
      cases haSet with
      | intro k hk =>
        have hck : Not (c = k) := by
          intro h
          apply ha.2.2.1
          subst k
          exact hk.symm
        have hkV : Membership.mem (poligono n).vertices (poligonoVertice n k) := by
          change Membership.mem (verticiPoligono n) (poligonoVertice n k)
          simp [verticiPoligono, hn0]
        have hqseg : q = segment Real (poligonoVertice n c)
            (poligonoVertice n k) := by
          rw [hk, ha.2.2.2]
        let qi : Set E2 := (centerRefl n c : E2 -> E2) '' q
        have hqiFace : (poligono n).IsFace qi :=
          isFace_image_isom2 (centerRefl n c) (centerRefl_symmetry hn0 c) hq.1
        have hqiSeg : qi = segment Real (poligonoVertice n c)
            (poligonoVertice n (reflIndex c k)) := by
          dsimp [qi]
          rw [hqseg, isom_image_segment, centerRefl_vertex hn0,
            centerRefl_vertex hn0, reflIndex_center]
        have hqiDim : faceDim qi = 1 := by
          rw [hqiSeg]
          apply faceDim_segment_eq_one
          exact hinj.ne (by
            intro h
            apply hck
            have hh := congrArg (reflIndex c) h
            rw [reflIndex_center, reflIndex_involutive] at hh
            exact hh)
        have hcqi : Membership.mem qi (poligonoVertice n c) := by
          rw [hqiSeg]
          exact left_mem_segment Real _ _
        have hcases : Or (qi = segment Real (poligonoVertice n c)
              (poligonoVertice n d)) (qi = q) := by
          by_cases hqie : qi = segment Real (poligonoVertice n c)
              (poligonoVertice n d)
          case pos => exact Or.inl hqie
          case neg =>
            by_cases hqiq : qi = q
            case pos => exact Or.inr hqiq
            case neg =>
              exfalso
              exact diamante_poligono (poligono n) hdim he hedim hq.1 hq.2.1
                hqiFace hqiDim (Ne.symm hq.2.2.2) (Ne.symm hqie)
                (Ne.symm hqiq)
                (left_mem_segment Real _ _) hq.2.2.1 hcqi
        cases hcases with
        | inl hqie =>
          have hrkd : reflIndex c k = d := by
            apply hinj
            rw [hqiSeg] at hqie
            exact segment_other_endpoint_eq hcV
              (by
                change Membership.mem (verticiPoligono n)
                  (poligonoVertice n (reflIndex c k))
                simp [verticiPoligono, hn0]) hdV (hinj.ne (Ne.symm hcd)) hqie
          have hkd : k = d := by
            have hh := congrArg (reflIndex c) hrkd
            rw [reflIndex_involutive, hrd] at hh
            exact hh
          apply hq.2.2.2
          rw [hqseg, hkd]
        | inr hqiq =>
          have hrkk : reflIndex c k = k := by
            apply hinj
            rw [hqiSeg, hqseg] at hqiq
            exact segment_other_endpoint_eq hcV
              (by
                change Membership.mem (verticiPoligono n)
                  (poligonoVertice n (reflIndex c k))
                simp [verticiPoligono, hn0]) hkV (hinj.ne (Ne.symm hck)) hqiq
          have hd2 : (d - c) + (d - c) = 0 := by
            calc
              (d - c) + (d - c) = d - reflIndex c d := by
                unfold reflIndex
                abel
              _ = 0 := by rw [hrd]; abel
          have hk2 : (k - c) + (k - c) = 0 := by
            calc
              (k - c) + (k - c) = k - reflIndex c k := by
                unfold reflIndex
                abel
              _ = 0 := by rw [hrkk]; abel
          have hdc0 : Not (d - c = 0) := by
            intro h
            apply hcd
            exact (sub_eq_zero.mp h).symm
          have hkc0 : Not (k - c = 0) := by
            intro h
            apply hck
            exact (sub_eq_zero.mp h).symm
          have hdkSub := fin_eq_of_double_eq_zero (d - c) (k - c)
            hd2 hk2 hdc0 hkc0
          have hdk : d = k := by
            exact sub_left_injective hdkSub
          apply hq.2.2.2
          rw [hqseg, hdk]

theorem poligono_isRegular (n : Nat) (hn : 3 <= n) :
    (poligono n).IsRegular := by
  constructor
  next => exact poligono_isFullDim n hn
  next =>
    intro F G
    let f := (polygon_flag_data n hn F).some
    let g := (polygon_flag_data n hn G).some
    have hn0 : Not (n = 0) := by omega
    letI : NeZero n := { out := hn0 }
    let s : Fin n := g.i - f.i
    have hfi : f.i + s = g.i := by
      dsimp [s]
      abel
    have hgp : Not (g.i = f.j + s) := by
      intro h
      apply f.index_ne
      have heq : f.i + s = f.j + s := hfi.trans h
      exact add_right_cancel heq
    let eplus : Set E2 := segment Real (poligonoVertice n g.i)
      (poligonoVertice n (f.j + s))
    let eminus : Set E2 := segment Real (poligonoVertice n g.i)
      (poligonoVertice n (reflIndex g.i (f.j + s)))
    let gedge : Set E2 := segment Real (poligonoVertice n g.i)
      (poligonoVertice n g.j)
    have hrot : (poligono n).isSymmetry
        (rotIsom (poligonoAngolo n s)) := rotIsom_symmetry hn0 s
    have heplus : (poligono n).IsFace eplus := by
      have h := isFace_image_isom2 (rotIsom (poligonoAngolo n s))
        hrot (F.isFace 1)
      rw [f.face_one, isom_image_segment, rotIsom_vertex_add hn0,
        rotIsom_vertex_add hn0, hfi] at h
      exact h
    have heminus : (poligono n).IsFace eminus := by
      have h := isFace_image_isom2 (centerRefl n g.i)
        (centerRefl_symmetry hn0 g.i) heplus
      dsimp [eplus] at h
      rw [isom_image_segment, centerRefl_vertex hn0,
        centerRefl_vertex hn0, reflIndex_center] at h
      exact h
    have hgedge : (poligono n).IsFace gedge := by
      have h := G.isFace 1
      rw [g.face_one] at h
      exact h
    have hplusDim : faceDim eplus = 1 := by
      dsimp [eplus]
      apply faceDim_segment_eq_one
      exact (poligonoVertice_injective hn0).ne hgp
    have hminusIndex : Not (g.i = reflIndex g.i (f.j + s)) := by
      intro h
      apply hgp
      have hh := congrArg (reflIndex g.i) h
      rw [reflIndex_center, reflIndex_involutive] at hh
      exact hh
    have hminusDim : faceDim eminus = 1 := by
      dsimp [eminus]
      apply faceDim_segment_eq_one
      exact (poligonoVertice_injective hn0).ne hminusIndex
    have hgedgeDim : faceDim gedge = 1 := by
      dsimp [gedge]
      rw [g.face_one.symm]
      exact G.dim_eq 1
    have hplusMinus : Not (eplus = eminus) := by
      have hmove := centerRefl_moves_edge n hn g.i (f.j + s) hgp heplus
      rw [isom_image_segment, centerRefl_vertex hn0,
        centerRefl_vertex hn0, reflIndex_center] at hmove
      exact Ne.symm hmove
    have hgiPlus : Membership.mem eplus (poligonoVertice n g.i) := by
      dsimp [eplus]
      exact left_mem_segment Real _ _
    have hgiMinus : Membership.mem eminus (poligonoVertice n g.i) := by
      dsimp [eminus]
      exact left_mem_segment Real _ _
    have hgiG : Membership.mem gedge (poligonoVertice n g.i) := by
      dsimp [gedge]
      exact left_mem_segment Real _ _
    have hedgeCases : Or (gedge = eplus) (gedge = eminus) := by
      by_cases hgeP : gedge = eplus
      case pos => exact Or.inl hgeP
      case neg =>
        by_cases hgeM : gedge = eminus
        case pos => exact Or.inr hgeM
        case neg =>
          exfalso
          have hdim : Module.finrank Real
              (vectorSpan Real (poligono n).toSet) = 2 :=
            poligono_isFullDim n hn
          exact diamante_poligono (poligono n) hdim heplus hplusDim
            heminus hminusDim hgedge hgedgeDim hplusMinus
            (Ne.symm hgeP) (Ne.symm hgeM) hgiPlus hgiMinus hgiG
    cases hedgeCases with
    | inl hgeP =>
      refine Exists.intro (rotIsom (poligonoAngolo n s))
        (And.intro hrot ?_)
      intro k
      have hk : Or (k = 0) (k = 1) := by omega
      cases hk with
      | inl hk0 =>
        subst k
        rw [f.face_zero, g.face_zero, isom_image_singleton,
          rotIsom_vertex_add hn0, hfi]
      | inr hk1 =>
        subst k
        rw [f.face_one, isom_image_segment, rotIsom_vertex_add hn0,
          rotIsom_vertex_add hn0, hfi, g.face_one]
        exact hgeP.symm
    | inr hgeM =>
      have hsym : (poligono n).isSymmetry
          ((rotIsom (poligonoAngolo n s)).trans (centerRefl n g.i)) :=
        symmetry_trans2 hrot (centerRefl_symmetry hn0 g.i)
      refine Exists.intro
        ((rotIsom (poligonoAngolo n s)).trans (centerRefl n g.i))
        (And.intro hsym ?_)
      intro k
      have hk : Or (k = 0) (k = 1) := by omega
      cases hk with
      | inl hk0 =>
        subst k
        rw [f.face_zero, g.face_zero, isom_image_singleton]
        congr 1
        change centerRefl n g.i
          (rotIsom (poligonoAngolo n s) (poligonoVertice n f.i)) = _
        rw [rotIsom_vertex_add hn0, hfi, centerRefl_vertex hn0,
          reflIndex_center]
      | inr hk1 =>
        subst k
        rw [f.face_one, isom_image_segment]
        change segment Real
          (centerRefl n g.i
            (rotIsom (poligonoAngolo n s) (poligonoVertice n f.i)))
          (centerRefl n g.i
            (rotIsom (poligonoAngolo n s) (poligonoVertice n f.j))) = _
        rw [rotIsom_vertex_add hn0, rotIsom_vertex_add hn0, hfi,
          centerRefl_vertex hn0, centerRefl_vertex hn0,
          reflIndex_center, g.face_one]
        exact hgeM.symm

end LeanEval.Geometry.PlatonicClassification
