import Mathlib
import UnicoProofs.Platonici.DiamanteRelativo
import UnicoProofs.Platonici.FacciaIntermedia
import UnicoProofs.Platonici.VerticiEsposti

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : Nat}

theorem normale_relativa {A B : Set (E n)} (hAB : A <= B)
    (hrank : faceDim B = faceDim A + 1) :
    Exists fun w : E n =>
      And (Membership.mem (Min.min (vectorSpan Real A).orthogonal
        (vectorSpan Real B)) w) (Ne w 0) := by
  let U : Submodule Real (E n) := vectorSpan Real A
  let W : Submodule Real (E n) := vectorSpan Real B
  have hUW : U <= W := vectorSpan_mono Real hAB
  have hdim : Module.finrank Real W = Module.finrank Real U + 1 := by
    change faceDim B = faceDim A + 1
    exact hrank
  have hadd := Submodule.finrank_add_inf_finrank_orthogonal hUW
  let V : Submodule Real (E n) := Min.min U.orthogonal W
  have hone : Module.finrank Real V = 1 := by
    dsimp [V]
    omega
  have hpos : 0 < Module.finrank Real V := by omega
  letI : Nontrivial V := Module.finrank_pos_iff.mp hpos
  let w : V := (exists_ne (0 : V)).choose
  have hwne : Ne w 0 := (exists_ne (0 : V)).choose_spec
  have hwval : Ne (w : E n) 0 := by
    intro h
    apply hwne
    exact Subtype.ext h
  exact Exists.intro (w : E n) (And.intro w.property hwval)

theorem pivot_relativo (P : ConvexPolytope n) {A B : Set (E n)}
    (hA : P.IsFace A) (hB : P.IsFace B)
    (hrank : faceDim B = faceDim A + 2)
    {C : Set (E n)} (hC : P.IsFace C) (hAC : A < C) (hCB : C < B) :
    Exists fun C' : Set (E n) =>
      And (P.IsFace C') (And (A < C') (And (C' < B) (Ne C' C))) := by
  classical
  let Q : ConvexPolytope n := facePolytope P hB
  have hQtoSet : Q.toSet = B := facePolytope_toSet P hB
  have hAQ : Q.IsFace A :=
    facePolytope_isFace_of P hB hA (hAC.le.trans hCB.le)
  have hCQ : Q.IsFace C := facePolytope_isFace_of P hB hC hCB.le
  have hdClo := faceDim_lt_of_ssubset P hA hC hAC
  have hdChi := faceDim_lt_of_ssubset P hC hB hCB
  have hdC : faceDim C = faceDim A + 1 := by omega
  have hdCB : faceDim B = faceDim C + 1 := by omega
  let p0 : E n := hA.2.choose
  have hp0A : Membership.mem A p0 := hA.2.choose_spec
  let hc1ex := Set.exists_of_ssubset hAC
  let c1 : E n := hc1ex.choose
  have hc1spec := hc1ex.choose_spec
  have hc1C : Membership.mem C c1 := hc1spec.1
  have hc1A : Not (Membership.mem A c1) := hc1spec.2
  let hlex := hAQ.1 hAQ.2
  let l := hlex.choose
  have hl := hlex.choose_spec
  have hp0Q : Membership.mem Q.toSet p0 := face_subset_toSet Q hAQ hp0A
  have hlmax : forall y, Membership.mem Q.toSet y -> l y <= l p0 := by
    intro y hy
    have hp := hp0A
    rw [hl] at hp
    exact hp.2 y hy
  have hlchar : forall q, Membership.mem Q.toSet q -> l q = l p0 ->
      Membership.mem A q := by
    intro q hq heq
    rw [hl]
    exact And.intro hq
      (fun y hy => le_trans (hlmax y hy) (le_of_eq heq.symm))
  have hlconst : forall z, Membership.mem A z -> l z = l p0 := by
    intro z hz
    have hz' := hz
    rw [hl] at hz'
    exact le_antisymm (hlmax z hz'.1) (hz'.2 p0 hp0Q)
  have hc1Q : Membership.mem Q.toSet c1 := face_subset_toSet Q hCQ hc1C
  have hc1lt : l c1 < l p0 := by
    apply lt_of_le_of_ne (hlmax c1 hc1Q)
    exact fun heq => hc1A (hlchar c1 hc1Q heq)
  let hwex := normale_relativa hCB.le hdCB
  let w : E n := hwex.choose
  have hw := hwex.choose_spec.1
  have hwne := hwex.choose_spec.2
  have hwperp : Membership.mem (vectorSpan Real C).orthogonal w := hw.1
  have hwB : Membership.mem (vectorSpan Real B) w := hw.2
  have hwconstC : forall z, Membership.mem C z ->
      forall z', Membership.mem C z' ->
      inner Real w z = inner Real w z' := by
    intro z hz z' hz'
    have hmem : Membership.mem (vectorSpan Real C) (z - z') :=
      vsub_mem_vectorSpan Real hz hz'
    have hzero : inner Real (z - z') w = 0 := by
      have horth :=
        (Submodule.mem_orthogonal (vectorSpan Real C) w).mp hwperp
      exact horth (z - z') hmem
    rw [real_inner_comm] at hzero
    rw [inner_sub_right] at hzero
    linarith
  have hwQ : Membership.mem (vectorSpan Real Q.toSet) w := by
    simpa [hQtoSet] using hwB
  let hu0ex := exists_vertex_inner_ne Q hp0Q hwQ hwne
  let u0 : E n := hu0ex.choose
  have hu0spec := hu0ex.choose_spec
  have hu0V := hu0spec.1
  have hu0ne := hu0spec.2
  have costruzione : forall w' : E n,
      (forall z, Membership.mem C z -> forall z', Membership.mem C z' ->
        inner Real w' z = inner Real w' z') ->
      (Exists fun u => And (Membership.mem Q.vertices u)
        (inner Real w' p0 < inner Real w' u)) ->
      Exists fun F : Set (E n) =>
        And (P.IsFace F) (And (A < F) (And (F < B) (Ne F C))) := by
    intro w' hw'C hup
    let ux : E n := hup.choose
    have huxV := hup.choose_spec.1
    have huxgt := hup.choose_spec.2
    let S : Finset (E n) :=
      Q.vertices.filter (fun u => inner Real w' p0 < inner Real w' u)
    have hSne : S.Nonempty := Exists.intro ux
      (Finset.mem_filter.mpr (And.intro huxV huxgt))
    let r : E n -> Real := fun u =>
      (l p0 - l u) / (inner Real w' u - inner Real w' p0)
    let husex := S.exists_min_image r hSne
    let us : E n := husex.choose
    have husspec := husex.choose_spec
    have husS := husspec.1
    have husmin := husspec.2
    have husV : Membership.mem Q.vertices us :=
      (Finset.mem_filter.mp husS).1
    have husgt : inner Real w' p0 < inner Real w' us :=
      (Finset.mem_filter.mp husS).2
    have husQ : Membership.mem Q.toSet us := subset_convexHull Real _ husV
    have husC : Not (Membership.mem C us) := by
      intro hus
      have heq := hw'C us hus p0 (hAC.le hp0A)
      rw [heq] at husgt
      exact lt_irrefl _ husgt
    have husA : Not (Membership.mem A us) := fun hus => husC (hAC.le hus)
    have huslt : l us < l p0 := by
      apply lt_of_le_of_ne (hlmax us husQ)
      exact fun heq => husA (hlchar us husQ heq)
    let t : Real := r us
    have htpos : 0 < t := by
      dsimp [t, r]
      exact div_pos (by linarith) (by linarith)
    let psi : ContinuousLinearMap (RingHom.id Real) (E n) Real :=
      l + HSMul.hSMul t (innerSL Real w')
    have hpsival : forall y : E n,
        psi y = l y + t * inner Real w' y := by
      intro y
      dsimp [psi]
      simp [smul_apply, smul_eq_mul]
    have hvert : forall u, Membership.mem Q.vertices u -> psi u <= psi p0 := by
      intro u huV
      rw [hpsival, hpsival]
      by_cases hside : inner Real w' p0 < inner Real w' u
      case pos =>
        have huS : Membership.mem S u :=
          Finset.mem_filter.mpr (And.intro huV hside)
        have hrle : t <= r u := husmin u huS
        have hgap : 0 < inner Real w' u - inner Real w' p0 := by linarith
        have hmul : t * (inner Real w' u - inner Real w' p0) <=
            r u * (inner Real w' u - inner Real w' p0) :=
          mul_le_mul_of_nonneg_right hrle (le_of_lt hgap)
        have hcancel : r u * (inner Real w' u - inner Real w' p0) =
            l p0 - l u := by
          dsimp [r]
          field_simp
        nlinarith
      case neg =>
        push Not at hside
        have hlu : l u <= l p0 :=
          hlmax u (subset_convexHull Real _ huV)
        have hmul : t * inner Real w' u <= t * inner Real w' p0 :=
          mul_le_mul_of_nonneg_left hside (le_of_lt htpos)
        linarith
    have hbody : forall y, Membership.mem Q.toSet y -> psi y <= psi p0 := by
      intro y hy
      have hconv : Convex Real
          ((fun z : E n => psi z <= psi p0) : Set (E n)) := by
        apply convex_halfSpace_le
        exact psi.toLinearMap.isLinear
      have hsub : (Q.vertices : Set (E n)) <=
          ((fun z : E n => psi z <= psi p0) : Set (E n)) := by
        intro u hu
        exact hvert u (Finset.mem_coe.mp hu)
      exact convexHull_min hsub hconv hy
    have hpsiA : forall z, Membership.mem A z -> psi z = psi p0 := by
      intro z hz
      rw [hpsival, hpsival, hlconst z hz,
        hw'C z (hAC.le hz) p0 (hAC.le hp0A)]
    let F : Set (E n) := fun x =>
      And (Membership.mem Q.toSet x)
        (forall y, Membership.mem Q.toSet y -> psi y <= psi x)
    have hAF : A <= F := by
      intro z hz
      apply And.intro (face_subset_toSet Q hAQ hz)
      intro y hy
      rw [hpsiA z hz]
      exact hbody y hy
    have hp0F : Membership.mem F p0 := hAF hp0A
    have hFQ : Q.IsFace F := And.intro
      (fun _ => Exists.intro psi rfl) (Exists.intro p0 hp0F)
    have htie : psi us = psi p0 := by
      rw [hpsival, hpsival]
      have hgap : 0 < inner Real w' us - inner Real w' p0 := by linarith
      have hcancel : t * (inner Real w' us - inner Real w' p0) =
          l p0 - l us := by
        dsimp [t, r]
        field_simp
      nlinarith
    have husF : Membership.mem F us := by
      apply And.intro husQ
      intro y hy
      rw [htie]
      exact hbody y hy
    have hc1F : Not (Membership.mem F c1) := by
      intro hmem
      have heqpsi : psi c1 = psi p0 :=
        le_antisymm (hbody c1 hc1Q) (hmem.2 p0 hp0Q)
      rw [hpsival, hpsival] at heqpsi
      have heqinner : inner Real w' c1 = inner Real w' p0 :=
        hw'C c1 hc1C p0 (hAC.le hp0A)
      rw [heqinner] at heqpsi
      have : l c1 = l p0 := by linarith
      exact (ne_of_lt hc1lt) this
    have hFP : P.IsFace F := isFace_of_facePolytope P hB hFQ
    have hAFstrict : A < F := by
      apply And.intro hAF
      intro hFA
      exact husA (hFA husF)
    have hFBsub : F <= B := by
      intro x hx
      rw [hQtoSet.symm]
      exact hx.1
    have hFBstrict : F < B := by
      apply And.intro hFBsub
      intro hBF
      exact hc1F (hBF (hCB.le hc1C))
    have hFneC : Ne F C := by
      intro heq
      apply hc1F
      rw [heq]
      exact hc1C
    exact Exists.intro F
      (And.intro hFP (And.intro hAFstrict (And.intro hFBstrict hFneC)))
  by_cases hgt : inner Real w p0 < inner Real w u0
  case pos =>
    exact costruzione w hwconstC
      (Exists.intro u0 (And.intro hu0V hgt))
  case neg =>
    have hlt : inner Real w u0 < inner Real w p0 := by
      apply lt_of_le_of_ne (le_of_not_gt hgt)
      exact hu0ne
    exact costruzione (-w)
      (by
        intro z hz z' hz'
        rw [inner_neg_left, inner_neg_left, hwconstC z hz z' hz'])
      (Exists.intro u0 (And.intro hu0V (by
        rw [inner_neg_left, inner_neg_left]
        linarith)))

theorem secondo_intermedio (P : ConvexPolytope n) {A B : Set (E n)}
    (hA : P.IsFace A) (hB : P.IsFace B)
    (hrank : faceDim B = faceDim A + 2)
    {C : Set (E n)} (hC : P.IsFace C) (hAC : A < C) (hCB : C < B) :
    Exists fun C' : Set (E n) =>
      And (P.IsFace C') (And (A < C') (And (C' < B) (Ne C' C))) := by
  exact pivot_relativo P hA hB hrank hC hAC hCB

theorem existsUnique_other_middle (P : ConvexPolytope n)
    {A B : Set (E n)} (hA : P.IsFace A) (hB : P.IsFace B)
    (hrank : faceDim B = faceDim A + 2)
    {C : Set (E n)} (hC : P.IsFace C) (hAC : A < C) (hCB : C < B) :
    ExistsUnique fun C' : Set (E n) =>
      And (And (P.IsFace C') (And (A < C') (C' < B))) (Ne C' C) := by
  classical
  let hC'ex := secondo_intermedio P hA hB hrank hC hAC hCB
  let C' : Set (E n) := hC'ex.choose
  have hC'spec := hC'ex.choose_spec
  have hC'face := hC'spec.1
  have hAC' := hC'spec.2.1
  have hC'B := hC'spec.2.2.1
  have hC'C := hC'spec.2.2.2
  refine ExistsUnique.intro C'
    (And.intro (And.intro hC'face (And.intro hAC' hC'B)) hC'C) ?_
  intro C'' hC''
  have hcases := atMostTwo_middle_faces P hA hB hrank
    hC hAC hCB hC'face hAC' hC'B
    hC''.1.1 hC''.1.2.1 hC''.1.2.2
  have hnotFirst : Ne C C' := hC'C.symm
  have hnotSecond : Ne C C'' := hC''.2.symm
  have hC'C'' : C' = C'' :=
    (hcases.resolve_left hnotFirst).resolve_left hnotSecond
  exact hC'C''.symm

end LeanEval.Geometry.PlatonicClassification
