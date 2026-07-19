import Mathlib
import UnicoProofs.Platonici.RaggioNelPiano
import UnicoProofs.Platonici.SemipianoScarico
import UnicoProofs.Platonici.RuotaFan
import UnicoProofs.Platonici.Chiusura
import UnicoProofs.Platonici.PoligonoConnesso

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- The same cyclic fan with the opposite cyclic orientation. -/
def rovesciato {P : FiniteConvexPolytope (E 3)} {v : E 3} {m : Nat}
    (D : P.CyclicVertexData v (m + 1)) : P.CyclicVertexData v (m + 1) where
  faccetta := fun i => D.faccetta (-i)
  isFacet := fun i => D.isFacet (-i)
  mem_v := fun i => D.mem_v (-i)
  distinte := by
    intro i j hij
    have h := D.distinte hij
    exact neg_injective h
  complete := by
    intro F hF hvF
    obtain ⟨j, hj⟩ := D.complete F hF hvF
    exact ⟨-j, by simpa using hj⟩
  σ := D.σ.symm
  fissa_v := by
    have h := congrArg D.σ.symm D.fissa_v
    simpa using h.symm
  preserva := by
    calc
      (⇑D.σ.symm) '' P.toSet =
          (⇑D.σ.symm) '' ((⇑D.σ) '' P.toSet) := by rw [D.preserva]
      _ = P.toSet := D.σ.toEquiv.symm_image_image P.toSet
  ruota := by
    intro i
    have hindex : finRotate (m + 1) (-(finRotate (m + 1) i)) = -i := by
      simp
    have h := D.ruota (-(finRotate (m + 1) i))
    rw [hindex] at h
    have hback := congrArg (fun S : Set (E 3) => (⇑D.σ.symm) '' S) h
    simpa [Set.image_image, hindex] using hback.symm
  spigolo := by
    intro i
    have hindex : finRotate (m + 1) (-(finRotate (m + 1) i)) = -i := by
      simp
    obtain ⟨x, hxv, hx⟩ := D.spigolo (-(finRotate (m + 1) i))
    rw [hindex] at hx
    refine ⟨x, hxv, hx.2, ?_⟩
    exact hx.1
  spigolo_due := by
    intro i j x hx hxv hxj
    have hindex : finRotate (m + 1) (-(finRotate (m + 1) i)) = -i := by
      simp
    have hedge : x ∈ D.faccetta (-(finRotate (m + 1) i)) ∩
        D.faccetta (finRotate (m + 1) (-(finRotate (m + 1) i))) := by
      exact ⟨hx.2, by rw [hindex]; exact hx.1⟩
    have hcases := D.spigolo_due (-(finRotate (m + 1) i)) (-j) x
      hedge hxv hxj
    rcases hcases with h | h
    · right
      exact neg_injective (by simpa using h)
    · left
      exact neg_injective (by simpa [hindex] using h)

@[simp] theorem rovesciato_faccetta
    {P : FiniteConvexPolytope (E 3)} {v : E 3} {m : Nat}
    (D : P.CyclicVertexData v (m + 1)) (i : Fin (m + 1)) :
    (rovesciato D).faccetta i = D.faccetta (-i) := rfl

/-- The edge selected by a common ray and a common diameter has a common
second endpoint. -/
theorem vertice_adiacente_comune
    (P Q : ConvexPolytope 3) {p q : Nat}
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (hQ : Q.asFinite.IsCyclicallyRegularOfType p q)
    {v : E 3} (hvP : v ∈ P.vertices) (hvQ : v ∈ Q.vertices)
    (DP : P.asFinite.CyclicVertexData v q)
    (DQ : Q.asFinite.CyclicVertexData v q)
    (hdir : dir P.asFinite v DP = dir Q.asFinite v DQ)
    (hdiam : ∀ k, Metric.diam
        (DP.faccetta k ∩ DP.faccetta (finRotate q k)) =
      Metric.diam (DQ.faccetta k ∩ DQ.faccetta (finRotate q k)))
    (i : Fin q) :
    ∃ w : E 3, w ∈ P.vertices ∧ w ∈ Q.vertices ∧ w ≠ v ∧
      w ∈ DP.faccetta i ∩ DP.faccetta (finRotate q i) ∧
      DP.faccetta i ∩ DP.faccetta (finRotate q i) = segment ℝ v w ∧
      DP.faccetta i ∩ DP.faccetta (finRotate q i) =
        DQ.faccetta i ∩ DQ.faccetta (finRotate q i) := by
  classical
  let edge : SpigoloPer P v := spigolo_adiacente P hP.2.2.1 DP i
  let w : E 3 := SpigoloPer.altro P v hvP edge
  have hspec := SpigoloPer.altro_spec P v hvP edge
  have hedge := spigolo_del_fan_eq P Q hP hQ hvP hvQ DP DQ i
    (congrFun hdir i) (hdiam i)
  have hfaceP : P.IsFace
      (DP.faccetta i ∩ DP.faccetta (finRotate q i)) :=
    (adiacenza_passo_uno_locale P hP.2.2.1 DP i).1
  have hfaceQ0 : Q.IsFace
      (DQ.faccetta i ∩ DQ.faccetta (finRotate q i)) :=
    (adiacenza_passo_uno_locale Q hQ.2.2.1 DQ i).1
  have hfaceQ : Q.IsFace
      (DP.faccetta i ∩ DP.faccetta (finRotate q i)) := by
    rw [hedge]
    exact hfaceQ0
  have hwEdge : w ∈ DP.faccetta i ∩ DP.faccetta (finRotate q i) := by
    simpa [edge, w] using hspec.2.1
  have hwP : w ∈ P.vertices := by simpa [edge, w] using hspec.1
  have hwQ : w ∈ Q.vertices :=
    vertice_comune_di_faccia_comune P Q hfaceP hfaceQ hwP hwEdge
  refine ⟨w, hwP, hwQ, ?_, hwEdge, ?_, hedge⟩
  · simpa [edge, w] using hspec.2.2.1
  · simpa [edge, w] using hspec.2.2.2

/-- A cyclic certificate can be oriented and rotated so that two prescribed
adjacent facets occur at indices zero and one in the prescribed order. -/
theorem fan_allineato_su_faccette
    (P : ConvexPolytope 3) {p q : Nat} [NeZero q]
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    {w x : E 3} (hw : w ∈ P.vertices) (hxw : x ≠ w)
    {A B delta : Set (E 3)}
    (hA : P.asFinite.IsFacet A) (hB : P.asFinite.IsFacet B)
    (hAB : A ≠ B) (hwA : w ∈ A) (hwB : w ∈ B)
    (hxA : x ∈ A) (hxB : x ∈ B)
    (hdelta : P.IsFace delta) (hddelta : faceDim delta = 1)
    (hwdelta : w ∈ delta) (hxdelta : x ∈ delta) (hdeltaA : delta ⊆ A)
    (hdeltaB : delta ⊆ B) :
    ∃ D : P.asFinite.CyclicVertexData w q,
      D.faccetta 0 = A ∧ D.faccetta 1 = B := by
  classical
  have hq : 3 ≤ q := hP.2.2.1
  obtain ⟨m, hqm⟩ : ∃ m, q = m + 1 := by
    refine ⟨q - 1, ?_⟩
    omega
  subst q
  obtain ⟨side, hside, hregular, hcyclic⟩ := hP.2.2.2
  obtain ⟨D⟩ := hcyclic w hw
  obtain ⟨a, ha⟩ := D.complete A hA hwA
  have hlocal := spigoli_in_v_della_faccetta_esatti P hP.2.2.1 D a
    hdelta hddelta hwdelta (by simpa only [ha] using hdeltaA)
  have hAface := (P.asFinite_isFacet_iff A).1 hA
  have hBface := (P.asFinite_isFacet_iff B).1 hB
  rcases hlocal with hprev | hnext
  · let b : Fin (m + 1) := (finRotate (m + 1)).symm a
    have hba : finRotate (m + 1) b = a :=
      (finRotate (m + 1)).apply_symm_apply a
    have hbne : b ≠ a := by
      intro h
      apply _root_.finRotate_ne_self (by omega : 2 ≤ m + 1) a
      simpa only [h] using hba
    have hBindex : D.faccetta b = B := by
      have hCface := (P.asFinite_isFacet_iff (D.faccetta b)).1 (D.isFacet b)
      have hcases := spigolo_in_due_faccette P w
        hAface.1 hAface.2 hBface.1 hBface.2 hCface.1 hCface.2
        hAB hwA hwB (D.mem_v b) ⟨hxA, hxB⟩ hxw ?_
      · rcases hcases with hCA | hCB
        · exfalso
          apply hbne
          apply D.distinte
          rw [← ha]
          exact hCA
        · exact hCB
      · have hxdelta : x ∈ delta := by
          exact hxdelta
        rw [hprev] at hxdelta
        simpa [b] using hxdelta.1
    let R := ruotato (rovesciato D) (-a)
    refine ⟨R, ?_, ?_⟩
    · change D.faccetta (-((0 : Fin (m + 1)) + -a)) = A
      simpa using ha.symm
    · change D.faccetta (-(1 + -a)) = B
      have hneg : -(1 + -a) = b := by
        apply (finRotate (m + 1)).injective
        simp [b]
      rw [hneg]
      exact hBindex
  · have hBindex : D.faccetta (finRotate (m + 1) a) = B := by
      have hCface := (P.asFinite_isFacet_iff
        (D.faccetta (finRotate (m + 1) a))).1
        (D.isFacet (finRotate (m + 1) a))
      have hcases := spigolo_in_due_faccette P w
        hAface.1 hAface.2 hBface.1 hBface.2 hCface.1 hCface.2
        hAB hwA hwB (D.mem_v (finRotate (m + 1) a))
        ⟨hxA, hxB⟩ hxw ?_
      · rcases hcases with hCA | hCB
        · exfalso
          apply _root_.finRotate_ne_self (by omega : 2 ≤ m + 1) a
          apply D.distinte
          rw [← ha]
          exact hCA
        · exact hCB
      · have hxdelta : x ∈ delta := by
          exact hxdelta
        rw [hnext] at hxdelta
        exact hxdelta.2
    let R := ruotato D a
    refine ⟨R, ?_, ?_⟩
    · change D.faccetta ((0 : Fin (m + 1)) + a) = A
      simpa using ha.symm
    · change D.faccetta (1 + a) = B
      simpa [finRotate_apply, add_comm] using hBindex

/-- If a marked edge is a known segment, its marked unit direction points
from the marked endpoint to the other endpoint. -/
theorem direzione_su_segmento_noto
    (P : ConvexPolytope 3) {p q : Nat}
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    {w x : E 3} (hw : w ∈ P.vertices) (hx : x ∈ P.vertices)
    (hxw : x ≠ w) (D : P.asFinite.CyclicVertexData w q) (k : Fin q)
    (hedge : D.faccetta k ∩ D.faccetta (finRotate q k) =
      segment ℝ x w) :
    dir P.asFinite w D k = ‖x - w‖⁻¹ • (x - w) := by
  classical
  obtain ⟨t, ht, hray⟩ := spigolo_eq_segmento_sul_raggio P hP hw D k
  let y : E 3 := w + t • dir P.asFinite w D k
  have hedgeRay : D.faccetta k ∩ D.faccetta (finRotate q k) =
      segment ℝ w y := by
    simpa [y] using hray
  have hwy : w ≠ y := by
    intro hwy
    have hzero : t • dir P.asFinite w D k = 0 := by
      have := congrArg (fun z => z - w) hwy
      simpa [y] using this.symm
    have ht0 : t = 0 := by
      rcases smul_eq_zero.mp hzero with h | h
      · exact h
      · exfalso
        have hunit := dir_unitaria P.asFinite w D k
        rw [h, norm_zero] at hunit
        norm_num at hunit
    exact (ne_of_gt ht) ht0
  have hface : P.IsFace
      (D.faccetta k ∩ D.faccetta (finRotate q k)) :=
    (adiacenza_passo_uno_locale P hP.2.2.1 D k).1
  have hxedge : x ∈ D.faccetta k ∩ D.faccetta (finRotate q k) := by
    rw [hedge]
    exact left_mem_segment ℝ x w
  have hxy : x = y := by
    rcases vertice_estremo_del_segmento P hface hedgeRay hwy hx hxedge with h | h
    · exact (hxw h).elim
    · exact h
  have hsub : x - w = t • dir P.asFinite w D k := by
    rw [hxy]
    simp [y]
  have hnorm : ‖x - w‖ = t := by
    rw [hsub, norm_smul, dir_unitaria P.asFinite w D k, mul_one,
      Real.norm_of_nonneg (le_of_lt ht)]
  rw [hnorm, hsub, smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul]

theorem secondo_estremo_segmento_unico {v w x : E 3} (hvw : v ≠ w)
    (hseg : segment Real v w = segment Real v x) : w = x := by
  have hdiam : dist v w = dist v x := by
    rw [← diam_segment v w, hseg, diam_segment]
  rcases endpoints_of_segment_eq_of_dist_eq hseg hvw hdiam with h | h
  · exact h.2
  · exact (hvw h.2.symm).elim

/-- Linear half-plane form of `raggio_nel_piano_unico`.  The vector `r`
canonically fixes the sign of the Gram--Schmidt normal. -/
theorem raggio_unico_da_semipiano_lineare {u r z z' : E 3}
    (hu : ‖u‖ = 1) (hzNorm : ‖z‖ = 1) (hzNorm' : ‖z'‖ = 1)
    (hind : LinearIndependent Real ![u, r])
    (phi : E 3 →L[Real] Real)
    (hphiu : phi u = 0) (hphir : 0 < phi r)
    (hphiz : 0 < phi z) (hphiz' : 0 < phi z')
    (hzSpan : z ∈ Submodule.span Real ({u, r} : Set (E 3)))
    (hzSpan' : z' ∈ Submodule.span Real ({u, r} : Set (E 3)))
    (hang : ⟪u, z⟫ = ⟪u, z'⟫) : z = z' := by
  classical
  let s : Real := ⟪r, u⟫
  let a : E 3 := r - s • u
  have haNe : a ≠ 0 := by
    intro ha
    have hr : r = s • u := sub_eq_zero.mp ha
    rw [LinearIndependent.pair_iff] at hind
    have hrel : (-s) • u + (1 : Real) • r = 0 := by
      rw [hr, one_smul, neg_smul, neg_add_cancel]
    have hcoef := hind (-s) 1 hrel
    norm_num at hcoef
  have haPos : 0 < ‖a‖ := norm_pos_iff.mpr haNe
  let an : Real := ‖a‖
  have hanPos : 0 < an := by simpa [an] using haPos
  let n : E 3 := an⁻¹ • a
  have hua : ⟪u, a⟫ = 0 := by
    dsimp [a, s]
    rw [inner_sub_right, real_inner_smul_right, real_inner_comm r u,
      real_inner_self_eq_norm_sq, hu]
    norm_num
  have hun : ⟪u, n⟫ = 0 := by
    dsimp [n]
    rw [real_inner_smul_right, hua, mul_zero]
  have hn : ‖n‖ = 1 := by
    dsimp [n]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hanPos)]
    simpa [an] using inv_mul_cancel₀ (ne_of_gt hanPos)
  have hnu : ⟪n, u⟫ = 0 := by
    rw [real_inner_comm]
    exact hun
  have hna : 0 < ⟪n, a⟫ := by
    dsimp [n]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    calc
      0 < an := hanPos
      _ = an⁻¹ * ‖a‖ ^ 2 := by
        dsimp [an]
        field_simp
  have hrform : r = a + s • u := by
    dsimp [a]
    abel
  have hnr : 0 < ⟪n, r⟫ := by
    rw [hrform, inner_add_right, real_inner_smul_right, hnu, mul_zero,
      add_zero]
    exact hna
  have haform : a = an • n := by
    dsimp [n]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hanPos), one_smul]
  have spanToNormal : ∀ {y : E 3},
      y ∈ Submodule.span Real ({u, r} : Set (E 3)) →
      y ∈ Submodule.span Real ({u, n} : Set (E 3)) := by
    intro y hy
    rw [Submodule.mem_span_pair] at hy ⊢
    obtain ⟨c, d, hcd⟩ := hy
    refine ⟨c + d * s, d * an, ?_⟩
    calc
      (c + d * s) • u + (d * an) • n =
          c • u + d • (s • u + an • n) := by module
      _ = c • u + d • (s • u + a) := by rw [haform]
      _ = c • u + d • r := by rw [hrform]; module
      _ = y := hcd
  have positiveNormal : ∀ {y : E 3},
      y ∈ Submodule.span Real ({u, r} : Set (E 3)) →
      0 < phi y → 0 < ⟪n, y⟫ := by
    intro y hy hphiy
    rw [Submodule.mem_span_pair] at hy
    obtain ⟨c, d, hcd⟩ := hy
    have hphiForm : phi y = d * phi r := by
      rw [← hcd]
      simp [hphiu]
    have hd : 0 < d := by nlinarith
    have hinnerForm : ⟪n, y⟫ = d * ⟪n, r⟫ := by
      rw [← hcd, inner_add_right, real_inner_smul_right,
        real_inner_smul_right, hnu]
      ring
    rw [hinnerForm]
    exact mul_pos hd hnr
  exact raggio_nel_piano_unico hu hn hun
    (spanToNormal hzSpan) (spanToNormal hzSpan') hzNorm hzNorm' hang
    ⟨positiveNormal hzSpan hphiz, positiveNormal hzSpan' hphiz'⟩

theorem dir_mem_vectorSpan_faccetta_sinistra
    {P : ConvexPolytope 3} {v : E 3} {q : Nat}
    (D : P.asFinite.CyclicVertexData v q) (k : Fin q) :
    dir P.asFinite v D k ∈ vectorSpan Real (D.faccetta k) := by
  unfold dir
  apply Submodule.smul_mem
  exact sub_mem_vectorSpan (punto_spec P.asFinite v D k).2.1 (D.mem_v k)

theorem dir_mem_vectorSpan_faccetta_destra
    {P : ConvexPolytope 3} {v : E 3} {q : Nat}
    (D : P.asFinite.CyclicVertexData v q) (k : Fin q) :
    dir P.asFinite v D k ∈
      vectorSpan Real (D.faccetta (finRotate q k)) := by
  unfold dir
  apply Submodule.smul_mem
  exact sub_mem_vectorSpan (punto_spec P.asFinite v D k).2.2
    (D.mem_v (finRotate q k))

theorem vectorSpan_eq_span_vettori {A : Set (E 3)} {u r : E 3}
    (huA : u ∈ vectorSpan Real A) (hrA : r ∈ vectorSpan Real A)
    (hind : LinearIndependent Real ![u, r])
    (hrank : Module.finrank Real (vectorSpan Real A) = 2) :
    vectorSpan Real A = Submodule.span Real ({u, r} : Set (E 3)) := by
  classical
  have hle : Submodule.span Real ({u, r} : Set (E 3)) ≤ vectorSpan Real A := by
    rw [Submodule.span_le]
    intro y hy
    rcases hy with rfl | hy
    · exact huA
    · simpa only [Set.mem_singleton_iff] using hy ▸ hrA
  have hrange : Set.range ![u, r] = ({u, r} : Set (E 3)) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | hy)
      · exact ⟨0, rfl⟩
      · rw [Set.mem_singleton_iff] at hy
        exact ⟨1, hy.symm⟩
  have hspanRank : Module.finrank Real
      (Submodule.span Real ({u, r} : Set (E 3))) = 2 := by
    rw [← hrange, finrank_span_eq_card hind]
    simp
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hspanRank, hrank])).symm

/-- A supporting functional is strictly positive on every marked ray whose
second incident facet is not one of the two facets of the supporting edge. -/
theorem funzionale_positivo_su_dir
    {P : ConvexPolytope 3} {v : E 3} {q : Nat}
    (D : P.asFinite.CyclicVertexData v q) (edgeIndex rayIndex otherIndex : Fin q)
    (phi : E 3 →L[Real] Real) {F : Set (E 3)}
    (hvF : v ∈ F) (hpF : punto P.asFinite v D rayIndex ∈ F)
    (hpOther : punto P.asFinite v D rayIndex ∈ D.faccetta otherIndex)
    (hlower : ∀ y ∈ F, phi v ≤ phi y)
    (hlevel : {y ∈ F | phi y = phi v} =
      D.faccetta edgeIndex ∩ D.faccetta (finRotate q edgeIndex))
    (hotherEdge : otherIndex ≠ edgeIndex)
    (hotherNext : otherIndex ≠ finRotate q edgeIndex) :
    0 < phi (dir P.asFinite v D rayIndex) := by
  have hpNe := (punto_spec P.asFinite v D rayIndex).1
  have hnormPos : 0 < ‖punto P.asFinite v D rayIndex - v‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hpNe)
  have hinvPos : 0 < ‖punto P.asFinite v D rayIndex - v‖⁻¹ :=
    inv_pos.mpr hnormPos
  have hdirForm : phi (dir P.asFinite v D rayIndex) =
      ‖punto P.asFinite v D rayIndex - v‖⁻¹ *
        (phi (punto P.asFinite v D rayIndex) - phi v) := by
    simp [dir, map_sub, smul_eq_mul]
  have hdiffNonneg :
      0 ≤ phi (punto P.asFinite v D rayIndex) - phi v :=
    sub_nonneg.mpr (hlower _ hpF)
  have hnonneg : 0 ≤ phi (dir P.asFinite v D rayIndex) := by
    rw [hdirForm]
    exact mul_nonneg (le_of_lt hinvPos) hdiffNonneg
  apply lt_of_le_of_ne hnonneg
  intro hzeroRev
  have hzero : phi (dir P.asFinite v D rayIndex) = 0 := hzeroRev.symm
  rw [hdirForm] at hzero
  have hdiffZero :
      phi (punto P.asFinite v D rayIndex) - phi v = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hinvPos)
  have hpLevel : punto P.asFinite v D rayIndex ∈ {y ∈ F | phi y = phi v} :=
    ⟨hpF, sub_eq_zero.mp hdiffZero⟩
  have hpEdge : punto P.asFinite v D rayIndex ∈
      D.faccetta edgeIndex ∩ D.faccetta (finRotate q edgeIndex) := by
    rw [← hlevel]
    exact hpLevel
  rcases D.spigolo_due edgeIndex otherIndex
      (punto P.asFinite v D rayIndex) hpEdge hpNe hpOther with h | h
  · exact hotherEdge h
  · exact hotherNext h

/-- Core of the inductive step: at the common adjacent vertex one can mark
the two cyclic fans with the same first two rays. -/
theorem due_raggi_comuni_al_vicino
    (P Q : ConvexPolytope 3) {p q : Nat} [NeZero q]
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (hQ : Q.asFinite.IsCyclicallyRegularOfType p q)
    {v : E 3} (hvP : v ∈ P.vertices) (hvQ : v ∈ Q.vertices)
    (DP : P.asFinite.CyclicVertexData v q)
    (DQ : Q.asFinite.CyclicVertexData v q)
    (hdir : dir P.asFinite v DP = dir Q.asFinite v DQ)
    (hdiam : ∀ k, Metric.diam
        (DP.faccetta k ∩ DP.faccetta (finRotate q k)) =
      Metric.diam (DQ.faccetta k ∩ DQ.faccetta (finRotate q k)))
    (i : Fin q) :
    ∃ (w : E 3) (hwP : w ∈ P.vertices) (hwQ : w ∈ Q.vertices)
      (EP : P.asFinite.CyclicVertexData w q)
      (EQ : Q.asFinite.CyclicVertexData w q),
      dir P.asFinite w EP 0 = dir Q.asFinite w EQ 0 ∧
      dir P.asFinite w EP 1 = dir Q.asFinite w EQ 1 := by
  classical
  have hq : 3 ≤ q := hP.2.2.1
  obtain ⟨w, hwP, hwQ, hwne, hwEdgeP, hsegP, hedge⟩ :=
    vertice_adiacente_comune P Q hP hQ hvP hvQ DP DQ hdir hdiam i
  have hwEdgeQ : w ∈ DQ.faccetta i ∩ DQ.faccetta (finRotate q i) := by
    rw [← hedge]
    exact hwEdgeP
  have hsegQ : DQ.faccetta i ∩ DQ.faccetta (finRotate q i) =
      segment Real v w := hedge.symm.trans hsegP
  have hfaceEdgeP := adiacenza_passo_uno_locale P hq DP i
  have hfaceEdgeQ := adiacenza_passo_uno_locale Q hQ.2.2.1 DQ i
  have hfacetNeP : DP.faccetta (finRotate q i) ≠ DP.faccetta i := by
    intro h
    apply _root_.finRotate_ne_self (by omega : 2 ≤ q) i
    exact DP.distinte h
  have hfacetNeQ : DQ.faccetta (finRotate q i) ≠ DQ.faccetta i := by
    intro h
    apply _root_.finRotate_ne_self (by omega : 2 ≤ q) i
    exact DQ.distinte h
  obtain ⟨EP, hEP0, hEP1⟩ := fan_allineato_su_faccette P hP hwP
    (Ne.symm hwne) (DP.isFacet (finRotate q i)) (DP.isFacet i) hfacetNeP
    hwEdgeP.2 hwEdgeP.1 (DP.mem_v (finRotate q i)) (DP.mem_v i)
    hfaceEdgeP.1 hfaceEdgeP.2.1 hwEdgeP
    ⟨DP.mem_v i, DP.mem_v (finRotate q i)⟩
    Set.inter_subset_right Set.inter_subset_left
  obtain ⟨EQ, hEQ0, hEQ1⟩ := fan_allineato_su_faccette Q hQ hwQ
    (Ne.symm hwne) (DQ.isFacet (finRotate q i)) (DQ.isFacet i) hfacetNeQ
    hwEdgeQ.2 hwEdgeQ.1 (DQ.mem_v (finRotate q i)) (DQ.mem_v i)
    hfaceEdgeQ.1 hfaceEdgeQ.2.1 hwEdgeQ
    ⟨DQ.mem_v i, DQ.mem_v (finRotate q i)⟩
    Set.inter_subset_right Set.inter_subset_left
  have hrot01 : finRotate q (0 : Fin q) = 1 := by
    simp [finRotate_apply]
  have hedgeEP : EP.faccetta 0 ∩ EP.faccetta (finRotate q 0) =
      segment Real v w := by
    simpa only [hrot01, hEP0, hEP1, Set.inter_comm] using hsegP
  have hedgeEQ : EQ.faccetta 0 ∩ EQ.faccetta (finRotate q 0) =
      segment Real v w := by
    simpa only [hrot01, hEQ0, hEQ1, Set.inter_comm] using hsegQ
  have huPform := direzione_su_segmento_noto P hP hwP hvP
    (Ne.symm hwne) EP 0 hedgeEP
  have huQform := direzione_su_segmento_noto Q hQ hwQ hvQ
    (Ne.symm hwne) EQ 0 hedgeEQ
  have hzero : dir P.asFinite w EP 0 = dir Q.asFinite w EQ 0 := by
    rw [huPform, huQform]
  let j : Fin q := (finRotate q).symm i
  have hji : finRotate q j = i := (finRotate q).apply_symm_apply i
  let u : E 3 := dir P.asFinite w EP 0
  let r : E 3 := dir P.asFinite v DP j
  let z : E 3 := dir P.asFinite w EP 1
  let z' : E 3 := dir Q.asFinite w EQ 1
  have hOldForm := direzione_su_segmento_noto P hP hvP hwP hwne DP i
    (by simpa only [segment_symm] using hsegP)
  have huOld : u = -dir P.asFinite v DP i := by
    rw [show u = dir P.asFinite w EP 0 by rfl, huPform, hOldForm]
    have hsub : v - w = -(w - v) := by abel
    rw [hsub, norm_neg, smul_neg]
  have hcons : LinearIndependent Real
      ![r, dir P.asFinite v DP i] := by
    simpa only [r, hji] using raggi_consecutivi_indipendenti P hP hvP DP j
  have hconsSwap : LinearIndependent Real
      ![dir P.asFinite v DP i, r] := LinearIndependent.pair_symm_iff.mp hcons
  have hscaled := indipendenti_smul_separati
    (by norm_num : (-1 : Real) ≠ 0) (by norm_num : (1 : Real) ≠ 0) hconsSwap
  have hind : LinearIndependent Real ![u, r] := by
    have hminus : (-1 : Real) • dir P.asFinite v DP i = u := by
      rw [neg_one_smul, ← huOld]
    simpa only [hminus, one_smul] using hscaled
  obtain ⟨wData, hsegDataP, hsegDataQ, hpiano, hsemi⟩ :=
    dati_faccetta_adiacente P Q hP hQ hvP hvQ DP DQ hdir hdiam i
  have hwData : wData = w := by
    exact (secondo_estremo_segmento_unico (Ne.symm hwne)
      (hsegP.symm.trans hsegDataP)).symm
  subst wData
  rcases hsemi with ⟨phi, hphiEdge, hlowerP, hlowerQ, hlevelP, hlevelQ⟩
  have hphiu : phi u = 0 := by
    rw [show u = dir P.asFinite w EP 0 by rfl, huPform]
    simp [map_sub, smul_eq_mul, hphiEdge]
  have hjne : j ≠ i := by
    intro hj
    apply _root_.finRotate_ne_self (by omega : 2 ≤ q) i
    simpa only [hj] using hji
  have hjneNext : j ≠ finRotate q i := by
    intro hj
    apply finRotate_due_ne hq i
    calc
      finRotate q (finRotate q i) = finRotate q j := by rw [hj]
      _ = i := hji
  have hpointR : punto P.asFinite v DP j ∈ DP.faccetta i := by
    simpa only [hji] using (punto_spec P.asFinite v DP j).2.2
  have hlevelOld : {y ∈ DP.faccetta i | phi y = phi v} =
      DP.faccetta i ∩ DP.faccetta (finRotate q i) :=
    hlevelP.trans hsegP.symm
  have hphir : 0 < phi r := by
    exact funzionale_positivo_su_dir DP i j j phi (DP.mem_v i) hpointR
      (punto_spec P.asFinite v DP j).2.1 hlowerP hlevelOld hjne hjneNext
  have hrot1ne0 : finRotate q (1 : Fin q) ≠ 0 := by
    intro h
    apply finRotate_due_ne hq (0 : Fin q)
    simpa only [hrot01] using h
  have hrot1ne1 : finRotate q (1 : Fin q) ≠ 1 :=
    _root_.finRotate_ne_self (by omega : 2 ≤ q) 1
  have hlevelEP : {y ∈ DP.faccetta i | phi y = phi v} =
      EP.faccetta 0 ∩ EP.faccetta (finRotate q 0) :=
    hlevelP.trans hedgeEP.symm
  have hlevelEPw : {y ∈ DP.faccetta i | phi y = phi w} =
      EP.faccetta 0 ∩ EP.faccetta (finRotate q 0) := by
    simpa only [← hphiEdge] using hlevelEP
  have hpointZ : punto P.asFinite w EP 1 ∈ DP.faccetta i := by
    simpa only [hEP1] using (punto_spec P.asFinite w EP 1).2.1
  have hphiz : 0 < phi z := by
    exact funzionale_positivo_su_dir EP 0 1 (finRotate q 1) phi
      (by simpa only [hEP1] using EP.mem_v 1) hpointZ
      (punto_spec P.asFinite w EP 1).2.2
      (by simpa only [hEP1, ← hphiEdge] using hlowerP) hlevelEPw hrot1ne0
      (by simpa only [hrot01] using hrot1ne1)
  have hlevelEQ : {y ∈ DQ.faccetta i | phi y = phi v} =
      EQ.faccetta 0 ∩ EQ.faccetta (finRotate q 0) :=
    hlevelQ.trans hedgeEQ.symm
  have hlevelEQw : {y ∈ DQ.faccetta i | phi y = phi w} =
      EQ.faccetta 0 ∩ EQ.faccetta (finRotate q 0) := by
    simpa only [← hphiEdge] using hlevelEQ
  have hpointZ' : punto Q.asFinite w EQ 1 ∈ DQ.faccetta i := by
    simpa only [hEQ1] using (punto_spec Q.asFinite w EQ 1).2.1
  have hphiz' : 0 < phi z' := by
    exact funzionale_positivo_su_dir EQ 0 1 (finRotate q 1) phi
      (by simpa only [hEQ1] using EQ.mem_v 1) hpointZ'
      (punto_spec Q.asFinite w EQ 1).2.2
      (by simpa only [hEQ1, ← hphiEdge] using hlowerQ) hlevelEQw hrot1ne0
      (by simpa only [hrot01] using hrot1ne1)
  have huSpan : u ∈ vectorSpan Real (DP.faccetta i) := by
    have hmem := dir_mem_vectorSpan_faccetta_destra EP (0 : Fin q)
    simpa only [u, hrot01, hEP1] using hmem
  have hrSpan : r ∈ vectorSpan Real (DP.faccetta i) := by
    have hmem := dir_mem_vectorSpan_faccetta_destra DP j
    simpa only [r, hji] using hmem
  have hspanP : vectorSpan Real (DP.faccetta i) =
      Submodule.span Real ({u, r} : Set (E 3)) :=
    vectorSpan_eq_span_vettori huSpan hrSpan hind (DP.isFacet i).2
  have hzVec : z ∈ vectorSpan Real (DP.faccetta i) := by
    have hmem := dir_mem_vectorSpan_faccetta_sinistra EP (1 : Fin q)
    simpa only [z, hEP1] using hmem
  have hzVec' : z' ∈ vectorSpan Real (DQ.faccetta i) := by
    have hmem := dir_mem_vectorSpan_faccetta_sinistra EQ (1 : Fin q)
    simpa only [z', hEQ1] using hmem
  have hvectorPlane : vectorSpan Real (DP.faccetta i) =
      vectorSpan Real (DQ.faccetta i) := by
    have hdirection := congrArg AffineSubspace.direction hpiano
    simpa only [direction_affineSpan] using hdirection
  have hzSpan : z ∈ Submodule.span Real ({u, r} : Set (E 3)) := by
    rw [← hspanP]
    exact hzVec
  have hzSpan' : z' ∈ Submodule.span Real ({u, r} : Set (E 3)) := by
    rw [← hspanP, hvectorPlane]
    exact hzVec'
  have hangP := inner_direzioni_consecutive P.asFinite hP hwP EP (0 : Fin q)
  have hangQ := inner_direzioni_consecutive Q.asFinite hQ hwQ EQ (0 : Fin q)
  have hang : ⟪u, z⟫ = ⟪u, z'⟫ := by
    calc
      ⟪u, z⟫ = cosFacciale p := by simpa only [u, z, hrot01] using hangP
      _ = ⟪dir Q.asFinite w EQ 0, z'⟫ := by
        simpa only [z', hrot01] using hangQ.symm
      _ = ⟪u, z'⟫ := by simpa only [u, hzero]
  have huno : z = z' := raggio_unico_da_semipiano_lineare
    (dir_unitaria P.asFinite w EP 0)
    (dir_unitaria P.asFinite w EP 1)
    (dir_unitaria Q.asFinite w EQ 1) hind phi hphiu hphir hphiz hphiz'
    hzSpan hzSpan' hang
  exact ⟨w, hwP, hwQ, EP, EQ, hzero, huno⟩

/-- The remaining orientation datum requested by
`fan_geometrico_marcato_unico`.  It is deliberately isolated from the
edge/plane/half-plane argument above. -/
def orientazione_compatibile (P Q : ConvexPolytope 3) (q : Nat)
    (hq : 3 ≤ q) : Prop :=
  ∀ (w : E 3) (_hwP : w ∈ P.vertices) (_hwQ : w ∈ Q.vertices)
    (EP : P.asFinite.CyclicVertexData w q)
    (EQ : Q.asFinite.CyclicVertexData w q) (k : Fin q),
    k ≠ (⟨0, by omega⟩ : Fin q) →
    k ≠ (⟨1, by omega⟩ : Fin q) →
    0 < volumeTre
        (dir P.asFinite w EP (⟨0, by omega⟩ : Fin q))
        (dir P.asFinite w EP (⟨1, by omega⟩ : Fin q))
        (dir P.asFinite w EP k) *
      volumeTre
        (dir Q.asFinite w EQ (⟨0, by omega⟩ : Fin q))
        (dir Q.asFinite w EQ (⟨1, by omega⟩ : Fin q))
        (dir Q.asFinite w EQ k)

/-- Inductive step for marked vertex fans.  All geometric ingredients are
proved above; `horient` is exactly the independent `volumeTre` orientation
condition of the final marked-fan uniqueness theorem. -/
theorem ventagli_uguali_al_vicino (P Q : ConvexPolytope 3) {p q : Nat}
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (hQ : Q.asFinite.IsCyclicallyRegularOfType p q)
    {v : E 3} (hvP : v ∈ P.vertices) (hvQ : v ∈ Q.vertices)
    (DP : P.asFinite.CyclicVertexData v q)
    (DQ : Q.asFinite.CyclicVertexData v q)
    (hdir : dir P.asFinite v DP = dir Q.asFinite v DQ)
    (hdiam : ∀ k, Metric.diam
        (DP.faccetta k ∩ DP.faccetta (finRotate q k)) =
      Metric.diam (DQ.faccetta k ∩ DQ.faccetta (finRotate q k)))
    (horient : orientazione_compatibile P Q q hP.2.2.1)
    (i : Fin q) :
    ∃ (w : E 3) (hwP : w ∈ P.vertices) (hwQ : w ∈ Q.vertices)
      (EP : P.asFinite.CyclicVertexData w q)
      (EQ : Q.asFinite.CyclicVertexData w q),
      dir P.asFinite w EP = dir Q.asFinite w EQ := by
  have hq : 3 ≤ q := hP.2.2.1
  haveI : NeZero q := ⟨by
    omega⟩
  obtain ⟨w, hwP, hwQ, EP, EQ, hzero, huno⟩ :=
    due_raggi_comuni_al_vicino P Q hP hQ hvP hvQ DP DQ hdir hdiam i
  have hstesso : ∀ k, k ≠ 0 → k ≠ 1 →
      0 < volumeTre (dir P.asFinite w EP 0) (dir P.asFinite w EP 1)
          (dir P.asFinite w EP k) *
        volumeTre (dir Q.asFinite w EQ 0) (dir Q.asFinite w EQ 1)
          (dir Q.asFinite w EQ k) := by
    intro k hk0 hk1
    have hZero : (0 : Fin q) = (⟨0, by omega⟩ : Fin q) := by
      apply Fin.ext
      simp [Fin.coe_ofNat_eq_mod]
    have hOne : (1 : Fin q) = (⟨1, by omega⟩ : Fin q) := by
      apply Fin.ext
      have hmod : 1 % q = 1 := Nat.mod_eq_of_lt (by omega)
      simp [Fin.coe_ofNat_eq_mod, hmod]
    simpa only [hZero, hOne] using horient w hwP hwQ EP EQ k
      (by simpa using hk0) (by
      intro hk
      apply hk1
      apply Fin.ext
      have hval := congrArg Fin.val hk
      have hmod : 1 % q = 1 := Nat.mod_eq_of_lt (by omega)
      simpa [Fin.coe_ofNat_eq_mod, hmod] using hval)
  have hfan := fan_geometrico_marcato_unico P Q hP hQ hwP hwQ EP EQ
    hzero huno hstesso
  exact ⟨w, hwP, hwQ, EP, EQ, hfan⟩

-- NON RIUSCITO: eliminare l'ipotesi `orientazione_compatibile`, perche' i
-- lemmi certificati determinano spigolo, piano e semipiano della faccetta ma
-- non trasferiscono ancora il lato tridimensionale (`volumeTre`) del corpo
-- attraverso lo spigolo comune.  Il teorema `due_raggi_comuni_al_vicino`
-- chiude integralmente e senza questa ipotesi i punti 1--4.

end LeanEval.Geometry.PlatonicClassification
