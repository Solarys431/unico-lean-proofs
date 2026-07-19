import Mathlib
import Solution.ScalaTipo
import Solution.TrasportoFinale
import Solution.RaggiTrasporto

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

theorem cyclicVertexData_scala_esplicito (P : ConvexPolytope 3)
    {a : Real} (ha : 0 < a) {v : E 3} {q : Nat}
    (D : P.asFinite.CyclicVertexData v q) :
    Exists fun D' : (scala a (ne_of_gt ha) P).asFinite.CyclicVertexData
        (SMul.smul a v) q =>
      forall i : Fin q,
        D'.faccetta i =
          (fun x : E 3 => SMul.smul a x) '' D.faccetta i := by
  classical
  have hane : Not (a = 0) := ne_of_gt ha
  have hinj_smul : Function.Injective (fun x : E 3 => SMul.smul a x) :=
    smul_right_injective (E 3) hane
  have hinj_img : Function.Injective
      (Set.image (fun x : E 3 => SMul.smul a x)) :=
    Set.image_injective.mpr hinj_smul
  cases D with
  | mk faccetta isFacet mem_v distinte complete sigma fissa_v preserva
      ruota spigolo spigolo_due =>
    refine Exists.intro ?_ ?_
    apply FiniteConvexPolytope.CyclicVertexData.mk
      (fun i => (fun x : E 3 => SMul.smul a x) '' faccetta i)
      (fun i => isFacet_scala hane (isFacet i))
      (fun i => Exists.intro v (And.intro (mem_v i) rfl))
      (fun _ _ hij => distinte (hinj_img hij))
      ?_
      (coniugioScala a hane sigma)
      ?_
      ?_
      ?_
      ?_
      ?_
    . intro F hF hvF
      have hback := isFacet_of_scala hane hF
      have hfacetP := hback.1
      have hround := hback.2
      have hvmem : ((fun x : E 3 => SMul.smul (Inv.inv a) x) '' F) v := by
        refine Exists.intro (SMul.smul a v) (And.intro hvF ?_)
        show SMul.smul (Inv.inv a) (SMul.smul a v) = v
        exact (omotetia a hane).symm_apply_apply v
      have hex := complete _ hfacetP hvmem
      have hFi := Classical.choose_spec hex
      apply Exists.intro (Classical.choose hex)
      calc
        F = (fun x : E 3 => SMul.smul a x) ''
              ((fun x : E 3 => SMul.smul (Inv.inv a) x) '' F) := hround
        _ = (fun x : E 3 => SMul.smul a x) ''
              faccetta (Classical.choose hex) :=
            congrArg (Set.image (fun x : E 3 => SMul.smul a x)) hFi
    . change coniugioScala a hane sigma (SMul.smul a v) = SMul.smul a v
      calc
        coniugioScala a hane sigma (SMul.smul a v) =
            SMul.smul a (sigma v) := coniugioScala_smul a hane sigma v
        _ = SMul.smul a v :=
          congrArg (fun z : E 3 => SMul.smul a z) fissa_v
    . rw [toSet_scala_finite a hane P]
      calc
        (fun x : E 3 => coniugioScala a hane sigma x) ''
              ((fun x : E 3 => SMul.smul a x) '' P.asFinite.toSet) =
            (fun x : E 3 =>
              coniugioScala a hane sigma (SMul.smul a x)) ''
              P.asFinite.toSet := Set.image_image _ _ _
        _ = (fun x : E 3 => SMul.smul a (sigma x)) ''
              P.asFinite.toSet := by
            have hcomp :
                (fun x : E 3 =>
                  coniugioScala a hane sigma (SMul.smul a x)) =
                fun x : E 3 => SMul.smul a (sigma x) := by
              funext z
              exact coniugioScala_smul a hane sigma z
            rw [hcomp]
        _ = (fun x : E 3 => SMul.smul a x) ''
              ((fun x : E 3 => sigma x) '' P.asFinite.toSet) :=
            (Set.image_image _ _ _).symm
        _ = (fun x : E 3 => SMul.smul a x) '' P.asFinite.toSet := by
            rw [preserva]
    . intro i
      calc
        (fun x : E 3 => coniugioScala a hane sigma x) ''
              ((fun x : E 3 => SMul.smul a x) '' faccetta i) =
            (fun x : E 3 =>
              coniugioScala a hane sigma (SMul.smul a x)) ''
              faccetta i := Set.image_image _ _ _
        _ = (fun x : E 3 => SMul.smul a (sigma x)) '' faccetta i := by
            have hcomp :
                (fun x : E 3 =>
                  coniugioScala a hane sigma (SMul.smul a x)) =
                fun x : E 3 => SMul.smul a (sigma x) := by
              funext z
              exact coniugioScala_smul a hane sigma z
            rw [hcomp]
        _ = (fun x : E 3 => SMul.smul a x) ''
              ((fun x : E 3 => sigma x) '' faccetta i) :=
            (Set.image_image _ _ _).symm
        _ = (fun x : E 3 => SMul.smul a x) ''
              faccetta (finRotate q i) := by
            rw [ruota i]
    . intro i
      have hex := spigolo i
      let x := Classical.choose hex
      have hxall := Classical.choose_spec hex
      have hxv := hxall.1
      have hx := hxall.2
      refine Exists.intro (SMul.smul a x) (And.intro ?_
        (And.intro
          (Exists.intro x (And.intro hx.1 rfl))
          (Exists.intro x (And.intro hx.2 rfl))))
      intro hcontra
      exact hxv (hinj_smul hcontra)
    . intro i j x hx hxv hxj
      let y1 := Classical.choose hx.1
      have hy1all := Classical.choose_spec hx.1
      have hy1 := hy1all.1
      have hxy1 := hy1all.2
      let y2 := Classical.choose hx.2
      have hy2all := Classical.choose_spec hx.2
      have hy2 := hy2all.1
      have hxy2 := hy2all.2
      have hxy1' : SMul.smul a y1 = x := hxy1
      have hxy2' : SMul.smul a y2 = x := hxy2
      have hy12 : y1 = y2 := by
        apply hinj_smul
        show SMul.smul a y1 = SMul.smul a y2
        rw [hxy1', hxy2']
      let y3 := Classical.choose hxj
      have hy3all := Classical.choose_spec hxj
      have hy3 := hy3all.1
      have hxy3 := hy3all.2
      have hxy3' : SMul.smul a y3 = x := hxy3
      have hy13 : y1 = y3 := by
        apply hinj_smul
        show SMul.smul a y1 = SMul.smul a y3
        rw [hxy1', hxy3']
      have hyv : Not (y1 = v) := by
        intro hcontra
        apply hxv
        calc
          x = SMul.smul a y1 := hxy1'.symm
          _ = SMul.smul a v := congrArg (fun z : E 3 => SMul.smul a z) hcontra
      refine spigolo_due i j y1 (And.intro hy1 ?_) hyv ?_
      . rw [hy12]
        exact hy2
      . rw [hy13]
        exact hy3
    . intro i
      rfl

theorem cyclicVertexData_muovi_esplicito (P : ConvexPolytope 3)
    (g : Isom 3) {v : E 3} {q : Nat}
    (D : P.asFinite.CyclicVertexData v q) :
    Exists fun D' : (muovi g P).asFinite.CyclicVertexData (g v) q =>
      forall i : Fin q, D'.faccetta i = (fun x : E 3 => g x) '' D.faccetta i := by
  classical
  cases D with
  | mk faccetta isFacet mem_v distinte complete sigma fissa_v preserva
      ruota spigolo spigolo_due =>
    have hinj_g : Function.Injective (fun x : E 3 => g x) := g.injective
    have hinj_img : Function.Injective (Set.image (fun x : E 3 => g x)) :=
      Set.image_injective.mpr hinj_g
    refine Exists.intro ?_ ?_
    apply FiniteConvexPolytope.CyclicVertexData.mk
      (fun i => (fun x : E 3 => g x) '' faccetta i)
      (fun i => isFacet_muovi g (isFacet i))
      (fun i => Set.mem_image_of_mem g (mem_v i))
      (fun _ _ hij => distinte (hinj_img hij))
      ?_
      ((g.symm.trans sigma).trans g)
      ?_
      ?_
      ?_
      ?_
      ?_
    . intro F hF hvF
      have hback := isFacet_of_muovi g hF
      have hfacetP := hback.1
      have hround := hback.2
      have hvmem : ((fun x : E 3 => g.symm x) '' F) v := by
        exact Exists.intro (g v) (And.intro hvF (by simp))
      have hex := complete _ hfacetP hvmem
      let i := Classical.choose hex
      have hFi := Classical.choose_spec hex
      apply Exists.intro i
      rw [hround, hFi]
    . simp [fissa_v]
    . rw [toSet_muovi_finite g P]
      calc
        (fun x : E 3 => ((g.symm.trans sigma).trans g) x) ''
              ((fun x : E 3 => g x) '' P.asFinite.toSet) =
            (fun x : E 3 => ((g.symm.trans sigma).trans g) (g x)) ''
              P.asFinite.toSet := Set.image_image _ _ _
        _ = (fun x : E 3 => g (sigma x)) '' P.asFinite.toSet := by
            congr 1
            funext x
            simp
        _ = (fun x : E 3 => g x) ''
              ((fun x : E 3 => sigma x) '' P.asFinite.toSet) :=
            (Set.image_image _ _ _).symm
        _ = (fun x : E 3 => g x) '' P.asFinite.toSet := by
            rw [preserva]
    . intro i
      calc
        (fun x : E 3 => ((g.symm.trans sigma).trans g) x) ''
              ((fun x : E 3 => g x) '' faccetta i) =
            (fun x : E 3 => ((g.symm.trans sigma).trans g) (g x)) ''
              faccetta i := Set.image_image _ _ _
        _ = (fun x : E 3 => g (sigma x)) '' faccetta i := by
            congr 1
            funext x
            simp
        _ = (fun x : E 3 => g x) ''
              ((fun x : E 3 => sigma x) '' faccetta i) :=
            (Set.image_image _ _ _).symm
        _ = (fun x : E 3 => g x) '' faccetta (finRotate q i) := by
            rw [ruota i]
    . intro i
      have hex := spigolo i
      let x := Classical.choose hex
      have hx := Classical.choose_spec hex
      apply Exists.intro (g x)
      apply And.intro
      . intro h
        exact hx.1 (hinj_g h)
      . exact And.intro (Set.mem_image_of_mem g hx.2.1)
          (Set.mem_image_of_mem g hx.2.2)
    . intro i j x hx hxv hxj
      let y1 := Classical.choose hx.1
      have hy1 := Classical.choose_spec hx.1
      let y2 := Classical.choose hx.2
      have hy2 := Classical.choose_spec hx.2
      have hy12 : y1 = y2 := hinj_g (hy1.2.trans hy2.2.symm)
      let y3 := Classical.choose hxj
      have hy3 := Classical.choose_spec hxj
      have hy13 : y1 = y3 := hinj_g (hy1.2.trans hy3.2.symm)
      have hyv : Not (y1 = v) := by
        intro h
        apply hxv
        calc
          x = g y1 := hy1.2.symm
          _ = g v := congrArg g h
      apply spigolo_due i j y1
      . apply And.intro hy1.1
        rw [hy12]
        exact hy2.1
      . exact hyv
      . rw [hy13]
        exact hy3.1
    . intro i
      rfl

theorem dir_scala_eq (P : ConvexPolytope 3) {p q : Nat}
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    {a : Real} (ha : 0 < a) {v : E 3} (hv : Membership.mem P.vertices v)
    (D : P.asFinite.CyclicVertexData v q)
    (D' : (scala a (ne_of_gt ha) P).asFinite.CyclicVertexData
      (SMul.smul a v) q)
    (hfacce : forall i,
      D'.faccetta i = (fun x : E 3 => SMul.smul a x) '' D.faccetta i)
    (i : Fin q) :
    dir (scala a (ne_of_gt ha) P).asFinite (SMul.smul a v) D' i =
      dir P.asFinite v D i := by
  classical
  let x := punto P.asFinite v D i
  have hx := punto_spec P.asFinite v D i
  have hv' : Membership.mem (scala a (ne_of_gt ha) P).vertices
      (SMul.smul a v) := by
    exact Finset.mem_image_of_mem (fun z : E 3 => SMul.smul a z) hv
  have hx' :
      D'.faccetta i (SMul.smul a x) /\
        D'.faccetta (finRotate q i) (SMul.smul a x) := by
    constructor
    . rw [hfacce i]
      exact Exists.intro x (And.intro hx.2.1 rfl)
    . rw [hfacce (finRotate q i)]
      exact Exists.intro x (And.intro hx.2.2 rfl)
  have hxv' : Not (SMul.smul a x = SMul.smul a v) := by
    intro h
    exact hx.1 ((smul_right_injective (E 3) (ne_of_gt ha)) h)
  have hd := dir_da_qualunque_punto
    (scala a (ne_of_gt ha) P) (cyclicallyRegular_scala P ha hP)
    hv' D' i hx' hxv'
  calc
    dir (scala a (ne_of_gt ha) P).asFinite (SMul.smul a v) D' i =
        SMul.smul (Inv.inv (norm (SMul.smul a x - SMul.smul a v)))
          (SMul.smul a x - SMul.smul a v) := hd.symm
    _ = SMul.smul (Inv.inv (norm (SMul.smul a (x - v))))
          (SMul.smul a (x - v)) := by
      have hsub : SMul.smul a (x - v) =
          SMul.smul a x - SMul.smul a v := smul_sub a x v
      rw [hsub]
    _ = SMul.smul (Inv.inv (norm (x - v))) (x - v) :=
      dir_smul_invariante ha (sub_ne_zero.mpr hx.1)
    _ = dir P.asFinite v D i := rfl

theorem dir_muovi_eq (P : ConvexPolytope 3) {p q : Nat}
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (g : Isom 3) {v : E 3} (hv : Membership.mem P.vertices v)
    (D : P.asFinite.CyclicVertexData v q)
    (D' : (muovi g P).asFinite.CyclicVertexData (g v) q)
    (hfacce : forall i,
      D'.faccetta i = (fun x : E 3 => g x) '' D.faccetta i)
    (i : Fin q) :
    dir (muovi g P).asFinite (g v) D' i =
      g.linearIsometryEquiv (dir P.asFinite v D i) := by
  classical
  let x := punto P.asFinite v D i
  have hx := punto_spec P.asFinite v D i
  have hv' : Membership.mem (muovi g P).vertices (g v) :=
    mem_vertices_muovi g P hv
  have hx' :
      D'.faccetta i (g x) /\
        D'.faccetta (finRotate q i) (g x) := by
    constructor
    . rw [hfacce i]
      exact Set.mem_image_of_mem g hx.2.1
    . rw [hfacce (finRotate q i)]
      exact Set.mem_image_of_mem g hx.2.2
  have hxv' : Not (g x = g v) := g.injective.ne hx.1
  have hd := dir_da_qualunque_punto
    (muovi g P) (cyclicallyRegular_muovi P g hP) hv' D' i hx' hxv'
  calc
    dir (muovi g P).asFinite (g v) D' i =
        SMul.smul (Inv.inv (norm (g x - g v))) (g x - g v) := hd.symm
    _ = g.linearIsometryEquiv
          (SMul.smul (Inv.inv (norm (x - v))) (x - v)) :=
      dir_isom_lineare g v x
    _ = g.linearIsometryEquiv (dir P.asFinite v D i) := rfl

end LeanEval.Geometry.PlatonicClassification
