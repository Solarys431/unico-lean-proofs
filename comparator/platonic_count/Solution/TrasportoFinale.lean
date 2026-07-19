import Mathlib
import Solution.MuoviTipo
import Solution.ScalaFacce

open Set
open scoped Pointwise

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- Iterating a conjugated isometry commutes with the transporting map. -/
theorem conjugate_isom_iterate (g rho : Isom 3) (x : E 3) (n : Nat) :
    Nat.iterate (fun z : E 3 => ((g.symm.trans rho).trans g) z) n
        (g x) =
      g (Nat.iterate (fun z : E 3 => rho z) n x) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      simp

/-- Cyclic vertex data is transported by an isometry. -/
theorem cyclicVertexData_muovi (P : ConvexPolytope 3) (g : Isom 3)
    {v : E 3} {q : Nat} (D : P.asFinite.CyclicVertexData v q) :
    Nonempty ((muovi g P).asFinite.CyclicVertexData (g v) q) := by
  classical
  cases D with
  | mk faccetta isFacet mem_v distinte complete sigma fissa_v preserva
      ruota spigolo spigolo_due =>
    have hinj_g : Function.Injective (fun x : E 3 => g x) := g.injective
    have hinj_img : Function.Injective (Set.image (fun x : E 3 => g x)) :=
      Set.image_injective.mpr hinj_g
    apply Nonempty.intro
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
        ((fun x : E 3 => ((g.symm.trans sigma).trans g) x) ''
            ((fun x : E 3 => g x) '' P.asFinite.toSet)) =
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
        ((fun x : E 3 => ((g.symm.trans sigma).trans g) x) ''
            ((fun x : E 3 => g x) '' faccetta i)) =
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

/-- Positive homotheties multiply metric diameter by their ratio. -/
theorem diam_smul_image (a : Real) (ha : 0 < a) (s : Set (E 3)) :
    Metric.diam ((fun x : E 3 => SMul.smul a x) '' s) =
      a * Metric.diam s := by
  let r : NNReal := Subtype.mk a (le_of_lt ha)
  have hr0 : Not (r = 0) := by
    intro h
    have hcoe := congrArg (fun z : NNReal => z.val) h
    change a = 0 at hcoe
    exact (ne_of_gt ha) hcoe
  have hscale : forall x y : E 3,
      dist (SMul.smul a x) (SMul.smul a y) = a * dist x y := by
    intro x y
    exact dist_smul_pos ha x y
  have hscale_r : forall x y : E 3,
      dist (SMul.smul a x) (SMul.smul a y) = (r : Real) * dist x y := by
    intro x y
    change dist (SMul.smul a x) (SMul.smul a y) = a * dist x y
    exact hscale x y
  let dil : Dilation (E 3) (E 3) :=
    Dilation.mkOfDistEq (fun x : E 3 => SMul.smul a x)
      (Exists.intro r (And.intro hr0 hscale_r))
  have hpair := exists_pair_ne (E 3)
  let x := Classical.choose hpair
  have hx : Exists (fun y : E 3 => Not (x = y)) := Classical.choose_spec hpair
  let y := Classical.choose hx
  have hxy : Not (x = y) := Classical.choose_spec hx
  have hratio : r = Dilation.ratio dil :=
    Dilation.ratio_unique_of_dist_ne_zero (f := dil) (r := r)
      (dist_ne_zero.mpr hxy) (by simpa [dil] using hscale_r x y)
  calc
    Metric.diam ((fun z : E 3 => SMul.smul a z) '' s) =
        (Dilation.ratio dil : Real) * Metric.diam s := by
          simpa [dil] using Dilation.diam_image dil s
    _ = (r : Real) * Metric.diam s := by rw [hratio.symm]
    _ = a * Metric.diam s := by rfl

/-- A regular facet is transported by an isometry, with unchanged side. -/
theorem isRegularFacet_muovi (P : ConvexPolytope 3) (g : Isom 3)
    {A : Set (E 3)} {p : Nat} {l : Real}
    (h : P.asFinite.IsRegularFacet A p l) :
    (muovi g P).asFinite.IsRegularFacet
      ((fun x : E 3 => g x) '' A) p l := by
  classical
  have hFacet := h.1
  have hl := h.2.1
  have hp := h.2.2.1
  have hex := h.2.2.2
  let rho := Classical.choose hex
  have hrho := Classical.choose_spec hex
  let x0 := Classical.choose hrho
  have hx0 := Classical.choose_spec hrho
  have hx0A := hx0.1
  have hrhoA := hx0.2.1
  have horbit := hx0.2.2.1
  have hclose := hx0.2.2.2.1
  have hhull := hx0.2.2.2.2.1
  have hdist := hx0.2.2.2.2.2
  apply And.intro (isFacet_muovi g hFacet)
  apply And.intro hl
  apply And.intro hp
  apply Exists.intro ((g.symm.trans rho).trans g)
  apply Exists.intro (g x0)
  apply And.intro (Set.mem_image_of_mem g hx0A)
  apply And.intro
  . calc
      ((fun z : E 3 => ((g.symm.trans rho).trans g) z) ''
          ((fun z : E 3 => g z) '' A)) =
          (fun z : E 3 => ((g.symm.trans rho).trans g) (g z)) '' A :=
            Set.image_image _ _ _
      _ = (fun z : E 3 => g (rho z)) '' A := by
          congr 1
          funext z
          simp
      _ = (fun z : E 3 => g z) ''
          ((fun z : E 3 => rho z) '' A) :=
            (Set.image_image _ _ _).symm
      _ = (fun z : E 3 => g z) '' A := by rw [hrhoA]
  apply And.intro
  . intro i j hij
    apply horbit
    apply g.injective
    calc
      g (Nat.iterate (fun z : E 3 => rho z) (i : Nat) x0) =
          Nat.iterate
            (fun z : E 3 => ((g.symm.trans rho).trans g) z)
            (i : Nat) (g x0) := (conjugate_isom_iterate g rho x0 i).symm
      _ = Nat.iterate
            (fun z : E 3 => ((g.symm.trans rho).trans g) z)
            (j : Nat) (g x0) := hij
      _ = g (Nat.iterate (fun z : E 3 => rho z) (j : Nat) x0) :=
            conjugate_isom_iterate g rho x0 j
  apply And.intro
  . calc
      Nat.iterate (fun z : E 3 => ((g.symm.trans rho).trans g) z) p
          (g x0) =
          g (Nat.iterate (fun z : E 3 => rho z) p x0) :=
            conjugate_isom_iterate g rho x0 p
      _ = g x0 := congrArg g hclose
  apply And.intro
  . let originalOrbit : Set (E 3) :=
      Set.range (fun i : Fin p =>
        Nat.iterate (fun z : E 3 => rho z) (i : Nat) x0)
    let movedOrbit : Set (E 3) :=
      Set.range (fun i : Fin p =>
        Nat.iterate
          (fun z : E 3 => ((g.symm.trans rho).trans g) z)
          (i : Nat) (g x0))
    have hrange : movedOrbit = (fun z : E 3 => g z) '' originalOrbit := by
      apply Set.ext
      intro z
      constructor
      . intro hz
        let i := Classical.choose hz
        have hi := Classical.choose_spec hz
        let y := Nat.iterate (fun w : E 3 => rho w) (i : Nat) x0
        apply Exists.intro y
        apply And.intro
        . exact Exists.intro i rfl
        . calc
            g y = Nat.iterate
                (fun w : E 3 => ((g.symm.trans rho).trans g) w)
                (i : Nat) (g x0) :=
                  (conjugate_isom_iterate g rho x0 i).symm
            _ = z := hi
      . intro hz
        let y := Classical.choose hz
        have hy := Classical.choose_spec hz
        let i := Classical.choose hy.1
        have hi := Classical.choose_spec hy.1
        apply Exists.intro i
        calc
          Nat.iterate
              (fun w : E 3 => ((g.symm.trans rho).trans g) w)
              (i : Nat) (g x0) =
              g (Nat.iterate (fun w : E 3 => rho w) (i : Nat) x0) :=
                conjugate_isom_iterate g rho x0 i
          _ = g y := congrArg g hi
          _ = z := hy.2
    have himage := g.toAffineEquiv.toAffineMap.image_convexHull originalOrbit
    have hco :
        (g.toAffineEquiv.toAffineMap : E 3 -> E 3) = (fun z : E 3 => g z) :=
      rfl
    rw [hco] at himage
    change ((fun z : E 3 => g z) '' A) = convexHull Real movedOrbit
    calc
      (fun z : E 3 => g z) '' A =
          (fun z : E 3 => g z) '' convexHull Real originalOrbit := by
            rw [hhull]
      _ = convexHull Real ((fun z : E 3 => g z) '' originalOrbit) := himage
      _ = convexHull Real movedOrbit := by rw [hrange]
  . calc
      dist (g x0) (((g.symm.trans rho).trans g) (g x0)) =
          dist (g x0) (g (rho x0)) := by simp
      _ = dist x0 (rho x0) := g.dist_map x0 (rho x0)
      _ = l := hdist

/-- The full cyclic regular type is invariant under an isometry. -/
theorem cyclicallyRegular_muovi (P : ConvexPolytope 3) (g : Isom 3)
    {p q : Nat} (h : P.asFinite.IsCyclicallyRegularOfType p q) :
    (muovi g P).asFinite.IsCyclicallyRegularOfType p q := by
  classical
  have hrank := h.1
  have hp := h.2.1
  have hq := h.2.2.1
  have hex := h.2.2.2
  let l := Classical.choose hex
  have hlrest := Classical.choose_spec hex
  have hl := hlrest.1
  have hfacets := hlrest.2.1
  have hvertices := hlrest.2.2
  apply And.intro
  . have hset :
        (((muovi g P).vertices : Finset (E 3)) : Set (E 3)) =
          (fun x : E 3 => g x) ''
            ((P.vertices : Finset (E 3)) : Set (E 3)) := by
      show ((P.vertices.image (fun x : E 3 => g x) : Finset (E 3)) :
          Set (E 3)) = _
      apply Set.ext
      intro x
      simp
    show Module.finrank Real (vectorSpan Real
      (((muovi g P).vertices : Finset (E 3)) : Set (E 3))) = 3
    rw [hset]
    show faceDim ((fun x : E 3 => g x) ''
      ((P.vertices : Finset (E 3)) : Set (E 3))) = 3
    rw [faceDim_image_isom]
    exact hrank
  apply And.intro hp
  apply And.intro hq
  apply Exists.intro l
  apply And.intro hl
  apply And.intro
  . intro F hF
    have hback := isFacet_of_muovi g hF
    have hreg := isRegularFacet_muovi P g (hfacets _ hback.1)
    have heq : (fun x : E 3 => g x) ''
        ((fun x : E 3 => g.symm x) '' F) = F :=
      image_isom_roundtrip g F
    rw [heq] at hreg
    exact hreg
  . intro w hw
    have hwback := (vertices_muovi_iff g).mp hw
    let v := Classical.choose hwback
    have hvrest := Classical.choose_spec hwback
    have hv := hvrest.1
    have hvw := hvrest.2
    have hdata := hvertices v hv
    let D := Classical.choice hdata
    have hmoved := cyclicVertexData_muovi P g D
    show Nonempty ((muovi g P).asFinite.CyclicVertexData w q)
    rw [hvw] at hmoved
    exact hmoved

end LeanEval.Geometry.PlatonicClassification
