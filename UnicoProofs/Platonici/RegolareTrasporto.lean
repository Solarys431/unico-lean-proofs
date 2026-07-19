import UnicoProofs.Platonici.ScalaFacce
import UnicoProofs.Platonici.MuoviTipo
import UnicoProofs.Platonici.SimilarEquiv

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

theorem isFace_of_muovi_regular {P : ConvexPolytope 3} (g : Isom 3)
    {G : Set (E 3)} (hG : (muovi g P).IsFace G) :
    P.IsFace ((fun x : E 3 => g.symm x) '' G) /\
      G = (fun x : E 3 => g x) ''
        ((fun x : E 3 => g.symm x) '' G) := by
  refine And.intro ?_ (image_isom_roundtrip g G).symm
  refine And.intro ?_ (hG.2.image _)
  have hP : P.toSet =
      (fun x : E 3 => g.symm x) '' (muovi g P).toSet := by
    rw [muovi_toSet]
    exact (g.toEquiv.symm_image_image P.toSet).symm
  rw [hP]
  exact isExposed_image_isom g.symm hG.1

theorem image_smul_strictMono {a : Real} (ha : Ne a 0) :
    StrictMono (fun F : Set (E 3) =>
      (fun x : E 3 => SMul.smul a x) '' F) := by
  intro F G hFG
  have hparts := Set.ssubset_iff_subset_ne.mp hFG
  have hsub := hparts.1
  have hne := hparts.2
  apply Set.ssubset_iff_subset_ne.mpr
  refine And.intro (Set.image_mono hsub) ?_
  intro heq
  apply hne
  apply (Set.image_injective.mpr ?_) heq
  change Function.Injective (fun x : E 3 => omotetia a ha x)
  exact (omotetia a ha).injective

theorem image_isom_strictMono (g : Isom 3) :
    StrictMono (fun F : Set (E 3) => (fun x : E 3 => g x) '' F) := by
  intro F G hFG
  have hparts := Set.ssubset_iff_subset_ne.mp hFG
  have hsub := hparts.1
  have hne := hparts.2
  apply Set.ssubset_iff_subset_ne.mpr
  refine And.intro (Set.image_mono hsub) ?_
  intro heq
  exact hne ((Set.image_injective.mpr g.injective) heq)

theorem isRegular_scala (P : ConvexPolytope 3) {a : Real} (ha : 0 < a)
    (h : P.IsRegular) : (scala a (ne_of_gt ha) P).IsRegular := by
  let hane : Ne a 0 := ne_of_gt ha
  refine And.intro ?_ ?_
  . change Module.finrank Real (vectorSpan Real (scala a hane P).toSet) = 3
    rw [scala_toSet, finrank_vectorSpan_smul a hane]
    exact h.1
  . intro F G
    let pullF : P.Flag :=
      { face := fun k =>
          (fun x : E 3 => SMul.smul (Inv.inv a) x) '' F.face k
        isFace := by
          intro k
          exact (isFace_of_scala hane (F.isFace k)).1
        dim_eq := by
          intro k
          unfold faceDim
          exact (finrank_vectorSpan_smul (Inv.inv a) (inv_ne_zero hane)
            (F.face k)).trans (F.dim_eq k)
        strict_mono := by
          intro i j hij
          exact image_smul_strictMono (inv_ne_zero hane)
            (F.strict_mono i j hij) }
    let pullG : P.Flag :=
      { face := fun k =>
          (fun x : E 3 => SMul.smul (Inv.inv a) x) '' G.face k
        isFace := by
          intro k
          exact (isFace_of_scala hane (G.isFace k)).1
        dim_eq := by
          intro k
          unfold faceDim
          exact (finrank_vectorSpan_smul (Inv.inv a) (inv_ne_zero hane)
            (G.face k)).trans (G.dim_eq k)
        strict_mono := by
          intro i j hij
          exact image_smul_strictMono (inv_ne_zero hane)
            (G.strict_mono i j hij) }
    let hex := h.2 pullF pullG
    let phi := hex.choose
    have hphi := hex.choose_spec.1
    have hflags := hex.choose_spec.2
    refine Exists.intro (coniugioScala a hane phi) (And.intro ?_ ?_)
    . unfold ConvexPolytope.isSymmetry
      rw [scala_toSet]
      calc
        (fun x : E 3 => coniugioScala a hane phi x) ''
            ((fun x : E 3 => SMul.smul a x) '' P.toSet) =
            (fun x : E 3 =>
              coniugioScala a hane phi (SMul.smul a x)) ''
              P.toSet := Set.image_image _ _ _
        _ = (fun x : E 3 => SMul.smul a (phi x)) '' P.toSet := by
          congr 1
          funext x
          exact coniugioScala_smul a hane phi x
        _ = (fun x : E 3 => SMul.smul a x) ''
            ((fun x : E 3 => phi x) '' P.toSet) :=
          (Set.image_image _ _ _).symm
        _ = (fun x : E 3 => SMul.smul a x) '' P.toSet := by rw [hphi]
    . intro k
      have hflag := hflags k
      change (fun x : E 3 => phi x) ''
          ((fun x : E 3 => SMul.smul (Inv.inv a) x) '' F.face k) =
        (fun x : E 3 => SMul.smul (Inv.inv a) x) '' G.face k at hflag
      have hroundF := (isFace_of_scala hane (F.isFace k)).2
      have hroundG := (isFace_of_scala hane (G.isFace k)).2
      calc
        (fun x : E 3 => coniugioScala a hane phi x) '' F.face k =
            (fun x : E 3 => coniugioScala a hane phi x) ''
              ((fun x : E 3 => SMul.smul a x) ''
                ((fun x : E 3 => SMul.smul (Inv.inv a) x) ''
                  F.face k)) := by
          exact congrArg
            (fun A : Set (E 3) =>
              (fun x : E 3 => coniugioScala a hane phi x) '' A)
            hroundF
        _ = (fun x : E 3 =>
              coniugioScala a hane phi (SMul.smul a x)) ''
              ((fun x : E 3 => SMul.smul (Inv.inv a) x) '' F.face k) :=
          Set.image_image _ _ _
        _ = (fun x : E 3 => SMul.smul a (phi x)) ''
              ((fun x : E 3 => SMul.smul (Inv.inv a) x) '' F.face k) := by
          congr 1
          funext x
          exact coniugioScala_smul a hane phi x
        _ = (fun x : E 3 => SMul.smul a x) ''
              ((fun x : E 3 => phi x) ''
                ((fun x : E 3 => SMul.smul (Inv.inv a) x) '' F.face k)) :=
          (Set.image_image _ _ _).symm
        _ = (fun x : E 3 => SMul.smul a x) ''
              ((fun x : E 3 => SMul.smul (Inv.inv a) x) '' G.face k) := by
          rw [hflag]
        _ = G.face k := smul_image_roundtrip a hane (G.face k)

theorem isRegular_muovi (P : ConvexPolytope 3) (g : Isom 3)
    (h : P.IsRegular) : (muovi g P).IsRegular := by
  refine And.intro ?_ ?_
  . change faceDim (muovi g P).toSet = 3
    rw [muovi_toSet, faceDim_image_isom]
    exact h.1
  . intro F G
    let pullF : P.Flag :=
      { face := fun k => (fun x : E 3 => g.symm x) '' F.face k
        isFace := by
          intro k
          exact (isFace_of_muovi_regular g (F.isFace k)).1
        dim_eq := by
          intro k
          rw [faceDim_image_isom]
          exact F.dim_eq k
        strict_mono := by
          intro i j hij
          exact image_isom_strictMono g.symm (F.strict_mono i j hij) }
    let pullG : P.Flag :=
      { face := fun k => (fun x : E 3 => g.symm x) '' G.face k
        isFace := by
          intro k
          exact (isFace_of_muovi_regular g (G.isFace k)).1
        dim_eq := by
          intro k
          rw [faceDim_image_isom]
          exact G.dim_eq k
        strict_mono := by
          intro i j hij
          exact image_isom_strictMono g.symm (G.strict_mono i j hij) }
    let hex := h.2 pullF pullG
    let phi := hex.choose
    have hphi := hex.choose_spec.1
    have hflags := hex.choose_spec.2
    let psi : Isom 3 := (g.symm.trans phi).trans g
    refine Exists.intro psi (And.intro ?_ ?_)
    . unfold ConvexPolytope.isSymmetry
      rw [muovi_toSet]
      calc
        (fun x : E 3 => psi x) '' ((fun x : E 3 => g x) '' P.toSet) =
            (fun x : E 3 => psi (g x)) '' P.toSet :=
          Set.image_image _ _ _
        _ = (fun x : E 3 => g (phi x)) '' P.toSet := by
          congr 1
          funext x
          simp [psi]
        _ = (fun x : E 3 => g x) ''
            ((fun x : E 3 => phi x) '' P.toSet) :=
          (Set.image_image _ _ _).symm
        _ = (fun x : E 3 => g x) '' P.toSet := by rw [hphi]
    . intro k
      have hflag := hflags k
      change (fun x : E 3 => phi x) ''
          ((fun x : E 3 => g.symm x) '' F.face k) =
        (fun x : E 3 => g.symm x) '' G.face k at hflag
      have hroundF := (isFace_of_muovi_regular g (F.isFace k)).2
      have hroundG := (isFace_of_muovi_regular g (G.isFace k)).2
      calc
        (fun x : E 3 => psi x) '' F.face k =
            (fun x : E 3 => psi x) ''
              ((fun x : E 3 => g x) ''
                ((fun x : E 3 => g.symm x) '' F.face k)) := by
          exact congrArg
            (fun A : Set (E 3) => (fun x : E 3 => psi x) '' A)
            hroundF
        _ = (fun x : E 3 => psi (g x)) ''
              ((fun x : E 3 => g.symm x) '' F.face k) :=
          Set.image_image _ _ _
        _ = (fun x : E 3 => g (phi x)) ''
              ((fun x : E 3 => g.symm x) '' F.face k) := by
          congr 1
          funext x
          simp [psi]
        _ = (fun x : E 3 => g x) ''
              ((fun x : E 3 => phi x) ''
                ((fun x : E 3 => g.symm x) '' F.face k)) :=
          (Set.image_image _ _ _).symm
        _ = (fun x : E 3 => g x) ''
              ((fun x : E 3 => g.symm x) '' G.face k) := by rw [hflag]
        _ = G.face k := image_isom_roundtrip g (G.face k)

end LeanEval.Geometry.PlatonicClassification
