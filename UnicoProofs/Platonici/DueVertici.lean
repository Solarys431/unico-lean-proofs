import Mathlib
import UnicoProofs.Platonici.BandieraVertice
import UnicoProofs.Platonici.ConoVertice

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : Nat}

/-- A zero-dimensional nonempty face is a singleton at a vertex. -/
theorem punto_di_faccia0_e_vertice (P : ConvexPolytope n)
    {F : Set (E n)} (hF : P.IsFace F) (hdF : faceDim F = 0) :
    Exists fun v : E n =>
      And (F = ({v} : Set (E n))) (Membership.mem P.vertices v) := by
  choose v hFv using faccia_dim0_singoletto hF.2 hdF
  refine Exists.intro v (And.intro hFv ?_)
  have hexposed : IsExposed Real P.toSet ({v} : Set (E n)) := by
    simpa only [hFv] using hF.1
  have hvext : Membership.mem (P.toSet.extremePoints Real) v :=
    hexposed.isExtreme.mem_extremePoints
  have hvertices := P.vertices_eq_extremePoints
  rw [ConvexPolytope.toSet, hvertices.symm] at hvext
  exact hvext

/-- The only vertices of a segment-face are its endpoints, in any rank. -/
theorem vertice_in_segmento_estremo_generico (P : ConvexPolytope n)
    {delta : Set (E n)} (hdelta : P.IsFace delta) {x y z : E n}
    (hseg : delta = segment Real x y)
    (hz : Membership.mem P.vertices z) (hzdelta : Membership.mem delta z) :
    Or (z = x) (z = y) := by
  have hzext : Membership.mem (delta.extremePoints Real) z :=
    vertice_estremo_in_faccia P hdelta hz hzdelta
  have hxdelta : Membership.mem delta x := by
    rw [hseg]
    exact left_mem_segment Real x y
  have hydelta : Membership.mem delta y := by
    rw [hseg]
    exact right_mem_segment Real x y
  have hzseg : Membership.mem (segment Real x y) z := by
    simpa only [hseg] using hzdelta
  have hends : Or (x = z) (y = z) :=
    (mem_extremePoints_iff_forall_segment.mp hzext).2
      x hxdelta y hydelta hzseg
  exact hends.imp Eq.symm Eq.symm

/-- Every edge has exactly one zero-face different from a fixed zero-face. -/
theorem due_vertici_per_spigolo (P : ConvexPolytope n)
    {delta : Set (E n)} (hdelta : P.IsFace delta)
    (hddelta : faceDim delta = 1)
    {V : Set (E n)} (hV : P.IsFace V) (hdV : faceDim V = 0)
    (hVdelta : V < delta) :
    ExistsUnique fun W : Set (E n) =>
      And (And (P.IsFace W) (And (faceDim W = 0) (W < delta)))
        (Not (W = V)) := by
  choose v hVeq hvP using punto_di_faccia0_e_vertice P hV hdV
  have hvV : Membership.mem V v := by
    rw [hVeq]
    exact Set.mem_singleton v
  have hvdelta : Membership.mem delta v := hVdelta.le hvV
  choose a haP hadelta hav hseg using
    spigolo_segmento P hdelta hddelta hvP hvdelta
  refine ExistsUnique.intro ({a} : Set (E n)) ?_ ?_
  next =>
    have haFace : P.IsFace ({a} : Set (E n)) := vertex_isFace P haP
    have hda : faceDim ({a} : Set (E n)) = 0 := faceDim_singleton a
    have hasub : ({a} : Set (E n)) <= delta :=
      Set.singleton_subset_iff.mpr hadelta
    have haneqdelta : Not (({a} : Set (E n)) = delta) := by
      intro haeqdelta
      have hdelta0 : faceDim delta = 0 := by
        rw [haeqdelta] at hda
        exact hda
      omega
    have hass : ({a} : Set (E n)) < delta :=
      lt_of_le_of_ne hasub haneqdelta
    have haneV : Not (({a} : Set (E n)) = V) := by
      intro haeqV
      apply hav
      have hsingle : ({a} : Set (E n)) = {v} := haeqV.trans hVeq
      exact Set.singleton_injective hsingle
    exact And.intro (And.intro haFace (And.intro hda hass)) haneV
  next =>
    intro W hW
    have hWFace : P.IsFace W := hW.1.1
    have hdW : faceDim W = 0 := hW.1.2.1
    have hWdelta : W < delta := hW.1.2.2
    have hWneV : Not (W = V) := hW.2
    choose x hWeq hxP using punto_di_faccia0_e_vertice P hWFace hdW
    have hxW : Membership.mem W x := by
      rw [hWeq]
      exact Set.mem_singleton x
    have hxdelta : Membership.mem delta x := hWdelta.le hxW
    have hxend := vertice_in_segmento_estremo_generico P hdelta hseg hxP hxdelta
    cases hxend with
    | inl hxv =>
        have hWV : W = V := by
          calc
            W = {x} := hWeq
            _ = {v} := by rw [hxv]
            _ = V := hVeq.symm
        exact (hWneV hWV).elim
    | inr hxa =>
        calc
          W = {x} := hWeq
          _ = {a} := by rw [hxa]

end LeanEval.Geometry.PlatonicClassification
