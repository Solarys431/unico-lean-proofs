import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FlagAdiacente
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.MossaInvolutiva

/-!
MOTORE COXETER, PASSO 8 — L'AZIONE SULLE BANDIERE E L'EQUIVARIANZA
(19 lug 2026).

I lemmi d'immagine della fase 3A (Immagini.lean) rifatti in dimensione
arbitraria: una simmetria trasporta facce in facce preservando la
dimensione. Ne segue l'azione `mapFlag` delle simmetrie sulle bandiere
e il lemma di EQUIVARIANZA: la mossa di adiacenza commuta con l'azione.
Con l'unicità già certificata, la commutazione è un montaggio: l'immagine
dell'adiacente è adiacente all'immagine, dunque È l'adiacente
dell'immagine.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Le esposizioni si trasportano lungo le isometrie affini (ogni `n`). -/
theorem isExposed_image_isomN (φ : Isom n) {A B : Set (E n)}
    (h : IsExposed ℝ A B) : IsExposed ℝ ((⇑φ) '' A) ((⇑φ) '' B) := by
  intro hne
  obtain ⟨b, hbB⟩ := hne
  obtain ⟨a, haB, hab⟩ := hbB
  obtain ⟨l, hl⟩ := h ⟨a, haB⟩
  let l' : E n →L[ℝ] ℝ :=
    l.comp φ.symm.linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
  have hl' (x : E n) : l' (φ x) = l x - l (φ.symm 0) := by
    have hm := φ.symm.map_vsub (φ x) 0
    have hm' : φ.symm.linearIsometryEquiv (φ x) = x - φ.symm 0 := by
      simpa using hm
    simp only [l', ContinuousLinearMap.comp_apply]
    change l (φ.symm.linearIsometryEquiv (φ x)) = _
    rw [hm', map_sub]
  refine ⟨l', Set.ext ?_⟩
  intro x
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [hl] at hb
    refine ⟨⟨b, hb.1, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [hl' y, hl' b]
    exact sub_le_sub_right (hb.2 y hy) _
  · rintro ⟨hxA, hxmax⟩
    obtain ⟨a, ha, rfl⟩ := hxA
    refine ⟨a, ?_, rfl⟩
    rw [hl]
    refine ⟨ha, ?_⟩
    intro y hy
    have hle := hxmax (φ y) ⟨y, hy, rfl⟩
    rw [hl' y, hl' a] at hle
    linarith

/-- Le isometrie affini preservano la dimensione delle facce (ogni `n`). -/
theorem faceDim_image_isomN (φ : Isom n) (F : Set (E n)) :
    faceDim ((⇑φ) '' F) = faceDim F := by
  unfold ConvexPolytope.faceDim
  have hmap := φ.toAffineEquiv.toAffineMap.map_vectorSpan (s := F)
  change Submodule.map (φ.toAffineEquiv.linear : E n →ₗ[ℝ] E n)
    (vectorSpan ℝ F) = vectorSpan ℝ ((⇑φ) '' F) at hmap
  rw [← hmap]
  exact φ.toAffineEquiv.linear.finrank_map_eq (vectorSpan ℝ F)

/-- Una simmetria trasporta facce in facce (ogni `n`). -/
theorem isFace_image_isomN {P : ConvexPolytope n} (φ : Isom n)
    (hφ : P.isSymmetry φ) {F : Set (E n)} (hF : P.IsFace F) :
    P.IsFace ((⇑φ) '' F) := by
  refine ⟨?_, hF.2.image _⟩
  rw [← hφ]
  exact isExposed_image_isomN φ hF.1

/-- L'identità è una simmetria (ogni `n`). -/
theorem symmetry_reflN (P : ConvexPolytope n) :
    P.isSymmetry (AffineIsometryEquiv.refl ℝ (E n)) :=
  Set.image_id _

/-- Le simmetrie sono chiuse per composizione (ogni `n`). -/
theorem symmetry_transN {P : ConvexPolytope n} {φ ψ : Isom n}
    (hφ : P.isSymmetry φ) (hψ : P.isSymmetry ψ) :
    P.isSymmetry (φ.trans ψ) := by
  unfold ConvexPolytope.isSymmetry at *
  calc
    (⇑(φ.trans ψ)) '' P.toSet = (⇑ψ) '' ((⇑φ) '' P.toSet) := by
      rw [Set.image_image]
      rfl
    _ = P.toSet := by rw [hφ, hψ]

/-- Le simmetrie sono chiuse per inversa (ogni `n`). -/
theorem symmetry_symmN {P : ConvexPolytope n} {φ : Isom n}
    (hφ : P.isSymmetry φ) : P.isSymmetry φ.symm := by
  unfold ConvexPolytope.isSymmetry at *
  calc
    (⇑φ.symm) '' P.toSet = (⇑φ.symm) '' ((⇑φ) '' P.toSet) := by rw [hφ]
    _ = P.toSet := φ.toEquiv.symm_image_image P.toSet

/-- **L'azione delle simmetrie sulle bandiere**: l'immagine di una
bandiera lungo una simmetria è una bandiera. -/
noncomputable def mapFlag (P : ConvexPolytope n) {φ : Isom n}
    (hφ : P.isSymmetry φ) (F : P.Flag) : P.Flag where
  face k := (⇑φ) '' F.face k
  isFace k := isFace_image_isomN φ hφ (F.isFace k)
  dim_eq k := by
    rw [faceDim_image_isomN]
    exact F.dim_eq k
  strict_mono i j hij := by
    have h := F.strict_mono i j hij
    have hparts := Set.ssubset_iff_subset_ne.mp h
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.image_mono hparts.1, ?_⟩
    intro heq
    exact hparts.2 ((Set.image_injective.mpr φ.injective) heq)

@[simp] theorem mapFlag_face (P : ConvexPolytope n) {φ : Isom n}
    (hφ : P.isSymmetry φ) (F : P.Flag) (k : Fin n) :
    (mapFlag P hφ F).face k = (⇑φ) '' F.face k := rfl

/-- L'adiacenza è equivariante: l'azione conserva la relazione. -/
theorem flagAdjacentAt_map (P : ConvexPolytope n) {φ : Isom n}
    (hφ : P.isSymmetry φ) {F G : P.Flag} {i : Fin n}
    (h : FlagAdjacentAt P F G i) :
    FlagAdjacentAt P (mapFlag P hφ F) (mapFlag P hφ G) i := by
  constructor
  · intro j hj
    show (⇑φ) '' G.face j = (⇑φ) '' F.face j
    rw [h.1 j hj]
  · show (⇑φ) '' G.face i ≠ (⇑φ) '' F.face i
    intro heq
    exact h.2 ((Set.image_injective.mpr φ.injective) heq)

/-- **EQUIVARIANZA DELLA MOSSA**: la mossa di adiacenza commuta con
l'azione delle simmetrie. Il cuore: per l'unicità, l'immagine
dell'adiacente — che è adiacente all'immagine — È l'adiacente
dell'immagine. -/
theorem mapFlag_adjacentFlag (P : ConvexPolytope n) (hfull : P.IsFullDim)
    {φ : Isom n} (hφ : P.isSymmetry φ) (F : P.Flag) (i : Fin n) :
    mapFlag P hφ (adjacentFlag P hfull F i) =
      adjacentFlag P hfull (mapFlag P hφ F) i :=
  adjacentFlag_eq_of_isAdjacent P hfull i
    (flagAdjacentAt_map P hφ (adjacentFlag_isAdjacent P hfull F i))

end LeanEval.Geometry.PlatonicClassification
