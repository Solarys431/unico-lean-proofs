import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FlagAdiacente
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.MossaInvolutiva
import UnicoProofs.Platonici.Equivarianza

/-!
MOTORE COXETER, PASSO 12 — IL LINGUAGGIO DELLE GALLERIE (19 lug 2026).

La mossa elementare (`FlagStep`) e la connessione per gallerie
(`GalleryConnected`, chiusura riflessivo-transitiva). Qui i lemmi
strutturali: la mossa è simmetrica, la connessione è un'equivalenza,
e l'azione delle simmetrie la rispetta. Il teorema profondo — OGNI due
bandiere sono connesse — è il muro successivo e vivrà in un modulo suo.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- La mossa elementare: `G` differisce da `F` in un solo rango. -/
def FlagStep (P : ConvexPolytope n) (F G : P.Flag) : Prop :=
  ∃ i : Fin n, FlagAdjacentAt P F G i

/-- Connessione per gallerie: una catena finita di mosse elementari. -/
def GalleryConnected (P : ConvexPolytope n) (F G : P.Flag) : Prop :=
  Relation.ReflTransGen (FlagStep P) F G

/-- La mossa elementare è simmetrica. -/
theorem flagStep_symm (P : ConvexPolytope n) {F G : P.Flag}
    (h : FlagStep P F G) : FlagStep P G F := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, flagAdjacentAt_symm P hi⟩

theorem galleryConnected_refl (P : ConvexPolytope n) (F : P.Flag) :
    GalleryConnected P F F :=
  Relation.ReflTransGen.refl

theorem galleryConnected_trans (P : ConvexPolytope n) {F G H : P.Flag}
    (h₁ : GalleryConnected P F G) (h₂ : GalleryConnected P G H) :
    GalleryConnected P F H :=
  Relation.ReflTransGen.trans h₁ h₂

/-- La connessione per gallerie è simmetrica. -/
theorem galleryConnected_symm (P : ConvexPolytope n) {F G : P.Flag}
    (h : GalleryConnected P F G) : GalleryConnected P G F := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (flagStep_symm P hstep)) ih

/-- Un passo di adiacenza è una galleria. -/
theorem galleryConnected_adjacent (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) (i : Fin n) :
    GalleryConnected P F (adjacentFlag P hfull F i) :=
  Relation.ReflTransGen.single ⟨i, adjacentFlag_isAdjacent P hfull F i⟩

/-- Le simmetrie trasportano mosse in mosse. -/
theorem flagStep_map (P : ConvexPolytope n) {φ : Isom n}
    (hφ : P.isSymmetry φ) {F G : P.Flag} (h : FlagStep P F G) :
    FlagStep P (mapFlag P hφ F) (mapFlag P hφ G) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, flagAdjacentAt_map P hφ hi⟩

/-- **Equivarianza delle gallerie**: l'azione rispetta la connessione. -/
theorem galleryConnected_map (P : ConvexPolytope n) {φ : Isom n}
    (hφ : P.isSymmetry φ) {F G : P.Flag} (h : GalleryConnected P F G) :
    GalleryConnected P (mapFlag P hφ F) (mapFlag P hφ G) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (flagStep_map P hφ hstep)

end LeanEval.Geometry.PlatonicClassification
