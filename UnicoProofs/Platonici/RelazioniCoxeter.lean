import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FlagAdiacente
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.MossaInvolutiva
import UnicoProofs.Platonici.Equivarianza
import UnicoProofs.Platonici.Trasportatore
import UnicoProofs.Platonici.Commutazione
import UnicoProofs.Platonici.RelazioneLontana
import UnicoProofs.Platonici.LibertaGenerica

/-!
MOTORE COXETER, PASSO 13 — LE RELAZIONI NEL GRUPPO (19 lug 2026).

La libertà dell'azione (`bandiera_fissata_id`) promuove le identità di
BANDIERE già certificate a identità di ISOMETRIE. Le due prime famiglie
di relazioni di Coxeter sono qui:

    rᵢ² = 1                    (le riflessioni sono involuzioni)
    (rᵢ rⱼ)² = 1  se |i−j| ≥ 2 (i generatori lontani commutano)

Il ponte è sempre lo stesso: una composizione di simmetrie che fissa
tutte le facce della bandiera base è l'identità.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- L'immagine lungo una composizione è la composizione delle immagini. -/
theorem image_trans_isom (φ ψ : Isom n) (S : Set (E n)) :
    (⇑(φ.trans ψ)) '' S = (⇑ψ) '' ((⇑φ) '' S) := by
  rw [Set.image_image]
  rfl

/-- Il ponte fra bandiere e gruppo: se una simmetria fissa la bandiera
base (come bandiera), è l'identità. -/
theorem eq_id_of_mapFlag_eq (P : ConvexPolytope n) (hfull : P.IsFullDim)
    {φ : Isom n} (hφ : P.isSymmetry φ) (F : P.Flag)
    (h : mapFlag P hφ F = F) : ∀ x : E n, φ x = x := by
  refine bandiera_fissata_id P hfull hφ F (fun k => ?_)
  have hk := congrArg (fun G : P.Flag => G.face k) h
  simpa only [mapFlag_face] using hk

/-- **rᵢ² = 1**: le riflessioni semplici sono involuzioni. -/
theorem simpleReflection_sq (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (x : E n) :
    simpleReflection P hreg F i (simpleReflection P hreg F i x) = x := by
  have hi : P.isSymmetry (simpleReflection P hreg F i) :=
    simpleReflection_isSymmetry P hreg F i
  have hcomp : P.isSymmetry
      ((simpleReflection P hreg F i).trans (simpleReflection P hreg F i)) :=
    symmetry_transN hi hi
  have hflag : mapFlag P hcomp F = F := by
    rw [← mapFlag_trans P hi hi F]
    exact simpleReflection_sq_fixes P hreg F i
  have h := eq_id_of_mapFlag_eq P hreg.1 hcomp F hflag x
  simpa using h

/-- **(rᵢ rⱼ)² = 1 per |i − j| ≥ 2**: i generatori lontani commutano. -/
theorem simpleReflection_far_rel (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) {i j : Fin n}
    (hij : (i : ℕ) + 2 ≤ (j : ℕ)) (x : E n) :
    simpleReflection P hreg F i (simpleReflection P hreg F j
      (simpleReflection P hreg F i
        (simpleReflection P hreg F j x))) = x := by
  have hi : P.isSymmetry (simpleReflection P hreg F i) :=
    simpleReflection_isSymmetry P hreg F i
  have hj : P.isSymmetry (simpleReflection P hreg F j) :=
    simpleReflection_isSymmetry P hreg F j
  have hs : P.isSymmetry
      ((simpleReflection P hreg F j).trans (simpleReflection P hreg F i)) :=
    symmetry_transN hj hi
  have hss : P.isSymmetry
      (((simpleReflection P hreg F j).trans
        (simpleReflection P hreg F i)).trans
        ((simpleReflection P hreg F j).trans
          (simpleReflection P hreg F i))) :=
    symmetry_transN hs hs
  have hflag : mapFlag P hss F = F := by
    rw [← mapFlag_trans P hs hs F, ← mapFlag_trans P hj hi F,
      ← mapFlag_trans P hj hi (mapFlag P hi (mapFlag P hj F))]
    exact simpleReflection_far_comm_fixes P hreg F hij
  have h := eq_id_of_mapFlag_eq P hreg.1 hss F hflag x
  simpa using h

/-- Le riflessioni semplici non sono l'identità. -/
theorem simpleReflection_ne_id (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) :
    ¬ (∀ x : E n, simpleReflection P hreg F i x = x) := by
  intro hid
  have hflag : mapFlag P (simpleReflection_isSymmetry P hreg F i) F = F := by
    apply flag_ext
    funext k
    show (⇑(simpleReflection P hreg F i)) '' F.face k = F.face k
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rwa [hid z]
    · intro hy
      exact ⟨y, hy, hid y⟩
  have hne := adjacentFlag_ne P hreg.1 F i
  rw [← simpleReflection_mapFlag P hreg F i] at hne
  exact hne hflag

end LeanEval.Geometry.PlatonicClassification
