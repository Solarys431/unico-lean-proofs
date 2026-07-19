import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.BandieraVertice
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.Equivarianza
import UnicoProofs.Platonici.LibertaGenerica

/-!
MOTORE COXETER, PASSO 14 — IL GRUPPO DI SIMMETRIA È FINITO (19 lug 2026).

Conseguenza diretta della libertà: l'azione delle simmetrie sulle
bandiere è libera, dunque l'orbita di una bandiera base distingue le
simmetrie. Poiché le facce di un politopo sono in numero finito, le
bandiere lo sono, e con esse il gruppo.

È il fatto che rende sensato parlare di ORDINE dei prodotti `rᵢ rⱼ`:
in un gruppo finito ogni elemento ha ordine finito, e la matrice di
Coxeter esiste.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- **Le bandiere sono in numero finito**: una bandiera è determinata
dalla sua catena, e le facce sono finite. -/
theorem flag_finite (P : ConvexPolytope n) : Finite P.Flag := by
  haveI : Finite {f : Set (E n) // P.IsFace f} :=
    Set.Finite.to_subtype (facce_finite P)
  refine Finite.of_injective
    (f := fun F : P.Flag =>
      (fun k : Fin n => (⟨F.face k, F.isFace k⟩ : {f : Set (E n) // P.IsFace f})))
    ?_
  intro F G h
  apply flag_ext
  funext k
  have hk := congrFun h k
  exact congrArg Subtype.val hk

/-- **L'azione sulle bandiere è libera**: una bandiera base separa le
simmetrie. -/
theorem symmetry_action_injective (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) {φ ψ : Isom n}
    (hφ : P.isSymmetry φ) (hψ : P.isSymmetry ψ)
    (h : mapFlag P hφ F = mapFlag P hψ F) : ∀ x : E n, φ x = ψ x := by
  have hcomp : P.isSymmetry (φ.trans ψ.symm) :=
    symmetry_transN hφ (symmetry_symmN hψ)
  have hfix : ∀ k : Fin n, (⇑(φ.trans ψ.symm)) '' F.face k = F.face k := by
    intro k
    have hk := congrArg (fun G : P.Flag => G.face k) h
    simp only [mapFlag_face] at hk
    calc
      (⇑(φ.trans ψ.symm)) '' F.face k
          = (⇑ψ.symm) '' ((⇑φ) '' F.face k) := by
            rw [Set.image_image]
            rfl
      _ = (⇑ψ.symm) '' ((⇑ψ) '' F.face k) := by rw [hk]
      _ = F.face k := ψ.toEquiv.symm_image_image _
  have hid := bandiera_fissata_id P hfull hcomp F hfix
  intro x
  have hx := hid x
  have hx' : ψ.symm (φ x) = x := by simpa using hx
  calc
    φ x = ψ (ψ.symm (φ x)) := (ψ.apply_symm_apply _).symm
    _ = ψ x := by rw [hx']

/-- **Il gruppo di simmetria di un politopo pieno è finito.** -/
theorem symmetries_finite (P : ConvexPolytope n) (hfull : P.IsFullDim) :
    Finite {φ : Isom n // P.isSymmetry φ} := by
  obtain ⟨F⟩ := flag_exists P hfull
  haveI := flag_finite P
  refine Finite.of_injective
    (f := fun φ : {φ : Isom n // P.isSymmetry φ} => mapFlag P φ.2 F) ?_
  intro φ ψ h
  apply Subtype.ext
  exact AffineIsometryEquiv.ext
    (symmetry_action_injective P hfull F φ.2 ψ.2 h)

end LeanEval.Geometry.PlatonicClassification
