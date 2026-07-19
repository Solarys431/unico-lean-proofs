import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.MossaInvolutiva
import UnicoProofs.Platonici.Equivarianza
import UnicoProofs.Platonici.Trasportatore
import UnicoProofs.Platonici.Gallerie
import UnicoProofs.Platonici.LibertaGenerica
import UnicoProofs.Platonici.GruppoFinito
import UnicoProofs.Platonici.Ordini
import UnicoProofs.Platonici.Coniugazione

/-!
MOTORE COXETER, PASSO 21 — LE RIFLESSIONI SEMPLICI GENERANO IL GRUPPO
(19 lug 2026).

Secondo ramo del diagramma: dalla connettività per gallerie discende che
ogni simmetria del politopo è una PAROLA nelle riflessioni semplici.

Il passo induttivo è più semplice di quanto sembri, e non richiede
coniugazioni: percorrendo una galleria, l'equivarianza fa scivolare la
mossa dall'estremità raggiunta alla bandiera base, e la parola cresce
semplicemente a destra,

    act (w · rᵢ) F = adj_i (act w F).

L'ipotesi di connettività è ESPLICITA nella firma: non è assunta di
nascosto. Quando il muro (connettività dei residui e delle gallerie)
cadrà, questo teorema si scaricherà da sé.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Il sottogruppo generato dalle riflessioni semplici, relativo a una
bandiera base. -/
def simpleSubgroup (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) : Subgroup (symGroup P) :=
  Subgroup.closure (Set.range (simpleGen P hreg F))

theorem simpleGen_mem (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) :
    simpleGen P hreg F i ∈ simpleSubgroup P hreg F :=
  Subgroup.subset_closure ⟨i, rfl⟩

/-- Il passo che fa crescere la parola: moltiplicare a destra per `rᵢ`
equivale a fare la mossa `i` sulla bandiera raggiunta. -/
theorem act_mul_simpleGen (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (w : symGroup P) (i : Fin n) :
    act P (w * simpleGen P hreg F i) F =
      adjacentFlag P hreg.1 (act P w F) i := by
  rw [act_mul, act_simpleGen P hreg F i]
  exact act_adjacentFlag P hreg.1 w F i

/-- **Ogni bandiera raggiungibile per gallerie è nell'orbita del
sottogruppo generato dalle riflessioni semplici.** -/
theorem orbita_di_galleria (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F G : P.Flag) (hgal : GalleryConnected P F G) :
    ∃ w : symGroup P, w ∈ simpleSubgroup P hreg F ∧ act P w F = G := by
  induction hgal with
  | refl => exact ⟨1, one_mem _, act_one P F⟩
  | tail _ hstep ih =>
      obtain ⟨w, hw, hwF⟩ := ih
      obtain ⟨i, hadj⟩ := hstep
      refine ⟨w * simpleGen P hreg F i,
        mul_mem hw (simpleGen_mem P hreg F i), ?_⟩
      rw [act_mul_simpleGen P hreg F w i, hwF]
      exact (adjacentFlag_eq_of_isAdjacent P hreg.1 i hadj).symm

/-- **LE RIFLESSIONI SEMPLICI GENERANO IL GRUPPO** (condizionale alla
connettività per gallerie, che è dichiarata in ipotesi). -/
theorem simpleSubgroup_eq_top (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag)
    (hconn : ∀ G : P.Flag, GalleryConnected P F G) :
    simpleSubgroup P hreg F = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro φ
  obtain ⟨w, hw, hwF⟩ :=
    orbita_di_galleria P hreg F (act P φ F) (hconn (act P φ F))
  have : w = φ := act_injective P hreg.1 F hwF
  rwa [← this]

/-- Riformulazione: ogni simmetria è una parola nelle riflessioni
semplici. -/
theorem simmetria_e_parola (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (hconn : ∀ G : P.Flag, GalleryConnected P F G)
    (φ : symGroup P) :
    φ ∈ Subgroup.closure (Set.range (simpleGen P hreg F)) := by
  have h := simpleSubgroup_eq_top P hreg F hconn
  unfold simpleSubgroup at h
  rw [h]
  exact Subgroup.mem_top φ

end LeanEval.Geometry.PlatonicClassification
