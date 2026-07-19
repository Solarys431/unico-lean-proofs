import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.MossaInvolutiva
import UnicoProofs.Platonici.Equivarianza
import UnicoProofs.Platonici.Trasportatore
import UnicoProofs.Platonici.LibertaGenerica
import UnicoProofs.Platonici.GruppoFinito
import UnicoProofs.Platonici.Ordini

/-!
MOTORE COXETER, PASSO 16 — CONIUGAZIONE E INDIPENDENZA DALLA BASE
(19 lug 2026).

Cambiare bandiera base coniuga i generatori: `r'ᵢ = g rᵢ g⁻¹`, dove `g`
è il trasportatore. Ne segue che la matrice di Coxeter NON dipende dalla
bandiera scelta: è un invariante del politopo.

Il perno è l'unicità del trasportatore, a sua volta conseguenza della
libertà dell'azione.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- L'azione del gruppo di simmetria sulle bandiere. -/
noncomputable def act (P : ConvexPolytope n) (g : symGroup P) (F : P.Flag) :
    P.Flag :=
  mapFlag P g.2 F

@[simp] theorem act_face (P : ConvexPolytope n) (g : symGroup P)
    (F : P.Flag) (k : Fin n) :
    (act P g F).face k = (⇑(g : Isom n)) '' F.face k := rfl

theorem act_one (P : ConvexPolytope n) (F : P.Flag) :
    act P 1 F = F := by
  apply flag_ext
  funext k
  show (⇑((1 : symGroup P) : Isom n)) '' F.face k = F.face k
  simp

theorem act_mul (P : ConvexPolytope n) (a b : symGroup P) (F : P.Flag) :
    act P (a * b) F = act P a (act P b F) := by
  apply flag_ext
  funext k
  show (⇑((a * b : symGroup P) : Isom n)) '' F.face k =
    (⇑(a : Isom n)) '' ((⇑(b : Isom n)) '' F.face k)
  rw [Set.image_image]
  rfl

/-- **L'azione è libera**: due elementi che muovono ugualmente una
bandiera coincidono. -/
theorem act_injective (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (F : P.Flag) {a b : symGroup P} (h : act P a F = act P b F) : a = b := by
  apply Subtype.ext
  exact AffineIsometryEquiv.ext
    (symmetry_action_injective P hfull F a.2 b.2 h)

/-- L'azione commuta con la mossa di adiacenza. -/
theorem act_adjacentFlag (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (g : symGroup P) (F : P.Flag) (i : Fin n) :
    act P g (adjacentFlag P hfull F i) =
      adjacentFlag P hfull (act P g F) i :=
  mapFlag_adjacentFlag P hfull g.2 F i

/-- Il generatore, applicato alla propria bandiera base, dà l'adiacente. -/
theorem act_simpleGen (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) :
    act P (simpleGen P hreg F i) F = adjacentFlag P hreg.1 F i :=
  simpleReflection_mapFlag P hreg F i

/-- Il trasportatore come elemento del gruppo. -/
noncomputable def transp (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F G : P.Flag) : symGroup P :=
  ⟨transporter P hreg F G, transporter_isSymmetry P hreg F G⟩

theorem act_transp (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F G : P.Flag) : act P (transp P hreg F G) F = G :=
  transporter_mapFlag P hreg F G

/-- **I generatori si coniugano** al cambio di bandiera base. -/
theorem simpleGen_conj (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F G : P.Flag) (i : Fin n) :
    simpleGen P hreg G i =
      transp P hreg F G * simpleGen P hreg F i *
        (transp P hreg F G)⁻¹ := by
  set g := transp P hreg F G with hg
  refine act_injective P hreg.1 G ?_
  have hgF : act P g F = G := act_transp P hreg F G
  have hinv : act P g⁻¹ G = F := by
    rw [← hgF, ← act_mul, inv_mul_cancel, act_one]
  calc
    act P (simpleGen P hreg G i) G = adjacentFlag P hreg.1 G i :=
      act_simpleGen P hreg G i
    _ = adjacentFlag P hreg.1 (act P g F) i := by rw [hgF]
    _ = act P g (adjacentFlag P hreg.1 F i) :=
      (act_adjacentFlag P hreg.1 g F i).symm
    _ = act P g (act P (simpleGen P hreg F i) F) := by
      rw [act_simpleGen P hreg F i]
    _ = act P g (act P (simpleGen P hreg F i) (act P g⁻¹ G)) := by
      rw [hinv]
    _ = act P (g * simpleGen P hreg F i * g⁻¹) G := by
      rw [act_mul, act_mul]

/-- **La matrice di Coxeter non dipende dalla bandiera base**: è un
invariante del politopo. -/
theorem coxeterMatrix_indep (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F G : P.Flag) (i j : Fin n) :
    coxeterMatrix P hreg G i j = coxeterMatrix P hreg F i j := by
  unfold coxeterMatrix
  have hprod : simpleGen P hreg G i * simpleGen P hreg G j =
      MulAut.conj (transp P hreg F G)
        (simpleGen P hreg F i * simpleGen P hreg F j) := by
    rw [MulAut.conj_apply, simpleGen_conj P hreg F G i,
      simpleGen_conj P hreg F G j]
    group
  rw [hprod]
  exact (MulAut.conj (transp P hreg F G)).orderOf_eq _

end LeanEval.Geometry.PlatonicClassification
