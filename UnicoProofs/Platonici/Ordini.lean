import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.Equivarianza
import UnicoProofs.Platonici.Trasportatore
import UnicoProofs.Platonici.LibertaGenerica
import UnicoProofs.Platonici.RelazioniCoxeter
import UnicoProofs.Platonici.GruppoFinito

/-!
MOTORE COXETER, PASSO 15 — IL SOTTOGRUPPO E GLI ORDINI (19 lug 2026).

Le simmetrie formano un sottogruppo di `Isom n`, finito per il passo
precedente. In un gruppo finito ogni elemento ha ordine finito: nasce
così la MATRICE DI COXETER `mᵢⱼ = ord(rᵢ rⱼ)`, con `mᵢᵢ = 1` (le
riflessioni sono involuzioni non banali) e `mᵢⱼ = 2` per i ranghi
lontani (commutano).
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- L'essere simmetria dipende solo dalla funzione sottostante. -/
theorem isSymmetry_congr (P : ConvexPolytope n) {φ ψ : Isom n}
    (h : ∀ x, φ x = ψ x) (hφ : P.isSymmetry φ) : P.isSymmetry ψ := by
  unfold ConvexPolytope.isSymmetry at *
  calc
    (⇑ψ) '' P.toSet = (⇑φ) '' P.toSet :=
      Set.image_congr (fun x _ => (h x).symm)
    _ = P.toSet := hφ

/-- **Il gruppo di simmetria** come sottogruppo di `Isom n`. -/
def symGroup (P : ConvexPolytope n) : Subgroup (Isom n) where
  carrier := {φ : Isom n | P.isSymmetry φ}
  one_mem' := symmetry_reflN P
  mul_mem' {a b} ha hb := by
    refine isSymmetry_congr P (φ := b.trans a) (fun x => rfl)
      (symmetry_transN hb ha)
  inv_mem' {a} ha := by
    refine isSymmetry_congr P (φ := a.symm) (fun x => rfl)
      (symmetry_symmN ha)

@[simp] theorem mem_symGroup (P : ConvexPolytope n) {φ : Isom n} :
    φ ∈ symGroup P ↔ P.isSymmetry φ := Iff.rfl

/-- Il gruppo di simmetria di un politopo pieno è finito. -/
instance symGroup_finite (P : ConvexPolytope n) [hfull : Fact P.IsFullDim] :
    Finite (symGroup P) :=
  symmetries_finite P hfull.out

/-- La riflessione semplice, come elemento del gruppo. -/
noncomputable def simpleGen (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) : symGroup P :=
  ⟨simpleReflection P hreg F i, simpleReflection_isSymmetry P hreg F i⟩

/-- **rᵢ² = 1 nel gruppo.** -/
theorem simpleGen_sq (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) :
    simpleGen P hreg F i * simpleGen P hreg F i = 1 := by
  apply Subtype.ext
  apply AffineIsometryEquiv.ext
  intro x
  exact simpleReflection_sq P hreg F i x

/-- **rᵢ ≠ 1**: i generatori non sono banali. -/
theorem simpleGen_ne_one (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) : simpleGen P hreg F i ≠ 1 := by
  intro h
  refine simpleReflection_ne_id P hreg F i (fun x => ?_)
  have hv : ((simpleGen P hreg F i : symGroup P) : Isom n) x = x := by
    rw [h]
    simp
  exact hv

/-- **Ogni riflessione semplice ha ordine esattamente 2.** -/
theorem simpleGen_orderOf (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) : orderOf (simpleGen P hreg F i) = 2 := by
  refine orderOf_eq_prime ?_ (simpleGen_ne_one P hreg F i)
  rw [sq]
  exact simpleGen_sq P hreg F i

/-- **(rᵢ rⱼ)² = 1 per ranghi lontani.** -/
theorem simpleGen_far_sq (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) {i j : Fin n} (hij : (i : ℕ) + 2 ≤ (j : ℕ)) :
    (simpleGen P hreg F i * simpleGen P hreg F j) *
      (simpleGen P hreg F i * simpleGen P hreg F j) = 1 := by
  apply Subtype.ext
  apply AffineIsometryEquiv.ext
  intro x
  exact simpleReflection_far_rel P hreg F hij x

/-- **I generatori lontani COMMUTANO**: da `(rᵢrⱼ)² = 1` e dal fatto che
entrambi sono involuzioni. -/
theorem simpleGen_far_comm (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) {i j : Fin n} (hij : (i : ℕ) + 2 ≤ (j : ℕ)) :
    simpleGen P hreg F i * simpleGen P hreg F j =
      simpleGen P hreg F j * simpleGen P hreg F i := by
  have ha : (simpleGen P hreg F i)⁻¹ = simpleGen P hreg F i := by
    rw [inv_eq_iff_mul_eq_one]
    exact simpleGen_sq P hreg F i
  have hb : (simpleGen P hreg F j)⁻¹ = simpleGen P hreg F j := by
    rw [inv_eq_iff_mul_eq_one]
    exact simpleGen_sq P hreg F j
  have h := mul_eq_one_iff_eq_inv.mp (simpleGen_far_sq P hreg F hij)
  rwa [mul_inv_rev, ha, hb] at h

/-- **Ogni prodotto di generatori ha ordine finito**: il gruppo è finito,
dunque la matrice di Coxeter `mᵢⱼ = ord(rᵢrⱼ)` è ben definita. -/
theorem simpleGen_mul_isOfFinOrder (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i j : Fin n) :
    IsOfFinOrder (simpleGen P hreg F i * simpleGen P hreg F j) := by
  haveI : Fact P.IsFullDim := ⟨hreg.1⟩
  haveI := symGroup_finite P
  exact isOfFinOrder_of_finite _

/-- La matrice di Coxeter del politopo, relativa a una bandiera base. -/
noncomputable def coxeterMatrix (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i j : Fin n) : ℕ :=
  orderOf (simpleGen P hreg F i * simpleGen P hreg F j)

/-- Sulla diagonale la matrice di Coxeter vale 1. -/
theorem coxeterMatrix_diag (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) : coxeterMatrix P hreg F i i = 1 := by
  unfold coxeterMatrix
  rw [simpleGen_sq P hreg F i]
  exact orderOf_one

/-- Fuori diagonale la matrice di Coxeter è almeno 2. -/
theorem coxeterMatrix_off_diag_ge (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) {i j : Fin n} (hij : i ≠ j) :
    2 ≤ coxeterMatrix P hreg F i j := by
  haveI : Fact P.IsFullDim := ⟨hreg.1⟩
  haveI := symGroup_finite P
  have hpos : 0 < coxeterMatrix P hreg F i j :=
    orderOf_pos_iff.mpr (simpleGen_mul_isOfFinOrder P hreg F i j)
  rcases Nat.lt_or_ge (coxeterMatrix P hreg F i j) 2 with hlt | hge
  · exfalso
    have h1 : coxeterMatrix P hreg F i j = 1 := by omega
    have hone : simpleGen P hreg F i * simpleGen P hreg F j = 1 :=
      orderOf_eq_one_iff.mp h1
    -- da rᵢ rⱼ = 1 segue rᵢ = rⱼ, dunque le due bandiere adiacenti
    -- coincidono in ranghi diversi: impossibile.
    have hij' : simpleGen P hreg F i = simpleGen P hreg F j := by
      have hinv := mul_eq_one_iff_eq_inv.mp hone
      rw [hinv, inv_eq_iff_mul_eq_one]
      exact simpleGen_sq P hreg F j
    have hflag : adjacentFlag P hreg.1 F i = adjacentFlag P hreg.1 F j := by
      rw [← simpleReflection_mapFlag P hreg F i,
        ← simpleReflection_mapFlag P hreg F j]
      apply flag_ext
      funext k
      show (⇑(simpleReflection P hreg F i)) '' F.face k =
        (⇑(simpleReflection P hreg F j)) '' F.face k
      have hfun : ∀ x, simpleReflection P hreg F i x =
          simpleReflection P hreg F j x := by
        intro x
        exact congrArg (fun g : symGroup P => (g : Isom n) x) hij'
      exact Set.image_congr (fun x _ => hfun x)
    -- ma l'adiacente in i differisce da F esattamente in i
    have hAi := adjacentFlag_isAdjacent P hreg.1 F i
    have hAj := adjacentFlag_isAdjacent P hreg.1 F j
    rw [hflag] at hAi
    exact hAi.2 (hAj.1 i hij)
  · exact hge

end LeanEval.Geometry.PlatonicClassification
