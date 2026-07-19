import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.MossaInvolutiva
import UnicoProofs.Platonici.Trasportatore
import UnicoProofs.Platonici.RelazioniCoxeter
import UnicoProofs.Platonici.GruppoFinito
import UnicoProofs.Platonici.Ordini
import UnicoProofs.Platonici.Iperpiano
import UnicoProofs.Platonici.Normali
import UnicoProofs.Platonici.FormulaRiflessione
import UnicoProofs.Platonici.Ortogonalita

/-!
MOTORE COXETER, PASSO 20 — LA MATRICE DI GRAM, PARTE FONDATA
(19 lug 2026).

Si raccolgono le voci della matrice di Gram dei normali che sono già
dimostrate:

  ⟪αᵢ, αᵢ⟫ = 1              (normalizzazione)
  ⟪αᵢ, αⱼ⟫ = 0  se |i−j| ≥ 2  (dalla commutazione: `Ortogonalita`)

e, sul versante combinatorio, il valore ESATTO della matrice di Coxeter
fuori dalla tridiagonale:

  mᵢⱼ = 2       se |i−j| ≥ 2

Le due cose combaciano come devono: −cos(π/mᵢⱼ) = −cos(π/2) = 0.

La voce che manca è la sottodiagonale `⟪αᵢ, αᵢ₊₁⟫ = −cos(π/mᵢ)`, che
dipende da `mᵢ ≥ 3`, che dipende dal muro (connettività dei residui).
Qui NON la si assume di nascosto: è semplicemente assente.

La famiglia dei normali è esposta come DATO (skolemizzazione esplicita),
non nascosta dentro un esistenziale: è la lezione dei fascicoli persi
nella notte della rigidità.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- **La famiglia dei normali**, esposta come dato: per ogni rango un
vettore unitario e un punto, con la formula della riflessione. -/
theorem esiste_famiglia_normali (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) :
    ∃ α p : Fin n → E n, (∀ i : Fin n, ‖α i‖ = 1) ∧
      ∀ (i : Fin n) (x : E n), simpleReflection P hreg F i x =
        x - (2 * ⟪α i, x - p i⟫ : ℝ) • α i := by
  choose α p hnorm hform using
    fun i : Fin n => simpleReflection_formula P hreg F i
  exact ⟨α, p, hnorm, hform⟩

/-- La diagonale della Gram. -/
theorem gram_diagonale {α : E n} (hα : ‖α‖ = 1) : ⟪α, α⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, hα]
  norm_num

/-- **Fuori dalla tridiagonale la matrice di Coxeter vale esattamente 2.** -/
theorem coxeterMatrix_far (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) {i j : Fin n} (hij : (i : ℕ) + 2 ≤ (j : ℕ)) :
    coxeterMatrix P hreg F i j = 2 := by
  have hne : i ≠ j := by
    intro he
    have : (i : ℕ) = (j : ℕ) := congrArg Fin.val he
    omega
  have hge : 2 ≤ coxeterMatrix P hreg F i j :=
    coxeterMatrix_off_diag_ge P hreg F hne
  have hle : coxeterMatrix P hreg F i j ≤ 2 := by
    unfold coxeterMatrix
    refine orderOf_le_of_pow_eq_one (by norm_num) ?_
    rw [pow_two]
    exact simpleGen_far_sq P hreg F hij
  omega

/-- **La Gram, parte fondata**: diagonale unitaria e zeri lontani. -/
theorem gram_parte_fondata (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (α p : Fin n → E n) (hnorm : ∀ i : Fin n, ‖α i‖ = 1)
    (hform : ∀ (i : Fin n) (x : E n), simpleReflection P hreg F i x =
      x - (2 * ⟪α i, x - p i⟫ : ℝ) • α i) :
    (∀ i : Fin n, ⟪α i, α i⟫ = 1) ∧
      (∀ i j : Fin n, (i : ℕ) + 2 ≤ (j : ℕ) → ⟪α i, α j⟫ = 0) ∧
      (∀ i j : Fin n, (j : ℕ) + 2 ≤ (i : ℕ) → ⟪α i, α j⟫ = 0) := by
  refine ⟨fun i => gram_diagonale (hnorm i), ?_, ?_⟩
  · intro i j hij
    exact normali_lontani_ortogonali P hreg F hij (hnorm i) (hform i)
      (hnorm j) (hform j)
  · intro i j hji
    have h := normali_lontani_ortogonali P hreg F hji (hnorm j) (hform j)
      (hnorm i) (hform i)
    rw [real_inner_comm]
    exact h

/-- Coerenza fra i due versanti: dove la matrice di Coxeter vale 2, il
coseno dell'angolo fra i normali vale 0. -/
theorem gram_coerente_con_coxeter (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (α p : Fin n → E n)
    (hnorm : ∀ i : Fin n, ‖α i‖ = 1)
    (hform : ∀ (i : Fin n) (x : E n), simpleReflection P hreg F i x =
      x - (2 * ⟪α i, x - p i⟫ : ℝ) • α i)
    {i j : Fin n} (hij : (i : ℕ) + 2 ≤ (j : ℕ)) :
    ⟪α i, α j⟫ =
      -Real.cos (Real.pi / (coxeterMatrix P hreg F i j : ℝ)) := by
  rw [coxeterMatrix_far P hreg F hij]
  rw [normali_lontani_ortogonali P hreg F hij (hnorm i) (hform i)
    (hnorm j) (hform j)]
  norm_num

end LeanEval.Geometry.PlatonicClassification
