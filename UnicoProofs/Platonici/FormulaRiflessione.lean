import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.Trasportatore
import UnicoProofs.Platonici.RelazioniCoxeter
import UnicoProofs.Platonici.Iperpiano
import UnicoProofs.Platonici.Normali

/-!
MOTORE COXETER, PASSO 19 — LA FORMULA DELLA RIFLESSIONE (19 lug 2026).

Sapere che i punti fissi sono un iperpiano non basta: serve la FORMULA,

    rᵢ x = x − 2⟪αᵢ, x − pᵢ⟫ • αᵢ,

perché è da lì che si leggono gli angoli fra i normali, e quindi la
matrice di Gram.

Dimostrazione, algebra lineare pura sulla parte lineare `L` di `rᵢ`:
`L` fissa la giacitura dell'iperpiano; manda dunque `α` in `c • α`
(un'isometria preserva l'ortogonale della giacitura, che è la retta di
`α`); `c = ±1` per la norma; e `c = +1` costringerebbe `rᵢ` all'identità,
esclusa da `simpleReflection_ne_id`.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- La componente di un vettore ortogonale a un unitario. -/
theorem inner_comp_ortogonale {α v : E n} (hα : ‖α‖ = 1) :
    ⟪α, v - (⟪α, v⟫ : ℝ) • α⟫ = 0 := by
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hα]
  ring

/-- Un vettore ortogonale a tutta la giacitura è multiplo del normale. -/
theorem multiplo_del_normale {α w : E n} (hα : ‖α‖ = 1)
    (hw : ∀ v : E n, ⟪α, v⟫ = 0 → ⟪w, v⟫ = 0) :
    w = (⟪α, w⟫ : ℝ) • α := by
  have hdec : ⟪α, w - (⟪α, w⟫ : ℝ) • α⟫ = 0 :=
    inner_comp_ortogonale (α := α) (v := w) hα
  have h0 : ⟪w, w - (⟪α, w⟫ : ℝ) • α⟫ = 0 := hw _ hdec
  have h1 : ⟪(⟪α, w⟫ : ℝ) • α, w - (⟪α, w⟫ : ℝ) • α⟫ = 0 := by
    rw [real_inner_smul_left, hdec, mul_zero]
  have h2 : ⟪w - (⟪α, w⟫ : ℝ) • α, w - (⟪α, w⟫ : ℝ) • α⟫ = 0 := by
    rw [inner_sub_left, h0, h1, sub_zero]
  have hz := inner_self_eq_zero.mp h2
  exact sub_eq_zero.mp hz

/-- **La formula della riflessione semplice.** -/
theorem simpleReflection_formula (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n) :
    ∃ α p : E n, ‖α‖ = 1 ∧
      ∀ x : E n, simpleReflection P hreg F i x =
        x - (2 * ⟪α, x - p⟫ : ℝ) • α := by
  obtain ⟨α, p, hα, hfix⟩ := esiste_normale P hreg F i
  refine ⟨α, p, hα, ?_⟩
  set r := simpleReflection P hreg F i with hr
  have hrp : r p = p := by
    refine (hfix p).mpr ?_
    simp
  set L := r.linearIsometryEquiv with hL
  have hLapp : ∀ y : E n, L y = r (y + p) - p := by
    intro y
    have hmv : L ((y + p) -ᵥ p) = r (y + p) -ᵥ r p := r.map_vsub (y + p) p
    rw [hrp] at hmv
    simpa [vsub_eq_sub] using hmv
  have hrx : ∀ x : E n, r x = L (x - p) + p := by
    intro x
    rw [hLapp (x - p)]
    simp
  have hLfix : ∀ v : E n, ⟪α, v⟫ = 0 → L v = v := by
    intro v hv
    have hvfix : r (v + p) = v + p := by
      refine (hfix (v + p)).mpr ?_
      simpa using hv
    rw [hLapp v, hvfix]
    abel
  have hLα_ortho : ∀ v : E n, ⟪α, v⟫ = 0 → ⟪L α, v⟫ = 0 := by
    intro v hv
    have h1 : ⟪L α, L v⟫ = ⟪α, v⟫ := L.inner_map_map α v
    rw [hLfix v hv, hv] at h1
    exact h1
  have hLαc : L α = (⟪α, L α⟫ : ℝ) • α :=
    multiplo_del_normale hα hLα_ortho
  -- il coefficiente vale ±1
  have hnorm : ‖L α‖ = 1 := by
    rw [L.norm_map]
    exact hα
  have habs : |(⟪α, L α⟫ : ℝ)| = 1 := by
    have hn := hnorm
    rw [hLαc, norm_smul, hα, mul_one, Real.norm_eq_abs] at hn
    exact hn
  have hc2 : (⟪α, L α⟫ : ℝ) * (⟪α, L α⟫ : ℝ) = 1 := by
    have := congrArg (fun t : ℝ => t * t) habs
    simpa [abs_mul_abs_self] using this
  -- il caso `+1` è escluso: renderebbe `rᵢ` l'identità
  have hcneg : (⟪α, L α⟫ : ℝ) = -1 := by
    rcases mul_self_eq_one_iff.mp hc2 with hpos | hneg
    · exfalso
      refine simpleReflection_ne_id P hreg F i (fun x => ?_)
      have hLid : L (x - p) = x - p := by
        have hdec : x - p =
            (x - p - (⟪α, x - p⟫ : ℝ) • α) + (⟪α, x - p⟫ : ℝ) • α := by
          abel
        rw [hdec, map_add, hLfix _ (inner_comp_ortogonale hα),
          map_smul, hLαc, hpos, one_smul]
      rw [hrx x, hLid]
      abel
    · exact hneg
  intro x
  have hLx : L (x - p) = (x - p) - (2 * ⟪α, x - p⟫ : ℝ) • α := by
    have hsplit : L (x - p) =
        L (x - p - (⟪α, x - p⟫ : ℝ) • α) + L ((⟪α, x - p⟫ : ℝ) • α) := by
      rw [← map_add]
      congr 1
      abel
    rw [hsplit, hLfix _ (inner_comp_ortogonale hα), map_smul, hLαc, hcneg]
    match_scalars <;> ring
  rw [hrx x, hLx]
  abel

end LeanEval.Geometry.PlatonicClassification
