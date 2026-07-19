-- NON RIUSCITO: testimoni_normalizzati completo perche' i moduli disponibili
-- non collegano ancora un generatore adiacente dell'orbita regolare a una
-- faccia di rango uno del politopo; si consegna la forma ridotta autorizzata.

import Challenge
import Solution.Fondamenta
import Solution.FanVertice
import Solution.Diamante
import Solution.ConnessioneVentaglio
import Solution.PianoDaiRaggi
import Solution.FaccettaDeterminata
import Solution.LatoSemipiano

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- Forma ridotta autorizzata dei testimoni normalizzati. -/
theorem testimoni_normalizzati (P : ConvexPolytope 3) {p q : ℕ}
    (h : P.asFinite.IsCyclicallyRegularOfType p q) {v : E 3}
    (_hv : v ∈ P.vertices) (D : P.asFinite.CyclicVertexData v q)
    (i : Fin q) :
    ∃ (rho : Isom 3) (x : E 3) (lato : ℝ), 0 < lato ∧
      x ∈ D.faccetta i ∧
      D.faccetta i = convexHull ℝ (Set.range fun j : Fin p =>
        (rho : E 3 → E 3)^[(j : ℕ)] x) ∧
      (rho : E 3 → E 3) '' D.faccetta i = D.faccetta i ∧
      Function.Injective (fun j : Fin p =>
        (rho : E 3 → E 3)^[(j : ℕ)] x) ∧
      (rho : E 3 → E 3)^[p] x = x ∧
      dist x (rho x) = lato ∧
      segment ℝ x (rho x) ⊆ D.faccetta i := by
  obtain ⟨lato, hlato, hreg, _⟩ := h.2.2.2
  obtain ⟨_, _, _, rho, x, hx, hrho, hinj, hclosed, hhull, hdist⟩ :=
    hreg (D.faccetta i) (D.isFacet i)
  have hrhox : rho x ∈ D.faccetta i := by
    have him : rho x ∈ (rho : E 3 → E 3) '' D.faccetta i := ⟨x, hx, rfl⟩
    rwa [hrho] at him
  refine ⟨rho, x, lato, hlato, hx, hhull, hrho, hinj, hclosed, hdist, ?_⟩
  exact ((D.isFacet i).1.1.convex (convex_convexHull ℝ _)).segment_subset
    hx hrhox

/-- Componente del secondo raggio ortogonale alla direzione del lato. -/
def normale_secondo_raggio (v x w : E 3) : E 3 :=
  (x - v) -
    (⟪x - v, w - v⟫ / ⟪w - v, w - v⟫) • (w - v)

/-- Funzionale lineare che misura il lato del semipiano rispetto al lato. -/
def funzionale_secondo_raggio (v x w : E 3) : E 3 →L[ℝ] ℝ :=
  innerSL ℝ (normale_secondo_raggio v x w)

/-- Il secondo raggio comune sceglie la stessa delle due orientazioni
possibili del semipiano. Le due disgiunzioni `hsideA` e `hsideB` sono la
forma orientazione-indipendente del fatto che il segmento e' una faccia
esposta nei due insiemi planari. -/
theorem semipiano_dal_secondo_raggio
    {A B : Set (E 3)} {v x w : E 3}
    (_hAconv : Convex ℝ A) (_hBconv : Convex ℝ B)
    (_hvA : v ∈ A) (_hvB : v ∈ B)
    (hxA : x ∈ A) (hxB : x ∈ B)
    (_hpiano : affineSpan ℝ A = affineSpan ℝ B)
    (hsideA :
      (∀ z ∈ A, funzionale_secondo_raggio v x w v ≤
        funzionale_secondo_raggio v x w z) ∨
      (∀ z ∈ A, funzionale_secondo_raggio v x w z ≤
        funzionale_secondo_raggio v x w v))
    (hsideB :
      (∀ z ∈ B, funzionale_secondo_raggio v x w v ≤
        funzionale_secondo_raggio v x w z) ∨
      (∀ z ∈ B, funzionale_secondo_raggio v x w z ≤
        funzionale_secondo_raggio v x w v))
    (hlatoA :
      {z ∈ A | funzionale_secondo_raggio v x w z =
        funzionale_secondo_raggio v x w v} = segment ℝ v w)
    (hlatoB :
      {z ∈ B | funzionale_secondo_raggio v x w z =
        funzionale_secondo_raggio v x w v} = segment ℝ v w)
    (hind : LinearIndependent ℝ ![w - v, x - v]) :
    SemipianoComune A B v w := by
  let u : E 3 := w - v
  let a : E 3 := x - v
  let c : ℝ := ⟪a, u⟫ / ⟪u, u⟫
  let n : E 3 := a - c • u
  have hindua : LinearIndependent ℝ ![u, a] := by
    simpa [u, a] using hind
  have hu_ne : u ≠ 0 := by
    simpa using hindua.ne_zero (0 : Fin 2)
  have huu_pos : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu_ne
  have huu_ne : ⟪u, u⟫ ≠ 0 := ne_of_gt huu_pos
  have hnu : ⟪n, u⟫ = 0 := by
    dsimp [n, c]
    rw [inner_sub_left, real_inner_smul_left]
    field_simp
    ring
  have hn_ne : n ≠ 0 := by
    intro hn
    have hacu : a = c • u := sub_eq_zero.mp hn
    have hind' := hindua
    rw [linearIndependent_fin2] at hind'
    change a ≠ 0 ∧ ∀ r : ℝ, r • a ≠ u at hind'
    by_cases hc : c = 0
    · apply hind'.1
      exact hacu.trans (by rw [hc, zero_smul])
    · apply hind'.2 c⁻¹
      rw [hacu, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hna_pos : 0 < ⟪n, a⟫ := by
    have ha : a = n + c • u := by
      dsimp [n]
      abel
    rw [ha, inner_add_right, real_inner_smul_right, hnu]
    simp only [mul_zero, add_zero]
    exact real_inner_self_pos.mpr hn_ne
  have hfun_eq : funzionale_secondo_raggio v x w = innerSL ℝ n := by
    rfl
  have hdiff : funzionale_secondo_raggio v x w x -
      funzionale_secondo_raggio v x w v = ⟪n, a⟫ := by
    rw [hfun_eq]
    simp only [innerSL_apply_apply, ← inner_sub_right, a]
  have hvx : funzionale_secondo_raggio v x w v <
      funzionale_secondo_raggio v x w x := by
    linarith
  have hnonnegA : ∀ z ∈ A, funzionale_secondo_raggio v x w v ≤
      funzionale_secondo_raggio v x w z := by
    rcases hsideA with hpos | hneg
    · exact hpos
    · exact (not_le_of_gt hvx (hneg x hxA)).elim
  have hnonnegB : ∀ z ∈ B, funzionale_secondo_raggio v x w v ≤
      funzionale_secondo_raggio v x w z := by
    rcases hsideB with hpos | hneg
    · exact hpos
    · exact (not_le_of_gt hvx (hneg x hxB)).elim
  refine ⟨funzionale_secondo_raggio v x w, ?_, hnonnegA, hnonnegB,
    hlatoA, hlatoB⟩
  rw [hfun_eq]
  simp only [innerSL_apply_apply]
  apply sub_eq_zero.mp
  rw [← inner_sub_right]
  change ⟪n, v - w⟫ = 0
  rw [show v - w = -u by simp [u], inner_neg_right, hnu, neg_zero]

end LeanEval.Geometry.PlatonicClassification
