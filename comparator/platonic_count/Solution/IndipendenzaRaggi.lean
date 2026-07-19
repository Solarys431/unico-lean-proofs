import Mathlib
import Challenge
import Solution.FanVertice
import Solution.FanMarcato
import Solution.GramDalFan

/-!
RIGIDITÀ — I RAGGI CONSECUTIVI SONO INDIPENDENTI (19 lug 2026).

Ultima ipotesi da scaricare per il piano: due raggi consecutivi del
ventaglio non sono paralleli. Segue dalla Gram del gate 2: il loro
prodotto scalare è il coseno facciale, che vale 1/2, 0 oppure
(1 - √5)/4 — mai ±1. Due vettori unitari con prodotto scalare diverso da
±1 sono linearmente indipendenti.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope
open scoped RealInnerProductSpace

/-- Due vettori unitari con prodotto scalare diverso da ±1 sono
linearmente indipendenti. -/
theorem indipendenti_di_inner_ne {u w : E 3} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (h1 : ⟪u, w⟫ ≠ 1) (h2 : ⟪u, w⟫ ≠ -1) :
    LinearIndependent ℝ ![u, w] := by
  classical
  rw [LinearIndependent.pair_iff]
  intro s t hst
  set c : ℝ := ⟪u, w⟫ with hc
  -- proiettando su u e su w si ottiene un sistema lineare in s, t
  have hcu : s + t * c = 0 := by
    have hproj := congrArg (fun z => ⟪u, z⟫) hst
    simpa [inner_add_right, real_inner_smul_right, hu, hw, hc] using hproj
  have hcw : s * c + t = 0 := by
    have hproj := congrArg (fun z => ⟪w, z⟫) hst
    simpa [inner_add_right, real_inner_smul_right, hu, hw,
      real_inner_comm w u, hc] using hproj
  -- il determinante 1 - c² è non nullo perché c ≠ ±1
  have hdet : (1 - c) * (1 + c) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · intro hzero
      exact h1 (by linarith [sub_eq_zero.mp (by linarith : (1 : ℝ) - c = 0)])
    · intro hzero
      exact h2 (by linarith)
  have ht : t = 0 := by
    have hkey : t * ((1 - c) * (1 + c)) = 0 := by
      have hs : s = -(t * c) := by linarith
      rw [hs] at hcw
      nlinarith [hcw]
    rcases mul_eq_zero.mp hkey with h | h
    · exact h
    · exact absurd h hdet
  refine ⟨?_, ht⟩
  rw [ht] at hcu
  linarith

/-- Il coseno facciale non vale mai 1. -/
theorem cosFacciale_ne_one {p : ℕ} (hp : p = 3 ∨ p = 4 ∨ p = 5) :
    cosFacciale p ≠ 1 := by
  rcases hp with rfl | rfl | rfl
  · norm_num [cosFacciale]
  · norm_num [cosFacciale]
  · rw [cosFacciale]
    norm_num
    intro hcontra
    have h5 : Real.sqrt 5 = -3 := by linarith
    have hpos : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    linarith

/-- Il coseno facciale non vale mai -1. -/
theorem cosFacciale_ne_neg_one {p : ℕ} (hp : p = 3 ∨ p = 4 ∨ p = 5) :
    cosFacciale p ≠ -1 := by
  rcases hp with rfl | rfl | rfl
  · norm_num [cosFacciale]
  · norm_num [cosFacciale]
  · rw [cosFacciale]
    norm_num
    intro hcontra
    -- se √5 = 5, quadrando si avrebbe 5 = 25
    have h5 : Real.sqrt 5 = 5 := by linarith
    have hq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    rw [h5] at hq
    norm_num at hq

/-- **I RAGGI CONSECUTIVI DEL VENTAGLIO SONO INDIPENDENTI**. -/
theorem raggi_consecutivi_indipendenti (P : ConvexPolytope 3) {p q : ℕ}
    (h : P.asFinite.IsCyclicallyRegularOfType p q) {v : E 3}
    (hv : v ∈ P.vertices) (D : P.asFinite.CyclicVertexData v q)
    (i : Fin q) :
    LinearIndependent ℝ
      ![dir P.asFinite v D i, dir P.asFinite v D (finRotate q i)] := by
  classical
  have hpq := (cyclicallyRegular_schlafli P.asFinite h).2
  have hp : p = 3 ∨ p = 4 ∨ p = 5 := by
    rcases hpq with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    all_goals try simp
  have hinner := inner_direzioni_consecutive P.asFinite h hv D i
  refine indipendenti_di_inner_ne
    (dir_unitaria P.asFinite v D i)
    (dir_unitaria P.asFinite v D (finRotate q i)) ?_ ?_
  · rw [hinner]
    exact cosFacciale_ne_one hp
  · rw [hinner]
    exact cosFacciale_ne_neg_one hp

end LeanEval.Geometry.PlatonicClassification
