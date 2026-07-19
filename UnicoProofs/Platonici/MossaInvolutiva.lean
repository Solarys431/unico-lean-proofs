import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FlagAdiacente
import UnicoProofs.Platonici.AdiacenzaUnica

/-!
MOTORE COXETER, PASSO 7 — LA MOSSA INVOLUTIVA (19 lug 2026).

Dal teorema di unicità l'adiacenza diventa una FUNZIONE sulle bandiere:
`adjacentFlag P hfull F i` è l'unica bandiera adiacente a `F` in `i`.
La relazione è simmetrica, quindi la mossa è un'involuzione senza punti
fissi: il germe combinatorio delle riflessioni semplici `rᵢ² = 1`.
-/

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- La bandiera adiacente a `F` al rango `i` (l'unica). -/
noncomputable def adjacentFlag (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (F : P.Flag) (i : Fin n) : P.Flag :=
  (existsUnique_flag_adjacent P hfull F i).choose

theorem adjacentFlag_isAdjacent (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) (i : Fin n) :
    FlagAdjacentAt P F (adjacentFlag P hfull F i) i :=
  (existsUnique_flag_adjacent P hfull F i).choose_spec.1

/-- Ogni bandiera adiacente a `F` in `i` È la bandiera adiacente. -/
theorem adjacentFlag_eq_of_isAdjacent (P : ConvexPolytope n)
    (hfull : P.IsFullDim) {F G : P.Flag} (i : Fin n)
    (h : FlagAdjacentAt P F G i) : G = adjacentFlag P hfull F i :=
  (existsUnique_flag_adjacent P hfull F i).choose_spec.2 G h

/-- L'adiacenza di bandiere è simmetrica. -/
theorem flagAdjacentAt_symm (P : ConvexPolytope n) {F G : P.Flag}
    {i : Fin n} (h : FlagAdjacentAt P F G i) :
    FlagAdjacentAt P G F i :=
  ⟨fun j hj => (h.1 j hj).symm, (h.2).symm⟩

/-- **La mossa è un'involuzione**: andare e tornare riporta a `F`. -/
theorem adjacentFlag_involutive (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) (i : Fin n) :
    adjacentFlag P hfull (adjacentFlag P hfull F i) i = F :=
  (adjacentFlag_eq_of_isAdjacent P hfull i
    (flagAdjacentAt_symm P (adjacentFlag_isAdjacent P hfull F i))).symm

/-- La mossa non ha punti fissi. -/
theorem adjacentFlag_ne (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (F : P.Flag) (i : Fin n) :
    adjacentFlag P hfull F i ≠ F := by
  intro heq
  have h := (adjacentFlag_isAdjacent P hfull F i).2
  rw [heq] at h
  exact h rfl

end LeanEval.Geometry.PlatonicClassification
