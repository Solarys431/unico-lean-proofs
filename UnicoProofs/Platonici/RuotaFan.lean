import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FanVertice

/-!
RIGIDITÀ — IL RIALLINEAMENTO DEI VENTAGLI (19 lug 2026).

Due politopi consegnano i loro ventagli con enumerazioni qualsiasi: per
confrontarli occorre poterli far partire dalla stessa faccetta. Qui la
rotazione dell'enumerazione, `ruotato D k`, che è un `CyclicVertexData`
a tutti gli effetti: nessuna geometria, solo il fatto che sommare una
costante commuta con l'aggiungere uno.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

variable {P : FiniteConvexPolytope (E 3)} {v : E 3} {q : ℕ}

/-- Il passo del fan commuta con lo spostamento dell'origine. -/
theorem finRotate_add_costante {m : ℕ} (i k : Fin (m + 1)) :
    finRotate (m + 1) (i + k) = finRotate (m + 1) i + k := by
  rw [finRotate_succ_apply, finRotate_succ_apply]
  exact add_right_comm i k 1

/-- **IL VENTAGLIO RIALLINEATO**: la stessa struttura ciclica, enumerata
a partire dalla faccetta `k`. -/
def ruotato {m : ℕ} (D : P.CyclicVertexData v (m + 1)) (k : Fin (m + 1)) :
    P.CyclicVertexData v (m + 1) where
  faccetta := fun i => D.faccetta (i + k)
  isFacet := fun i => D.isFacet (i + k)
  mem_v := fun i => D.mem_v (i + k)
  distinte := by
    intro i j hij
    have h := D.distinte hij
    exact add_right_cancel h
  complete := by
    intro F hF hvF
    obtain ⟨j, hj⟩ := D.complete F hF hvF
    refine ⟨j - k, ?_⟩
    rw [hj]
    congr 1
    exact (sub_add_cancel j k).symm
  σ := D.σ
  fissa_v := D.fissa_v
  preserva := D.preserva
  ruota := by
    intro i
    have h := D.ruota (i + k)
    rw [h, finRotate_add_costante]
  spigolo := by
    intro i
    obtain ⟨x, hxv, hx⟩ := D.spigolo (i + k)
    refine ⟨x, hxv, hx.1, ?_⟩
    have hrot : finRotate (m + 1) (i + k) =
        finRotate (m + 1) i + k := finRotate_add_costante i k
    rw [← hrot]
    exact hx.2
  spigolo_due := by
    intro i j x hx hxv hxj
    have hrot : finRotate (m + 1) (i + k) =
        finRotate (m + 1) i + k := finRotate_add_costante i k
    have hx' : x ∈ D.faccetta (i + k) ∩
        D.faccetta (finRotate (m + 1) (i + k)) := by
      rw [hrot]
      exact hx
    have hcase := D.spigolo_due (i + k) (j + k) x hx' hxv hxj
    rcases hcase with hc | hc
    · exact Or.inl (add_right_cancel hc)
    · refine Or.inr ?_
      rw [hrot] at hc
      exact add_right_cancel hc

@[simp] theorem ruotato_faccetta {m : ℕ} (D : P.CyclicVertexData v (m + 1))
    (k i : Fin (m + 1)) : (ruotato D k).faccetta i = D.faccetta (i + k) :=
  rfl

@[simp] theorem ruotato_sigma {m : ℕ} (D : P.CyclicVertexData v (m + 1))
    (k : Fin (m + 1)) : (ruotato D k).σ = D.σ := rfl

/-- Ogni faccetta del ventaglio può essere portata all'indice zero. -/
theorem esiste_riallineamento {m : ℕ} (D : P.CyclicVertexData v (m + 1))
    (k : Fin (m + 1)) : (ruotato D k).faccetta 0 = D.faccetta k := by
  show D.faccetta (0 + k) = D.faccetta k
  rw [zero_add]

end LeanEval.Geometry.PlatonicClassification
