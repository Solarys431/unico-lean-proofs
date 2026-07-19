import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FlagAdiacente
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.MossaInvolutiva

/-!
MOTORE COXETER, PASSO 10 — LA COMMUTAZIONE LONTANA (19 lug 2026).

Per ranghi non adiacenti (`i + 2 ≤ j`) le mosse di adiacenza COMMUTANO:
`adj_i (adj_j F) = adj_j (adj_i F)`. È un fatto puramente combinatorio
dell'unicità: la bandiera `H` che differisce da `F` esattamente nei due
ranghi `i` e `j` è adiacente in `i` ad `adj_j F` e adiacente in `j` ad
`adj_i F`; l'∃! la identifica con entrambi i lati. Il punto geometrico
è uno solo: le due facce nuove restano incastrate (`C_i ⊂ C_j`) perché
tra loro c'è la catena invariata `F.face (i+1) ⊆ F.face (j−1)`.

È il germe della relazione di Coxeter `(rᵢ rⱼ)² = 1` per `|i−j| ≥ 2`.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- **La commutazione lontana delle mosse**: per `i + 2 ≤ j`,
`adj_i (adj_j F) = adj_j (adj_i F)`. -/
theorem adjacentFlag_comm (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (F : P.Flag) {i j : Fin n} (hij : (i : ℕ) + 2 ≤ (j : ℕ)) :
    adjacentFlag P hfull (adjacentFlag P hfull F j) i =
      adjacentFlag P hfull (adjacentFlag P hfull F i) j := by
  have hAdjA := adjacentFlag_isAdjacent P hfull F i
  have hAdjB := adjacentFlag_isAdjacent P hfull F j
  set A := adjacentFlag P hfull F i with hA_def
  set B := adjacentFlag P hfull F j with hB_def
  have hi1n : (i : ℕ) + 1 < n := by
    have := j.isLt
    omega
  have hj1n : (j : ℕ) - 1 < n := by
    have := j.isLt
    omega
  have hCface : P.IsFace (A.face i) := A.isFace i
  have hCdim : faceDim (A.face i) = (i : ℕ) := A.dim_eq i
  -- la catena sotto il rango i, vista dentro B
  have hsotto : ∀ k : Fin n, k < i → B.face k ⊂ A.face i := by
    intro k hk
    have hkj : k ≠ j := fun he => by
      rw [Fin.lt_def] at hk
      have hv : (k : ℕ) = (j : ℕ) := congrArg Fin.val he
      omega
    have hki : k ≠ i := ne_of_lt hk
    rw [hAdjB.1 k hkj, ← hAdjA.1 k hki]
    exact A.strict_mono k i hk
  -- la catena sopra il rango i, vista dentro B (il nodo: C_i ⊂ C_j)
  have hsopra : ∀ k : Fin n, i < k → A.face i ⊂ B.face k := by
    intro k hk
    by_cases hkj : k = j
    · rw [hkj]
      have h1 : A.face i ⊂ A.face ⟨(i : ℕ) + 1, hi1n⟩ := by
        refine A.strict_mono i _ ?_
        rw [Fin.lt_def]
        show (i : ℕ) < (i : ℕ) + 1
        omega
      have h1' : A.face ⟨(i : ℕ) + 1, hi1n⟩ =
          F.face ⟨(i : ℕ) + 1, hi1n⟩ := by
        refine hAdjA.1 _ (fun he => ?_)
        have hv : (i : ℕ) + 1 = (i : ℕ) := congrArg Fin.val he
        omega
      have h2 : F.face ⟨(i : ℕ) + 1, hi1n⟩ ⊆
          F.face ⟨(j : ℕ) - 1, hj1n⟩ := by
        rcases Nat.lt_or_ge ((i : ℕ) + 1) ((j : ℕ) - 1) with hlt | hge
        · refine (F.strict_mono _ _ ?_).subset
          rw [Fin.lt_def]
          show (i : ℕ) + 1 < (j : ℕ) - 1
          exact hlt
        · have he : (⟨(i : ℕ) + 1, hi1n⟩ : Fin n) = ⟨(j : ℕ) - 1, hj1n⟩ := by
            apply Fin.ext
            show (i : ℕ) + 1 = (j : ℕ) - 1
            omega
          rw [he]
      have h3 : F.face ⟨(j : ℕ) - 1, hj1n⟩ = B.face ⟨(j : ℕ) - 1, hj1n⟩ := by
        refine (hAdjB.1 _ (fun he => ?_)).symm
        have hv : (j : ℕ) - 1 = (j : ℕ) := congrArg Fin.val he
        omega
      have h4 : B.face ⟨(j : ℕ) - 1, hj1n⟩ ⊂ B.face j := by
        refine B.strict_mono _ j ?_
        rw [Fin.lt_def]
        show (j : ℕ) - 1 < (j : ℕ)
        omega
      have hstep : A.face i ⊂ F.face ⟨(j : ℕ) - 1, hj1n⟩ := by
        refine ssubset_of_ssubset_of_subset ?_ h2
        rw [← h1']
        exact h1
      rw [h3] at hstep
      exact hstep.trans h4
    · have hki : k ≠ i := (ne_of_lt hk).symm
      rw [hAdjB.1 k hkj, ← hAdjA.1 k hki]
      exact A.strict_mono i k hk
  -- H = B con la faccia i sostituita da C_i è adiacente a B in i…
  have hHB : FlagAdjacentAt P B
      (sostituisci P B i (A.face i) hCface hCdim hsotto hsopra) i := by
    constructor
    · intro k hk
      exact sostituisci_face_ne P B i (A.face i) hCface hCdim hsotto hsopra hk
    · rw [sostituisci_face_self]
      have hBi : B.face i = F.face i := by
        refine hAdjB.1 i (fun he => ?_)
        have hv : (i : ℕ) = (j : ℕ) := congrArg Fin.val he
        omega
      rw [hBi]
      exact hAdjA.2
  -- …ed è adiacente ad A in j.
  have hHA : FlagAdjacentAt P A
      (sostituisci P B i (A.face i) hCface hCdim hsotto hsopra) j := by
    constructor
    · intro k hk
      by_cases hki : k = i
      · rw [hki, sostituisci_face_self]
      · rw [sostituisci_face_ne P B i (A.face i) hCface hCdim hsotto hsopra
          hki, hAdjB.1 k hk, hAdjA.1 k hki]
    · have hji : j ≠ i := fun he => by
        have hv : (j : ℕ) = (i : ℕ) := congrArg Fin.val he
        omega
      rw [sostituisci_face_ne P B i (A.face i) hCface hCdim hsotto hsopra hji]
      have hAj : A.face j = F.face j := hAdjA.1 j hji
      rw [hAj]
      exact hAdjB.2
  have e1 : sostituisci P B i (A.face i) hCface hCdim hsotto hsopra =
      adjacentFlag P hfull B i :=
    adjacentFlag_eq_of_isAdjacent P hfull i hHB
  have e2 : sostituisci P B i (A.face i) hCface hCdim hsotto hsopra =
      adjacentFlag P hfull A j :=
    adjacentFlag_eq_of_isAdjacent P hfull j hHA
  rw [← e1, ← e2]

/-- La commutazione nelle due direzioni (`|i − j| ≥ 2`). -/
theorem adjacentFlag_comm_far (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (F : P.Flag) {i j : Fin n}
    (hij : (i : ℕ) + 2 ≤ (j : ℕ) ∨ (j : ℕ) + 2 ≤ (i : ℕ)) :
    adjacentFlag P hfull (adjacentFlag P hfull F j) i =
      adjacentFlag P hfull (adjacentFlag P hfull F i) j := by
  rcases hij with h | h
  · exact adjacentFlag_comm P hfull F h
  · exact (adjacentFlag_comm P hfull F h).symm

end LeanEval.Geometry.PlatonicClassification
