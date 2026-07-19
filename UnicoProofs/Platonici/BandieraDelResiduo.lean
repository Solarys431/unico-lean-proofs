import Mathlib
import UnicoProofs.Platonici.FlagAdiacente

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Rimonta simultaneamente due ranghi consecutivi di una bandiera.  Il
rimontaggio simultaneo e necessario: nessuna delle due sostituzioni singole
deve, in generale, essere gia una bandiera. -/
noncomputable def sostituisci_due (P : ConvexPolytope n) (F : P.Flag)
    (i ip : Fin n) (hip : (i : ℕ) + 1 = (ip : ℕ))
    (C D : Set (E n)) (hC : P.IsFace C) (hD : P.IsFace D)
    (hdC : faceDim C = (i : ℕ)) (hdD : faceDim D = (ip : ℕ))
    (hsotto : ∀ j : Fin n, j < i → F.face j ⊂ C)
    (hCD : C ⊂ D)
    (hsopra : ∀ j : Fin n, ip < j → D ⊂ F.face j) : P.Flag where
  face := Function.update (Function.update F.face i C) ip D
  isFace := by
    intro k
    have hi_ne_ip : i ≠ ip := by
      intro h
      have := congrArg Fin.val h
      omega
    by_cases hk_ip : k = ip
    · subst k
      rw [Function.update_self]
      exact hD
    · by_cases hk_i : k = i
      · subst k
        rw [Function.update_of_ne hi_ne_ip, Function.update_self]
        exact hC
      · rw [Function.update_of_ne hk_ip, Function.update_of_ne hk_i]
        exact F.isFace k
  dim_eq := by
    intro k
    have hi_ne_ip : i ≠ ip := by
      intro h
      have := congrArg Fin.val h
      omega
    by_cases hk_ip : k = ip
    · subst k
      rw [Function.update_self]
      exact hdD
    · by_cases hk_i : k = i
      · subst k
        rw [Function.update_of_ne hi_ne_ip, Function.update_self]
        exact hdC
      · rw [Function.update_of_ne hk_ip, Function.update_of_ne hk_i]
        exact F.dim_eq k
  strict_mono := by
    intro j k hjk
    have hi_ne_ip : i ≠ ip := by
      intro h
      have := congrArg Fin.val h
      omega
    by_cases hj_ip : j = ip
    · subst j
      have hk_ip : k ≠ ip := ne_of_gt hjk
      have hk_i : k ≠ i := by
        intro h
        subst k
        rw [Fin.lt_def] at hjk
        omega
      rw [Function.update_self, Function.update_of_ne hk_ip,
        Function.update_of_ne hk_i]
      exact hsopra k hjk
    · by_cases hj_i : j = i
      · subst j
        by_cases hk_ip : k = ip
        · subst k
          rw [Function.update_of_ne hi_ne_ip, Function.update_self,
            Function.update_self]
          exact hCD
        · have hk_i : k ≠ i := ne_of_gt hjk
          have hipk : ip < k := by
            rw [Fin.lt_def] at hjk ⊢
            omega
          rw [Function.update_of_ne hi_ne_ip, Function.update_self,
            Function.update_of_ne hk_ip, Function.update_of_ne hk_i]
          exact hCD.trans (hsopra k hipk)
      · by_cases hk_i : k = i
        · subst k
          rw [Function.update_of_ne hj_ip, Function.update_of_ne hj_i,
            Function.update_of_ne hi_ne_ip, Function.update_self]
          exact hsotto j hjk
        · by_cases hk_ip : k = ip
          · subst k
            have hji : j < i := by
              rw [Fin.lt_def] at hjk ⊢
              have hj_ne_i : (j : ℕ) ≠ (i : ℕ) := by
                intro h
                exact hj_i (Fin.ext h)
              omega
            rw [Function.update_of_ne hj_ip, Function.update_of_ne hj_i,
              Function.update_self]
            exact (hsotto j hji).trans hCD
          · rw [Function.update_of_ne hj_ip, Function.update_of_ne hj_i,
              Function.update_of_ne hk_ip, Function.update_of_ne hk_i]
            exact F.strict_mono j k hjk

theorem bandiera_del_residuo (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    {C : Set (E n)} (hC : P.IsFace C) (hdC : faceDim C = (i : ℕ))
    (hsotto : ∀ k : Fin n, (k : ℕ) < (i : ℕ) → F.face k ⊂ C)
    (hsopra : C ⊂ F.face ⟨(i : ℕ) + 1, hi⟩) :
    ∃ G : P.Flag,
      (∀ k : Fin n, k ≠ i → (k : ℕ) ≠ (i : ℕ) + 1 →
        G.face k = F.face k) ∧
      G.face i = C := by
  let ip : Fin n := ⟨(i : ℕ) + 1, hi⟩
  have hsotto' : ∀ j : Fin n, j < i → F.face j ⊂ C := by
    intro j hj
    exact hsotto j hj
  have hsopra' : ∀ j : Fin n, i < j → C ⊂ F.face j :=
    catena_sopra P F (i := i) (ip := ip) (by rfl) hsopra
  let G := sostituisci P F i C hC hdC hsotto' hsopra'
  refine ⟨G, ?_, ?_⟩
  · intro k hk_i _
    exact sostituisci_face_ne P F i C hC hdC hsotto' hsopra' hk_i
  · exact sostituisci_face_self P F i C hC hdC hsotto' hsopra'

theorem bandiera_del_residuo_generale (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hi2 : (i : ℕ) + 2 < n)
    {C : Set (E n)} (hC : P.IsFace C) (hdC : faceDim C = (i : ℕ))
    (hsotto : ∀ k : Fin n, (k : ℕ) < (i : ℕ) → F.face k ⊂ C)
    (hsopra : C ⊂ F.face ⟨(i : ℕ) + 2, hi2⟩) :
    ∃ G : P.Flag,
      (∀ k : Fin n, k ≠ i → (k : ℕ) ≠ (i : ℕ) + 1 →
        G.face k = F.face k) ∧
      G.face i = C := by
  let ip : Fin n := ⟨(i : ℕ) + 1, hi⟩
  let ip2 : Fin n := ⟨(i : ℕ) + 2, hi2⟩
  have hrank : faceDim (F.face ip2) = faceDim C + 2 := by
    rw [F.dim_eq ip2, hdC]
  obtain ⟨D, hD, hCD, hDtop, hdD0⟩ :=
    faccia_intermedia P hC (F.isFace ip2) hsopra hrank
  have hdD : faceDim D = (ip : ℕ) := by
    rw [hdD0, hdC]
  have hsotto' : ∀ j : Fin n, j < i → F.face j ⊂ C := by
    intro j hj
    exact hsotto j hj
  have hsopra' : ∀ j : Fin n, ip < j → D ⊂ F.face j :=
    catena_sopra P F (i := ip) (ip := ip2) (by rfl) hDtop
  let G := sostituisci_due P F i ip (by rfl) C D hC hD hdC hdD
    hsotto' hCD hsopra'
  have hi_ne_ip : i ≠ ip := by
    intro h
    have := congrArg Fin.val h
    omega
  refine ⟨G, ?_, ?_⟩
  · intro k hk_i hk_ip_val
    have hk_ip : k ≠ ip := by
      intro h
      apply hk_ip_val
      rw [h]
    simp only [G, sostituisci_due, Function.update_of_ne hk_ip,
      Function.update_of_ne hk_i]
  · simp only [G, sostituisci_due, Function.update_of_ne hi_ne_ip,
      Function.update_self]

theorem bandiera_del_residuo_al_bordo (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hbordo : (i : ℕ) + 2 = n)
    {C : Set (E n)} (hC : P.IsFace C) (hdC : faceDim C = (i : ℕ))
    (hsotto : ∀ k : Fin n, (k : ℕ) < (i : ℕ) → F.face k ⊂ C)
    (hsopra : C ⊂ P.toSet) :
    ∃ G : P.Flag,
      (∀ k : Fin n, k ≠ i → (k : ℕ) ≠ (i : ℕ) + 1 →
        G.face k = F.face k) ∧
      G.face i = C := by
  let ip : Fin n := ⟨(i : ℕ) + 1, hi⟩
  have htopdim : faceDim P.toSet = n := hfull
  have hrank : faceDim P.toSet = faceDim C + 2 := by
    rw [htopdim, hdC]
    omega
  obtain ⟨D, hD, hCD, hDtop, hdD0⟩ :=
    faccia_intermedia P hC (toSet_isFace P) hsopra hrank
  have hdD : faceDim D = (ip : ℕ) := by
    rw [hdD0, hdC]
  have hsotto' : ∀ j : Fin n, j < i → F.face j ⊂ C := by
    intro j hj
    exact hsotto j hj
  have hsopra' : ∀ j : Fin n, ip < j → D ⊂ F.face j := by
    intro j hj
    exfalso
    rw [Fin.lt_def] at hj
    have := j.isLt
    omega
  let G := sostituisci_due P F i ip (by rfl) C D hC hD hdC hdD
    hsotto' hCD hsopra'
  have hi_ne_ip : i ≠ ip := by
    intro h
    have := congrArg Fin.val h
    omega
  refine ⟨G, ?_, ?_⟩
  · intro k hk_i hk_ip_val
    have hk_ip : k ≠ ip := by
      intro h
      apply hk_ip_val
      rw [h]
    simp only [G, sostituisci_due, Function.update_of_ne hk_ip,
      Function.update_of_ne hk_i]
  · simp only [G, sostituisci_due, Function.update_of_ne hi_ne_ip,
      Function.update_self]

end LeanEval.Geometry.PlatonicClassification
