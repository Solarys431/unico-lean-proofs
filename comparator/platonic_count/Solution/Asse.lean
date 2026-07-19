import Mathlib

open scoped RealInnerProductSpace
open Fin.NatCast

/-!
R1b (campagna #50): L'ASSE DEL FAN CICLICO.

Se un'isometria lineare L permuta ciclicamente i vettori u₀,…,u_{q−1}
(L(uᵢ) = u_{i+1}), allora dalla SOLA simmetria seguono:
  · `asse_invariante`  — la somma w = Σuᵢ è un vettore L-fisso (l'asse);
  · `colatitudine_comune` — i prodotti ⟪uⱼ, w⟫ sono tutti uguali
    (e la loro somma è ‖w‖²: puntatezza non appena w ≠ 0);
  · `passo_costante` — i prodotti fra consecutivi ⟪uⱼ, u_{j+1}⟫ sono uguali.
Il motore è `ciclo_costante`: una funzione invariante per il passo del ciclo
è costante su Fin q.
-/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Una funzione su `Fin (n+1)` invariante per `finRotate` è costante. -/
lemma ciclo_costante {n : ℕ} (g : Fin (n + 1) → ℝ)
    (h : ∀ i, g (finRotate (n + 1) i) = g i) : ∀ i j, g i = g j := by
  have hiter : ∀ (m : ℕ) (i : Fin (n + 1)), (finRotate (n + 1))^[m] i = i + (↑m : Fin (n + 1)) := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ k ih =>
        intro i
        rw [Function.iterate_succ_apply', ih, finRotate_succ_apply,
          Nat.cast_succ]
        exact add_assoc i (↑k) 1
  have hstep : ∀ (m : ℕ) (i : Fin (n + 1)), g ((finRotate (n + 1))^[m] i) = g i := by
    intro m
    induction m with
    | zero => intro i; rfl
    | succ k ih => intro i; rw [Function.iterate_succ_apply', h, ih]
  intro i j
  have hm : (finRotate (n + 1))^[((j - i : Fin (n + 1)) : ℕ)] i = j := by
    have h1 := hiter ((j - i : Fin (n + 1)) : ℕ) i
    simp only [Fin.cast_val_eq_self] at h1
    rw [h1]
    abel
  calc g i = g ((finRotate (n + 1))^[((j - i : Fin (n + 1)) : ℕ)] i) := (hstep _ i).symm
    _ = g j := by rw [hm]

/-- L'asse: la somma di un ciclo di vettori è fissata dall'isometria che li ruota. -/
theorem asse_invariante {q : ℕ} (L : V ≃ₗᵢ[ℝ] V) (u : Fin q → V)
    (hL : ∀ i, L (u i) = u (finRotate q i)) :
    L (∑ i, u i) = ∑ i, u i := by
  rw [map_sum]
  simp_rw [hL]
  exact Equiv.sum_comp (finRotate q) u

/-- Colatitudine comune: ogni ⟪uⱼ, w⟫ vale lo stesso (dalla sola simmetria). -/
theorem colatitudine_comune {n : ℕ} (L : V ≃ₗᵢ[ℝ] V) (u : Fin (n + 1) → V)
    (hL : ∀ i, L (u i) = u (finRotate (n + 1) i)) (j k : Fin (n + 1)) :
    ⟪u j, ∑ i, u i⟫ = ⟪u k, ∑ i, u i⟫ := by
  apply ciclo_costante (fun i => ⟪u i, ∑ i, u i⟫)
  intro i
  calc ⟪u (finRotate (n + 1) i), ∑ i, u i⟫
      = ⟪L (u i), L (∑ i, u i)⟫ := by rw [hL, asse_invariante L u hL]
    _ = ⟪u i, ∑ i, u i⟫ := L.inner_map_map _ _

/-- La somma delle colatitudini è ‖w‖²: da qui, con w ≠ 0, la puntatezza. -/
theorem somma_colatitudini {n : ℕ} (L : V ≃ₗᵢ[ℝ] V) (u : Fin (n + 1) → V)
    (hL : ∀ i, L (u i) = u (finRotate (n + 1) i)) (j : Fin (n + 1)) :
    (n + 1 : ℝ) * ⟪u j, ∑ i, u i⟫ = ‖∑ i, u i‖ ^ 2 := by
  have hconst := colatitudine_comune L u hL
  have hsum : ∑ i, ⟪u i, ∑ k, u k⟫ = ‖∑ i, u i‖ ^ 2 := by
    rw [← sum_inner, real_inner_self_eq_norm_sq]
  calc (n + 1 : ℝ) * ⟪u j, ∑ i, u i⟫
      = ∑ _i : Fin (n + 1), ⟪u j, ∑ k, u k⟫ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        push_cast; ring
    _ = ∑ i, ⟪u i, ∑ k, u k⟫ := Finset.sum_congr rfl fun i _ => hconst j i
    _ = ‖∑ i, u i‖ ^ 2 := hsum

/-- Il passo del fan è costante: ⟪uⱼ, u_{j+1}⟫ non dipende da j. -/
theorem passo_costante {n : ℕ} (L : V ≃ₗᵢ[ℝ] V) (u : Fin (n + 1) → V)
    (hL : ∀ i, L (u i) = u (finRotate (n + 1) i)) (j k : Fin (n + 1)) :
    ⟪u j, u (finRotate (n + 1) j)⟫ = ⟪u k, u (finRotate (n + 1) k)⟫ := by
  apply ciclo_costante (fun i => ⟪u i, u (finRotate (n + 1) i)⟫)
  intro i
  calc ⟪u (finRotate (n + 1) i), u (finRotate (n + 1) (finRotate (n + 1) i))⟫
      = ⟪L (u i), L (u (finRotate (n + 1) i))⟫ := by rw [hL, hL]
    _ = ⟪u i, u (finRotate (n + 1) i)⟫ := L.inner_map_map _ _

/-- L'innesto del funzionale espositore: se un funzionale è positivo su ogni
vettore del ciclo, la loro somma (l'asse) non è nulla. -/
theorem asse_non_nullo {q : ℕ} (u : Fin q → V) (f : V →L[ℝ] ℝ)
    (hpos : ∀ i, 0 < f (u i)) (hq : 0 < q) : (∑ i, u i) ≠ 0 := by
  intro h0
  haveI : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp hq
  have hsum : (0 : ℝ) < f (∑ i, u i) := by
    rw [map_sum]
    exact Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty
  rw [h0] at hsum
  simp at hsum

/-- PUNTATEZZA DEL CONO: simmetria ciclica + funzionale espositore ⟹ ogni
vettore del ciclo ha prodotto strettamente positivo con l'asse. È il «0 < β»
che alimenta lo spike del difetto angolare. -/
theorem puntatezza {n : ℕ} (L : V ≃ₗᵢ[ℝ] V) (u : Fin (n + 1) → V)
    (hL : ∀ i, L (u i) = u (finRotate (n + 1) i))
    (f : V →L[ℝ] ℝ) (hpos : ∀ i, 0 < f (u i)) (j : Fin (n + 1)) :
    0 < ⟪u j, ∑ i, u i⟫ := by
  have hw0 : (∑ i, u i) ≠ 0 :=
    asse_non_nullo u f hpos (Nat.succ_pos n)
  have hnorm : (0 : ℝ) < ‖∑ i, u i‖ ^ 2 := by
    have := norm_pos_iff.mpr hw0
    positivity
  have hsc := somma_colatitudini L u hL j
  nlinarith [hsc, hnorm]
