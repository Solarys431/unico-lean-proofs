import Mathlib

/-!
A4 — L'ORDINE DEL PASSO (campagna #50, assemblaggio).

Se q direzioni non nulle e DISTINTE sono permutate ciclicamente da una
rotazione di passo θ nel piano, allora θ ha ordine additivo esattamente q.
È l'ipotesi `hord` di `passo_del_fan`: con la colla A1-A3 chiude la catena
politopo → killer. La distinzione delle direzioni verrà da `spigolo_due`.
-/

open Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

namespace PlatoniciA4

/-- Le iterate di una rotazione sono la rotazione dell'angolo multiplo. -/
theorem rotation_iterate (o : Orientation ℝ E (Fin 2)) (θ : Real.Angle)
    (x : E) (k : ℕ) :
    (⇑(o.rotation θ))^[k] x = o.rotation ((k : ℕ) • θ) x := by
  induction k with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, o.rotation_rotation, succ_nsmul,
        add_comm θ ((m : ℕ) • θ)]

/-- L'orbita di 0 sotto finRotate percorre i valori in ordine. -/
theorem finRotate_iterate_zero (n : ℕ) (k : ℕ) (hk : k < n + 1) :
    (⇑(finRotate (n + 1)))^[k] (0 : Fin (n + 1)) = ⟨k, hk⟩ := by
  induction k with
  | zero => rfl
  | succ m ih =>
      have hm : m < n + 1 := Nat.lt_of_succ_lt hk
      rw [Function.iterate_succ_apply', ih hm, finRotate_succ_apply]
      apply Fin.ext
      rw [Fin.val_add_one_of_lt' (by simpa using hk)]

/-- Dopo n+1 passi l'orbita di finRotate si chiude. -/
theorem finRotate_iterate_full (n : ℕ) :
    (⇑(finRotate (n + 1)))^[n + 1] (0 : Fin (n + 1)) = 0 := by
  rw [Function.iterate_succ_apply',
    finRotate_iterate_zero n n (Nat.lt_succ_self n)]
  exact finRotate_last

/-- A4 — q direzioni non nulle distinte permutate ciclicamente dalla
rotazione di passo θ ⟹ addOrderOf θ = q. -/
theorem ordine_del_passo (o : Orientation ℝ E (Fin 2)) (θ : Real.Angle)
    (q : ℕ) (hq : 3 ≤ q) (u : Fin q → E)
    (hu : ∀ i, u i ≠ 0)
    (hstep : ∀ i : Fin q, u (finRotate q i) = o.rotation θ (u i))
    (hdist : Function.Injective u) :
    addOrderOf θ = q := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  have horb : ∀ k : ℕ, u ((⇑(finRotate (n + 1)))^[k] (0 : Fin (n + 1)))
      = (⇑(o.rotation θ))^[k] (u 0) := by
    intro k
    induction k with
    | zero => rfl
    | succ m ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          hstep, ih]
  rw [addOrderOf_eq_iff (by omega : 0 < n + 1)]
  constructor
  · have h1 := horb (n + 1)
    rw [finRotate_iterate_full, rotation_iterate] at h1
    rcases (o.rotation_eq_self_iff (u 0) ((n + 1 : ℕ) • θ)).mp h1.symm with h | h
    · exact absurd h (hu 0)
    · exact h
  · intro m hm hm0 hcontra
    have h2 := horb m
    rw [finRotate_iterate_zero n m hm, rotation_iterate, hcontra,
      o.rotation_zero] at h2
    have hval := congrArg Fin.val (hdist h2)
    simp only [Fin.val_zero] at hval
    omega

end PlatoniciA4
