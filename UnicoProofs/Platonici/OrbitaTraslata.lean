import Mathlib

/-!
A10 — L'ORBITA TRASLATA E IL VERTICE NEL POLIGONO (campagna #50, assemblaggio).

La faccetta regolare è l'hull dell'orbita di ρ da un punto x₀ QUALSIASI; il
nostro vertice v è un punto estremo della faccetta, quindi STA nell'orbita,
ma in generale v = ρ^[k] x₀ con k ≠ 0. Questi lemmi trasferiscono chiusura,
iniettività e range dall'orbita di x₀ all'orbita di v: così il teorema
dell'angolo interno (AngoloInterno, via la carta A8) si applica con base v.
Più due lemmi di estremalità: l'estremalità si eredita ai sottoinsiemi, e un
punto estremo dell'hull di un insieme sta nell'insieme.
-/

namespace PlatoniciA10

section OrbitaTraslata

variable {α : Type*} (f : α → α) (x : α) (p : ℕ)

/-- La chiusura del ciclo si estende ai multipli. -/
theorem iterate_multiplo (hp : f^[p] x = x) (m : ℕ) : f^[p * m] x = x := by
  induction m with
  | zero => simp
  | succ n ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, hp, ih]

/-- L'orbita è periodica: l'esponente si legge modulo p. -/
theorem iterate_mod (hp : f^[p] x = x) (a : ℕ) : f^[a] x = f^[a % p] x := by
  conv_lhs => rw [← Nat.mod_add_div a p]
  rw [Function.iterate_add_apply, iterate_multiplo f x p hp]

/-- La chiusura del ciclo vale da ogni punto dell'orbita. -/
theorem orbita_traslata_chiusa (hp : f^[p] x = x) (k : ℕ) :
    f^[p] (f^[k] x) = f^[k] x := by
  rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hp]

/-- L'iniettività del ciclo vale da ogni punto dell'orbita. -/
theorem orbita_traslata_iniettiva (hp0 : 0 < p) (hp : f^[p] x = x)
    (hinj : Function.Injective (fun i : Fin p => f^[(i : ℕ)] x)) (k : ℕ) :
    Function.Injective (fun i : Fin p => f^[(i : ℕ)] (f^[k] x)) := by
  intro i j hij
  have h1 : f^[((i : ℕ) + k) % p] x = f^[((j : ℕ) + k) % p] x := by
    rw [← iterate_mod f x p hp, ← iterate_mod f x p hp,
      Function.iterate_add_apply, Function.iterate_add_apply]
    exact hij
  have h2 : (⟨((i : ℕ) + k) % p, Nat.mod_lt _ hp0⟩ : Fin p)
      = ⟨((j : ℕ) + k) % p, Nat.mod_lt _ hp0⟩ := hinj h1
  have h3 := congrArg Fin.val h2
  simp only [] at h3
  apply Fin.ext
  have hi : (i : ℕ) < p := i.isLt
  have hj : (j : ℕ) < p := j.isLt
  have := Nat.ModEq.add_right_cancel' k
    (show ((i : ℕ) + k) ≡ ((j : ℕ) + k) [MOD p] by
      unfold Nat.ModEq
      exact h3)
  unfold Nat.ModEq at this
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  exact this

/-- Il range dell'orbita non dipende dal punto di partenza sull'orbita. -/
theorem orbita_traslata_range (hp0 : 0 < p) (hp : f^[p] x = x) (k : ℕ) :
    Set.range (fun i : Fin p => f^[(i : ℕ)] (f^[k] x))
      = Set.range (fun i : Fin p => f^[(i : ℕ)] x) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨⟨((i : ℕ) + k) % p, Nat.mod_lt _ hp0⟩, ?_⟩
    show f^[((i : ℕ) + k) % p] x = f^[(i : ℕ)] (f^[k] x)
    rw [← iterate_mod f x p hp, Function.iterate_add_apply]
  · rintro ⟨i, rfl⟩
    refine ⟨⟨((i : ℕ) + (p - k % p)) % p, Nat.mod_lt _ hp0⟩, ?_⟩
    show f^[((i : ℕ) + (p - k % p)) % p] (f^[k] x) = f^[(i : ℕ)] x
    have hdm := Nat.div_add_mod k p
    have hk : k % p < p := Nat.mod_lt _ hp0
    have harit : (((i : ℕ) + (p - k % p)) % p + k) % p = (i : ℕ) % p := by
      rw [Nat.mod_add_mod]
      rw [show (i : ℕ) + (p - k % p) + k = (i : ℕ) + (p + p * (k / p)) by omega]
      rw [show p + p * (k / p) = p * (1 + k / p) by ring]
      rw [Nat.add_mul_mod_self_left]
    calc f^[((i : ℕ) + (p - k % p)) % p] (f^[k] x)
        = f^[((i : ℕ) + (p - k % p)) % p + k] x :=
          (Function.iterate_add_apply f _ k x).symm
      _ = f^[(((i : ℕ) + (p - k % p)) % p + k) % p] x :=
          iterate_mod f x p hp _
      _ = f^[(i : ℕ) % p] x := by rw [harit]
      _ = f^[(i : ℕ)] x := (iterate_mod f x p hp _).symm

end OrbitaTraslata

section Estremi

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- L'estremalità si eredita ai sottoinsiemi. -/
theorem estremo_ereditato {S F : Set A} (hFS : F ⊆ S) {v : A}
    (hvex : v ∈ S.extremePoints ℝ) (hvF : v ∈ F) :
    v ∈ F.extremePoints ℝ := by
  rw [mem_extremePoints] at hvex ⊢
  exact ⟨hvF, fun x₁ hx₁ x₂ hx₂ hseg =>
    hvex.2 x₁ (hFS hx₁) x₂ (hFS hx₂) hseg⟩

/-- Un punto estremo dell'hull di un'orbita finita sta nell'orbita. -/
theorem estremo_in_orbita {α : Type*} (f : α → A) {v : A}
    (hvex : v ∈ (convexHull ℝ (Set.range f)).extremePoints ℝ) :
    ∃ i, f i = v := by
  have := extremePoints_convexHull_subset hvex
  exact this

end Estremi

end PlatoniciA10
