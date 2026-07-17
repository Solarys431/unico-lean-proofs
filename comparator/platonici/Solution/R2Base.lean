import Mathlib

open Finset

/-!
R2-P1/P2 (campagna #50): le fondamenta del p-gono regolare per orbita.
P1: il baricentro dell'orbita ciclica è fisso per ρ.
P2: l'orbita è cocircolare attorno a ogni punto ρ-fisso.
-/

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- P2 — cocircolarità: l'orbita di un'isometria sta a distanza costante da
ogni punto fisso. -/
theorem orbita_cocircolare (ρ : A ≃ᵃⁱ[ℝ] A) (x₀ c : A) (hc : ρ c = c) :
    ∀ m : ℕ, dist ((⇑ρ)^[m] x₀) c = dist x₀ c := by
  intro m
  induction m with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc dist (ρ ((⇑ρ)^[n] x₀)) c
          = dist (ρ ((⇑ρ)^[n] x₀)) (ρ c) := by rw [hc]
        _ = dist ((⇑ρ)^[n] x₀) c := ρ.dist_map _ _
        _ = dist x₀ c := ih

/-- La rotazione dell'orbita: applicare ρ equivale a rileggere l'orbita col
passo del ciclo (con la chiusura ρ^[p+1] x₀ = x₀ sull'ultimo). -/
theorem rho_comp_orbita {p : ℕ} (ρ : A ≃ᵃⁱ[ℝ] A) (x₀ : A)
    (hchiude : (⇑ρ)^[p + 1] x₀ = x₀) :
    (fun i : Fin (p + 1) => ρ ((⇑ρ)^[(i : ℕ)] x₀))
      = (fun i : Fin (p + 1) => (⇑ρ)^[((finRotate (p + 1) i : Fin (p + 1)) : ℕ)] x₀) := by
  funext i
  rcases Fin.lt_or_eq_of_le (Fin.le_last i) with hlt | hlast
  · have hval : ((finRotate (p + 1) i : Fin (p + 1)) : ℕ) = (i : ℕ) + 1 := by
      rw [finRotate_succ_apply]
      exact Fin.val_add_one_of_lt hlt
    rw [hval, Function.iterate_succ_apply']
  · subst hlast
    have hval : ((finRotate (p + 1) (Fin.last p) : Fin (p + 1)) : ℕ) = 0 := by
      rw [finRotate_succ_apply]
      simp
    rw [hval]
    show ρ ((⇑ρ)^[p] x₀) = x₀
    exact (Function.iterate_succ_apply' (⇑ρ) p x₀).symm.trans hchiude

set_option maxHeartbeats 800000 in
/-- P1 — il baricentro dell'orbita è ρ-fisso. -/
theorem orbita_centroid_fisso {p : ℕ} (ρ : A ≃ᵃⁱ[ℝ] A) (x₀ : A)
    (hchiude : (⇑ρ)^[p + 1] x₀ = x₀) :
    ρ (Finset.univ.centroid ℝ (fun i : Fin (p + 1) => (⇑ρ)^[(i : ℕ)] x₀))
      = Finset.univ.centroid ℝ (fun i : Fin (p + 1) => (⇑ρ)^[(i : ℕ)] x₀) := by
  set orb : Fin (p + 1) → A := fun i => (⇑ρ)^[(i : ℕ)] x₀ with horb
  have hsum : ∑ i ∈ Finset.univ, Finset.univ.centroidWeights ℝ (ι := Fin (p + 1)) i = 1 :=
    Finset.univ.sum_centroidWeights_eq_one_of_nonempty ℝ Finset.univ_nonempty
  -- ρ commuta con la combinazione affine
  have hmap : ρ (Finset.univ.centroid ℝ orb)
      = Finset.univ.centroid ℝ (fun i => ρ (orb i)) := by
    rw [Finset.centroid_def, Finset.centroid_def]
    exact Finset.univ.map_affineCombination orb _ hsum ρ.toAffineIsometry.toAffineMap
  rw [hmap]
  -- e la rilettura ciclica non cambia il baricentro
  have hciclo := rho_comp_orbita ρ x₀ hchiude
  rw [show (fun i => ρ (orb i)) = (fun i : Fin (p + 1) => orb (finRotate (p + 1) i)) from hciclo]
  calc Finset.univ.centroid ℝ (fun i => orb (finRotate (p + 1) i))
      = (Finset.univ.map (finRotate (p + 1)).toEmbedding).centroid ℝ orb :=
        (Finset.centroid_map (k := ℝ) (s₂ := Finset.univ)
          (e := (finRotate (p + 1)).toEmbedding) orb).symm
    _ = Finset.univ.centroid ℝ orb := by
        rw [Finset.map_univ_equiv]
