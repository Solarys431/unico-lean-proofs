import Mathlib

/-!
A13 — IL PONTE DELL'ESPOSIZIONE (campagna #50, assemblaggio).

Due fatti di teoria delle facce che servono al lato-faccetta del teorema:

* `esposto_ristretto` — un insieme esposto nel corpo P, contenuto in una
  faccia F, è esposto ANCHE in F (stesso funzionale: il massimo locale
  coincide col globale perché l'insieme non è vuoto);
* con `IsExposed.inter` (mathlib) questo rende lo spigolo del fan
  Fᵢ ∩ Fᵢ₊₁ una faccia esposta della faccetta: l'ingresso di G1.
-/

open scoped RealInnerProductSpace

namespace PlatoniciA13

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- Un esposto del corpo contenuto in una faccia è esposto nella faccia. -/
theorem esposto_ristretto {S B F : Set A} (hB : IsExposed ℝ S B)
    (hBF : B ⊆ F) (hFS : F ⊆ S) : IsExposed ℝ F B := by
  intro hBne
  obtain ⟨l, hl⟩ := hB hBne
  refine ⟨l, ?_⟩
  ext x
  constructor
  · intro hx
    rw [hl] at hx
    exact ⟨hBF (by rw [hl]; exact hx), fun y hy => hx.2 y (hFS hy)⟩
  · rintro ⟨hxF, hxmax⟩
    obtain ⟨b, hb⟩ := hBne
    have hbF : b ∈ F := hBF hb
    rw [hl] at hb
    rw [hl]
    refine ⟨hFS hxF, fun y hy => ?_⟩
    calc l y ≤ l b := hb.2 y hy
      _ ≤ l x := hxmax b hbF

/-- Lo spigolo del fan è esposto nella faccetta (per G1). -/
theorem spigolo_esposto_nella_faccetta {S F G : Set A}
    (hF : IsExposed ℝ S F) (hG : IsExposed ℝ S G) :
    IsExposed ℝ F (F ∩ G) := by
  have hinter : IsExposed ℝ S (F ∩ G) := hF.inter hG
  exact esposto_ristretto hinter Set.inter_subset_left hF.subset

end PlatoniciA13
