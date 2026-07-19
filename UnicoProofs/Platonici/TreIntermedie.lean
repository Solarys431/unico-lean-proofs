import Mathlib
import UnicoProofs.Platonici.BandieraVertice
import UnicoProofs.Platonici.SecondoIntermedio

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

theorem tre_vertici_di_poligono (P : ConvexPolytope n)
    (hdim : faceDim P.toSet = 2) :
    ∃ u v w : Set (E n),
      (P.IsFace u ∧ faceDim u = 0) ∧ (P.IsFace v ∧ faceDim v = 0) ∧
      (P.IsFace w ∧ faceDim w = 0) ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w := by
  classical
  have hdim_vertices :
      Module.finrank ℝ (vectorSpan ℝ (P.vertices : Set (E n))) = 2 := by
    have hspan : vectorSpan ℝ P.toSet =
        vectorSpan ℝ (P.vertices : Set (E n)) := by
      rw [← direction_affineSpan, ← direction_affineSpan]
      exact congrArg AffineSubspace.direction
        (affineSpan_convexHull (P.vertices : Set (E n)))
    rw [← hspan]
    exact hdim
  let vertexPoint : {x // x ∈ (P.vertices : Set (E n))} → E n :=
    fun x => x.1
  letI : Nonempty {x // x ∈ (P.vertices : Set (E n))} := by
    obtain ⟨x, hx⟩ := P.vertices_nonempty
    exact ⟨⟨x, by exact_mod_cast hx⟩⟩
  have hrange : Set.range vertexPoint = (P.vertices : Set (E n)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hcard_bound := finrank_vectorSpan_range_add_one_le ℝ vertexPoint
  rw [hrange, hdim_vertices] at hcard_bound
  have hcard_eq : Fintype.card {x // x ∈ (P.vertices : Set (E n))} =
      P.vertices.card := by
    simp
  have hthree : 2 < P.vertices.card := by
    rw [hcard_eq] at hcard_bound
    omega
  obtain ⟨u, hu, v, hv, w, hw, huv, huw, hvw⟩ :=
    Finset.two_lt_card.mp hthree
  refine ⟨{u}, {v}, {w},
    ⟨vertex_isFace P hu, faceDim_singleton u⟩,
    ⟨vertex_isFace P hv, faceDim_singleton v⟩,
    ⟨vertex_isFace P hw, faceDim_singleton w⟩, ?_, ?_, ?_⟩
  · simpa using huv
  · simpa using huw
  · simpa using hvw

theorem tre_intermedie_di_rango_tre (P : ConvexPolytope n)
    {A B : Set (E n)} (hA : P.IsFace A) (hB : P.IsFace B)
    (hAB : A ⊂ B) (hrank : faceDim B = faceDim A + 3) :
    ∃ C₁ C₂ C₃ : Set (E n),
      (P.IsFace C₁ ∧ A ⊂ C₁ ∧ C₁ ⊂ B ∧ faceDim C₁ = faceDim A + 1) ∧
      (P.IsFace C₂ ∧ A ⊂ C₂ ∧ C₂ ⊂ B ∧ faceDim C₂ = faceDim A + 1) ∧
      (P.IsFace C₃ ∧ A ⊂ C₃ ∧ C₃ ⊂ B ∧ faceDim C₃ = faceDim A + 1) ∧
      C₁ ≠ C₂ ∧ C₁ ≠ C₃ ∧ C₂ ≠ C₃ := by
  classical
  let Q := facePolytope P hB
  have hAQ : Q.IsFace A :=
    facePolytope_isFace_of P hB hA hAB.1
  have hgapQ : faceDim A + 2 ≤
      Module.finrank ℝ (vectorSpan ℝ Q.toSet) := by
    change faceDim A + 2 ≤
      Module.finrank ℝ (vectorSpan ℝ (facePolytope P hB).toSet)
    rw [facePolytope_toSet P hB]
    change faceDim A + 2 ≤ faceDim B
    omega
  obtain ⟨F, hFQ, hAF, hFneQ⟩ := interpolazione Q hAQ hgapQ
  have hFP : P.IsFace F := isFace_of_facePolytope P hB hFQ
  have hFsubB : F ⊆ B := by
    have hsub := face_subset_toSet Q hFQ
    change F ⊆ (facePolytope P hB).toSet at hsub
    rwa [facePolytope_toSet P hB] at hsub
  have hFneB : F ≠ B := by
    intro hFB
    apply hFneQ
    change F = (facePolytope P hB).toSet
    rw [facePolytope_toSet P hB]
    exact hFB
  have hFB : F ⊂ B := by
    refine ⟨hFsubB, ?_⟩
    intro hBF
    exact hFneB (Set.Subset.antisymm hFsubB hBF)
  have hdimF_lo := faceDim_lt_of_ssubset P hA hFP hAF
  have hdimF_hi := faceDim_lt_of_ssubset P hFP hB hFB
  have hchain : ∃ C₁ D : Set (E n),
      P.IsFace C₁ ∧ P.IsFace D ∧ A ⊂ C₁ ∧ C₁ ⊂ D ∧ D ⊂ B ∧
      faceDim C₁ = faceDim A + 1 ∧ faceDim D = faceDim A + 2 := by
    by_cases hdimF : faceDim F = faceDim A + 1
    · have hrankFB : faceDim B = faceDim F + 2 := by omega
      obtain ⟨D, hD, hFD, hDB, hdimD⟩ :=
        faccia_intermedia P hFP hB hFB hrankFB
      refine ⟨F, D, hFP, hD, hAF, hFD, hDB, hdimF, ?_⟩
      omega
    · have hdimF' : faceDim F = faceDim A + 2 := by omega
      have hrankAF : faceDim F = faceDim A + 2 := hdimF'
      obtain ⟨C₁, hC₁, hAC₁, hC₁F, hdimC₁⟩ :=
        faccia_intermedia P hA hFP hAF hrankAF
      exact ⟨C₁, F, hC₁, hFP, hAC₁, hC₁F, hFB, hdimC₁, hdimF'⟩
  obtain ⟨C₁, D, hC₁, hD, hAC₁, hC₁D, hDB, hdimC₁, hdimD⟩ := hchain
  have hrankAD : faceDim D = faceDim A + 2 := hdimD
  obtain ⟨C₂, hC₂, hAC₂, hC₂D, hC₂neC₁⟩ :=
    secondo_intermedio P hA hD hrankAD hC₁ hAC₁ hC₁D
  have hdimC₂_lo := faceDim_lt_of_ssubset P hA hC₂ hAC₂
  have hdimC₂_hi := faceDim_lt_of_ssubset P hC₂ hD hC₂D
  have hdimC₂ : faceDim C₂ = faceDim A + 1 := by omega
  have hrankC₁B : faceDim B = faceDim C₁ + 2 := by omega
  obtain ⟨D₂, hD₂, hC₁D₂, hD₂B, hD₂neD⟩ :=
    secondo_intermedio P hC₁ hB hrankC₁B hD hC₁D hDB
  have hdimD₂_lo := faceDim_lt_of_ssubset P hC₁ hD₂ hC₁D₂
  have hdimD₂_hi := faceDim_lt_of_ssubset P hD₂ hB hD₂B
  have hdimD₂ : faceDim D₂ = faceDim A + 2 := by omega
  have hrankAD₂ : faceDim D₂ = faceDim A + 2 := hdimD₂
  obtain ⟨C₃, hC₃, hAC₃, hC₃D₂, hC₃neC₁⟩ :=
    secondo_intermedio P hA hD₂ hrankAD₂ hC₁ hAC₁ hC₁D₂
  have hdimC₃_lo := faceDim_lt_of_ssubset P hA hC₃ hAC₃
  have hdimC₃_hi := faceDim_lt_of_ssubset P hC₃ hD₂ hC₃D₂
  have hdimC₃ : faceDim C₃ = faceDim A + 1 := by omega
  have hC₂neC₃ : C₂ ≠ C₃ := by
    intro hC₂C₃
    obtain ⟨a, haA⟩ := hA.2
    have hI : P.IsFace (D ∩ D₂) := by
      refine ⟨hD.1.inter hD₂.1, ?_⟩
      exact ⟨a, hC₁D.1 (hAC₁.1 haA), hC₁D₂.1 (hAC₁.1 haA)⟩
    have hID : D ∩ D₂ ⊂ D := by
      refine ⟨Set.inter_subset_left, ?_⟩
      intro hDsubI
      have hDsubD₂ : D ⊆ D₂ := fun x hx => (hDsubI hx).2
      have hDD₂ : D ⊂ D₂ := by
        refine ⟨hDsubD₂, ?_⟩
        intro hD₂subD
        exact hD₂neD (Set.Subset.antisymm hD₂subD hDsubD₂)
      have hlt := faceDim_lt_of_ssubset P hD hD₂ hDD₂
      omega
    have hC₁I : C₁ ⊆ D ∩ D₂ := fun x hx =>
      ⟨hC₁D.1 hx, hC₁D₂.1 hx⟩
    have hIeqC₁ : D ∩ D₂ = C₁ := by
      apply Set.Subset.antisymm
      · by_contra hnot
        have hC₁strict : C₁ ⊂ D ∩ D₂ := ⟨hC₁I, hnot⟩
        have hlo := faceDim_lt_of_ssubset P hC₁ hI hC₁strict
        have hhi := faceDim_lt_of_ssubset P hI hD hID
        omega
      · exact hC₁I
    have hC₂D₂ : C₂ ⊆ D₂ := by
      rw [hC₂C₃]
      exact hC₃D₂.1
    have hC₂C₁ : C₂ ⊆ C₁ := by
      intro x hx
      have hxI : x ∈ D ∩ D₂ := ⟨hC₂D.1 hx, hC₂D₂ hx⟩
      rwa [hIeqC₁] at hxI
    have hC₂strict : C₂ ⊂ C₁ := by
      refine ⟨hC₂C₁, ?_⟩
      intro hC₁C₂
      exact hC₂neC₁ (Set.Subset.antisymm hC₂C₁ hC₁C₂)
    have hlt := faceDim_lt_of_ssubset P hC₂ hC₁ hC₂strict
    omega
  have hC₁B : C₁ ⊂ B := hC₁D.trans hDB
  have hC₂B : C₂ ⊂ B := hC₂D.trans hDB
  have hC₃B : C₃ ⊂ B := hC₃D₂.trans hD₂B
  exact ⟨C₁, C₂, C₃,
    ⟨hC₁, hAC₁, hC₁B, hdimC₁⟩,
    ⟨hC₂, hAC₂, hC₂B, hdimC₂⟩,
    ⟨hC₃, hAC₃, hC₃B, hdimC₃⟩,
    hC₂neC₁.symm, hC₃neC₁.symm, hC₂neC₃⟩

end LeanEval.Geometry.PlatonicClassification
