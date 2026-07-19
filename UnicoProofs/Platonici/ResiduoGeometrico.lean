import Mathlib
import UnicoProofs.Platonici.LibertaGenerica
import UnicoProofs.Platonici.RotazioneElementare

open Set
open scoped RealInnerProductSpace

noncomputable section

-- Alcune ipotesi sono mantenute per compatibilità con le firme del ponte.
set_option linter.unusedVariables false

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Il centroide dei vertici del politopo è fissato da ogni sua simmetria. -/
theorem centro_fisso (P : ConvexPolytope n) (hreg : P.IsRegular)
    {φ : Isom n} (hφ : P.isSymmetry φ) :
    φ (Finset.centroid ℝ P.vertices id) = Finset.centroid ℝ P.vertices id := by
  classical
  have hfilter : P.vertices.filter (fun x => x ∈ P.toSet) = P.vertices := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    exact subset_convexHull ℝ _ (by exact_mod_cast hx)
  simpa only [hfilter] using
    (centroide_di_faccia_fissato P hφ (toSet_isFace P) hφ)

/-- Se le due riflessioni fissano `O`, fissano anche `O + y` quando `y`
è ortogonale a entrambi i normali. -/
theorem parte_lineare_preserva (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    {αi pi αj pj : E n} (hαi : ‖αi‖ = 1) (hαj : ‖αj‖ = 1)
    (hri : ∀ x, simpleReflection P hreg F i x =
      x - (2 * ⟪αi, x - pi⟫ : ℝ) • αi)
    (hrj : ∀ x, simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ x =
      x - (2 * ⟪αj, x - pj⟫ : ℝ) • αj)
    (y : E n) (hy : ⟪αi, y⟫ = 0) (hz : ⟪αj, y⟫ = 0) (O : E n)
    (hOi : simpleReflection P hreg F i O = O)
    (hOj : simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ O = O) :
    simpleReflection P hreg F i (O + y) = O + y ∧
      simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ (O + y) = O + y := by
  have hOi' := hOi
  rw [hri O] at hOi'
  have hzi : (2 * ⟪αi, O - pi⟫ : ℝ) • αi = 0 := sub_eq_self.mp hOi'
  have hOj' := hOj
  rw [hrj O] at hOj'
  have hzj : (2 * ⟪αj, O - pj⟫ : ℝ) • αj = 0 := sub_eq_self.mp hOj'
  constructor
  · rw [hri (O + y)]
    rw [show O + y - pi = (O - pi) + y by abel, inner_add_right,
      hy, add_zero, hzi, sub_zero]
  · rw [hrj (O + y)]
    rw [show O + y - pj = (O - pj) + y by abel, inner_add_right,
      hz, add_zero, hzj, sub_zero]

/-- Il fissaggio di un punto sopravvive alla proiezione sul piano dei
due normali, effettuata rispetto a un centro fisso. -/
theorem proiettato_fissato (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    {αi pi αj pj : E n} (hαi : ‖αi‖ = 1) (hαj : ‖αj‖ = 1)
    (hri : ∀ x, simpleReflection P hreg F i x =
      x - (2 * ⟪αi, x - pi⟫ : ℝ) • αi)
    (hrj : ∀ x, simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ x =
      x - (2 * ⟪αj, x - pj⟫ : ℝ) • αj)
    (V : Submodule ℝ (E n)) (hVspan : V = Submodule.span ℝ {αi, αj})
    (O c : E n) (hOfix : simpleReflection P hreg F i O = O)
    (hcfix : simpleReflection P hreg F i c = c) :
    simpleReflection P hreg F i
        (O + (V.orthogonalProjection (c - O) : E n)) =
      O + (V.orthogonalProjection (c - O) : E n) := by
  have hαne : αi ≠ 0 := by
    intro h
    rw [h, norm_zero] at hαi
    norm_num at hαi
  have hαV : αi ∈ V := by
    rw [hVspan]
    exact Submodule.subset_span (by simp)
  have hproj :
      ⟪αi, (V.orthogonalProjection (c - O) : E n)⟫ = ⟪αi, c - O⟫ := by
    have ho := Submodule.inner_right_of_mem_orthogonal hαV
      (V.sub_starProjection_mem_orthogonal (c - O))
    rw [inner_sub_right, sub_eq_zero] at ho
    exact ho.symm
  have hinner_of_fix : ∀ {x : E n},
      simpleReflection P hreg F i x = x → ⟪αi, x - pi⟫ = 0 := by
    intro x hx
    rw [hri x] at hx
    have hs : (2 * ⟪αi, x - pi⟫ : ℝ) • αi = 0 := sub_eq_self.mp hx
    have : (2 * ⟪αi, x - pi⟫ : ℝ) = 0 :=
      (smul_eq_zero.mp hs).resolve_right hαne
    linarith
  have hOinner := hinner_of_fix hOfix
  have hcinner := hinner_of_fix hcfix
  have hcOinner : ⟪αi, c - O⟫ = 0 := by
    rw [show c - pi = (O - pi) + (c - O) by abel, inner_add_right,
      hOinner, zero_add] at hcinner
    exact hcinner
  rw [hri]
  rw [show O + (V.orthogonalProjection (c - O) : E n) - pi =
      (O - pi) + (V.orthogonalProjection (c - O) : E n) by abel,
    inner_add_right, hOinner, zero_add, hproj, hcOinner, mul_zero,
    zero_smul, sub_zero]

/-- Il non fissaggio di un punto sopravvive alla proiezione sul piano dei
due normali, effettuata rispetto a un centro fisso. -/
theorem proiettato_non_fissato (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    {αi pi αj pj : E n} (hαi : ‖αi‖ = 1) (hαj : ‖αj‖ = 1)
    (hri : ∀ x, simpleReflection P hreg F i x =
      x - (2 * ⟪αi, x - pi⟫ : ℝ) • αi)
    (hrj : ∀ x, simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ x =
      x - (2 * ⟪αj, x - pj⟫ : ℝ) • αj)
    (V : Submodule ℝ (E n)) (hVspan : V = Submodule.span ℝ {αi, αj})
    (O c : E n) (hOfix : simpleReflection P hreg F i O = O)
    (hcne : simpleReflection P hreg F i c ≠ c) :
    simpleReflection P hreg F i
        (O + (V.orthogonalProjection (c - O) : E n)) ≠
      O + (V.orthogonalProjection (c - O) : E n) := by
  have hαne : αi ≠ 0 := by
    intro h
    rw [h, norm_zero] at hαi
    norm_num at hαi
  have hαV : αi ∈ V := by
    rw [hVspan]
    exact Submodule.subset_span (by simp)
  have hproj :
      ⟪αi, (V.orthogonalProjection (c - O) : E n)⟫ = ⟪αi, c - O⟫ := by
    have ho := Submodule.inner_right_of_mem_orthogonal hαV
      (V.sub_starProjection_mem_orthogonal (c - O))
    rw [inner_sub_right, sub_eq_zero] at ho
    exact ho.symm
  have hOinner : ⟪αi, O - pi⟫ = 0 := by
    have hOfix' := hOfix
    rw [hri O] at hOfix'
    have hs : (2 * ⟪αi, O - pi⟫ : ℝ) • αi = 0 := sub_eq_self.mp hOfix'
    have : (2 * ⟪αi, O - pi⟫ : ℝ) = 0 :=
      (smul_eq_zero.mp hs).resolve_right hαne
    linarith
  have hcinner_ne : ⟪αi, c - pi⟫ ≠ 0 := by
    intro hcinner
    apply hcne
    rw [hri c, hcinner, mul_zero, zero_smul, sub_zero]
  have hprojected_inner :
      ⟪αi, O + (V.orthogonalProjection (c - O) : E n) - pi⟫ =
        ⟪αi, c - pi⟫ := by
    rw [show O + (V.orthogonalProjection (c - O) : E n) - pi =
        (O - pi) + (V.orthogonalProjection (c - O) : E n) by abel,
      inner_add_right, hOinner, zero_add, hproj]
    rw [show c - pi = (O - pi) + (c - O) by abel, inner_add_right,
      hOinner, zero_add]
  intro hfix
  rw [hri] at hfix
  have hs :
      (2 * ⟪αi, O + (V.orthogonalProjection (c - O) : E n) - pi⟫ : ℝ) • αi = 0 :=
    sub_eq_self.mp hfix
  have hscalar :
      (2 * ⟪αi, O + (V.orthogonalProjection (c - O) : E n) - pi⟫ : ℝ) = 0 :=
    (smul_eq_zero.mp hs).resolve_right hαne
  apply hcinner_ne
  rw [← hprojected_inner]
  linarith

/-- I due normali e i due vettori proiettati appartengono al piano `V`. -/
theorem proiettati_in_V {αi αj : E n} (V : Submodule ℝ (E n))
    (hVspan : V = Submodule.span ℝ {αi, αj}) (O c₁ cnext : E n) :
    αi ∈ V ∧ αj ∈ V ∧
      O + (V.orthogonalProjection (c₁ - O) : E n) - O ∈ V ∧
      O + (V.orthogonalProjection (cnext - O) : E n) - O ∈ V := by
  constructor
  · rw [hVspan]
    exact Submodule.subset_span (by simp)
  constructor
  · rw [hVspan]
    exact Submodule.subset_span (by simp)
  constructor
  · simpa only [add_sub_cancel_left] using
      (V.orthogonalProjection (c₁ - O)).property
  · simpa only [add_sub_cancel_left] using
      (V.orthogonalProjection (cnext - O)).property

/-- Due vettori non paralleli, il primo dei quali è unitario, generano un
sottospazio di finrank due. -/
theorem finrank_span_normali {αi αj : E n} (hαi : ‖αi‖ = 1)
    (hind : ∀ t : ℝ, αj ≠ t • αi) :
    Module.finrank ℝ (Submodule.span ℝ ({αi, αj} : Set (E n))) = 2 := by
  have hαne : αi ≠ 0 := by
    intro h
    rw [h, norm_zero] at hαi
    norm_num at hαi
  have hLI : LinearIndependent ℝ ![αi, αj] :=
    (LinearIndependent.pair_iff' hαne).2 fun t => (hind t).symm
  have hrange : Set.range ![αi, αj] = {αi, αj} := by
    ext x
    simp [or_comm]
  rw [← hrange]
  exact finrank_span_eq_card hLI

end LeanEval.Geometry.PlatonicClassification
