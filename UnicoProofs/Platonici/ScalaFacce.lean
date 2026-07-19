import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FanVertice
import UnicoProofs.Platonici.Scala

/-!
RIGIDITÀ — LE FACCE DEL POLITOPO SCALATO (19 lug 2026).

Il corredo di trasporto per l'omotetia positiva, gemello-scaling di
`isExposed_image_isom`/`faceDim_image_isom`: per l'omotetia il funzionale
espositore si ricompone con (a⁻¹ • ·) SENZA offset di traslazione, e le
facce, le faccette e i rank si trasportano nei due versi fra P e
`scala a ha P` al livello del mondo finito.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- Andata e ritorno dell'omotetia sulle immagini. -/
theorem smul_image_roundtrip (a : ℝ) (ha : a ≠ 0) (G : Set (E 3)) :
    (fun x : E 3 => a • x) '' ((fun x : E 3 => a⁻¹ • x) '' G) = G := by
  rw [Set.image_image]
  have h1 : (fun x : E 3 => a • a⁻¹ • x) = fun x : E 3 => x := by
    funext x
    rw [smul_smul, mul_inv_cancel₀ ha, one_smul]
  rw [h1, Set.image_id']

/-- Ritorno e andata. -/
theorem inv_smul_image_roundtrip (a : ℝ) (ha : a ≠ 0) (G : Set (E 3)) :
    (fun x : E 3 => a⁻¹ • x) '' ((fun x : E 3 => a • x) '' G) = G := by
  rw [Set.image_image]
  have h1 : (fun x : E 3 => a⁻¹ • a • x) = fun x : E 3 => x := by
    funext x
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [h1, Set.image_id']

/-- L'esposizione si trasporta lungo l'omotetia: il funzionale si
ricompone con l'omotetia inversa. -/
theorem isExposed_image_smul {a : ℝ} (ha : a ≠ 0) {T B : Set (E 3)}
    (h : IsExposed ℝ T B) :
    IsExposed ℝ ((fun x : E 3 => a • x) '' T)
      ((fun x : E 3 => a • x) '' B) := by
  intro hne
  obtain ⟨b0, hb0⟩ := hne
  obtain ⟨b1, hb1B, _⟩ := hb0
  obtain ⟨l, hl⟩ := h ⟨b1, hb1B⟩
  let l' : E 3 →L[ℝ] ℝ :=
    l.comp (a⁻¹ • ContinuousLinearMap.id ℝ (E 3))
  have hl' : ∀ x : E 3, l' (a • x) = l x := by
    intro x
    have h1 : (a⁻¹ • ContinuousLinearMap.id ℝ (E 3)) (a • x) = x := by
      show a⁻¹ • a • x = x
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    show l ((a⁻¹ • ContinuousLinearMap.id ℝ (E 3)) (a • x)) = l x
    rw [h1]
  refine ⟨l', Set.ext ?_⟩
  intro x
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [hl] at hb
    refine ⟨⟨b, hb.1, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [hl' y, hl' b]
    exact hb.2 y hy
  · rintro ⟨hxA, hxmax⟩
    obtain ⟨c, hc, rfl⟩ := hxA
    refine ⟨c, ?_, rfl⟩
    rw [hl]
    refine ⟨hc, ?_⟩
    intro y hy
    have hle := hxmax (a • y) ⟨y, hy, rfl⟩
    rw [hl' y, hl' c] at hle
    exact hle

/-- Il rank direzionale è invariante sotto omotetia. -/
theorem finrank_vectorSpan_smul (a : ℝ) (ha : a ≠ 0) (F : Set (E 3)) :
    Module.finrank ℝ (vectorSpan ℝ ((fun x : E 3 => a • x) '' F)) =
      Module.finrank ℝ (vectorSpan ℝ F) := by
  have hmap := (omotetia a ha (n := 3)).toAffineMap.map_vectorSpan (s := F)
  have hco : (⇑(omotetia a ha (n := 3)).toAffineMap : E 3 → E 3) =
      fun x : E 3 => a • x := rfl
  rw [hco] at hmap
  change Submodule.map
    ((omotetia a ha (n := 3)).linear : E 3 →ₗ[ℝ] E 3)
    (vectorSpan ℝ F) = vectorSpan ℝ ((fun x : E 3 => a • x) '' F) at hmap
  rw [← hmap]
  exact (omotetia a ha (n := 3)).linear.finrank_map_eq (vectorSpan ℝ F)

/-- Il corpo del politopo scalato, al livello finito. -/
theorem toSet_scala_finite (a : ℝ) (ha : a ≠ 0) (P : ConvexPolytope 3) :
    (scala a ha P).asFinite.toSet =
      (fun x : E 3 => a • x) '' P.asFinite.toSet := by
  show (scala a ha P).toSet = (fun x : E 3 => a • x) '' P.toSet
  exact scala_toSet a ha P

/-- Le facce si trasportano sul politopo scalato. -/
theorem isFace_scala {P : ConvexPolytope 3} {a : ℝ} (ha : a ≠ 0)
    {F : Set (E 3)} (hF : P.asFinite.IsFace F) :
    (scala a ha P).asFinite.IsFace ((fun x : E 3 => a • x) '' F) := by
  refine ⟨?_, hF.2.image _⟩
  rw [toSet_scala_finite a ha P]
  exact isExposed_image_smul ha hF.1

/-- Le facce del politopo scalato vengono da facce di P. -/
theorem isFace_of_scala {P : ConvexPolytope 3} {a : ℝ} (ha : a ≠ 0)
    {G : Set (E 3)} (hG : (scala a ha P).asFinite.IsFace G) :
    P.asFinite.IsFace ((fun x : E 3 => a⁻¹ • x) '' G) ∧
      G = (fun x : E 3 => a • x) '' ((fun x : E 3 => a⁻¹ • x) '' G) := by
  refine ⟨⟨?_, hG.2.image _⟩, (smul_image_roundtrip a ha G).symm⟩
  have h1 : P.asFinite.toSet =
      (fun x : E 3 => a⁻¹ • x) '' ((scala a ha P).asFinite.toSet) := by
    rw [toSet_scala_finite a ha P, inv_smul_image_roundtrip a ha]
  rw [h1]
  exact isExposed_image_smul (inv_ne_zero ha) hG.1

/-- Le faccette si trasportano sul politopo scalato. -/
theorem isFacet_scala {P : ConvexPolytope 3} {a : ℝ} (ha : a ≠ 0)
    {F : Set (E 3)} (hF : P.asFinite.IsFacet F) :
    (scala a ha P).asFinite.IsFacet ((fun x : E 3 => a • x) '' F) := by
  refine ⟨isFace_scala ha hF.1, ?_⟩
  rw [finrank_vectorSpan_smul a ha]
  exact hF.2

/-- Le faccette del politopo scalato vengono da faccette di P. -/
theorem isFacet_of_scala {P : ConvexPolytope 3} {a : ℝ} (ha : a ≠ 0)
    {G : Set (E 3)} (hG : (scala a ha P).asFinite.IsFacet G) :
    P.asFinite.IsFacet ((fun x : E 3 => a⁻¹ • x) '' G) ∧
      G = (fun x : E 3 => a • x) '' ((fun x : E 3 => a⁻¹ • x) '' G) := by
  obtain ⟨hface, hround⟩ := isFace_of_scala ha hG.1
  refine ⟨⟨hface, ?_⟩, hround⟩
  have h2 : Module.finrank ℝ (vectorSpan ℝ G) = 2 := hG.2
  rw [hround] at h2
  rw [finrank_vectorSpan_smul a ha] at h2
  exact h2

/-- La distanza scala del fattore positivo. -/
theorem dist_smul_pos {a : ℝ} (ha : 0 < a) (x y : E 3) :
    dist (a • x) (a • y) = a * dist x y := by
  rw [dist_smul₀]
  rw [Real.norm_of_nonneg (le_of_lt ha)]

end LeanEval.Geometry.PlatonicClassification
