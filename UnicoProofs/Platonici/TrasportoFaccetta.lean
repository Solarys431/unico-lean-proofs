import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.Fondamenta
import UnicoProofs.Platonici.VerticiEsposti
import UnicoProofs.Platonici.SottoPolitopo
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.Interpolazione
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.Immagini
import UnicoProofs.Platonici.FanVertice
import UnicoProofs.Platonici.PassoFan

/-!
FASE 3A, F7 — IL TRASPORTO DELLA FACCETTA REGOLARE (18 lug 2026).

(1) Ogni faccetta ospita una bandiera (il gemello di `bandiera_al_vertice`
con la faccetta prescritta). (2) Una simmetria trasporta `IsRegularFacet`
con GLI STESSI p ed ℓ: la rotazione del poligono passa per coniugio, l'orbita
per immagine (il coniugio-iterato è l'immagine dell'iterato), l'hull per
`AffineMap.image_convexHull`, la distanza per l'isometria. Con questi due
attrezzi l'uniformità di p e ℓ sulle faccette di un politopo regolare è un
trasporto dal riferimento, senza alcun teorema di unicità.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Ogni faccetta ospita una bandiera. -/
theorem bandiera_con_faccetta (P : ConvexPolytope 3)
    {A : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2) :
    ∃ F : P.Flag, F.face 2 = A := by
  classical
  -- un vertice della faccetta
  obtain ⟨x₀, hx₀Q⟩ := (facePolytope P hA).vertices_nonempty
  have hx₀V : x₀ ∈ P.vertices := by
    have h1 : x₀ ∈ P.vertices.filter (· ∈ A) := hx₀Q
    exact (Finset.mem_filter.mp h1).1
  have hx₀A : x₀ ∈ A := by
    have h1 : x₀ ∈ P.vertices.filter (· ∈ A) := hx₀Q
    exact (Finset.mem_filter.mp h1).2
  -- uno spigolo della faccetta per x₀
  have hQdim : Module.finrank ℝ
      (vectorSpan ℝ (facePolytope P hA).toSet) = 2 := by
    rw [facePolytope_toSet P hA]
    exact hdA
  have hx₀face : (facePolytope P hA).IsFace ({x₀} : Set (E 3)) :=
    vertex_isFace (facePolytope P hA) hx₀Q
  have hgap : faceDim ({x₀} : Set (E 3)) + 2 ≤
      Module.finrank ℝ (vectorSpan ℝ (facePolytope P hA).toSet) := by
    rw [faceDim_singleton, hQdim]
  obtain ⟨e, he, hxe, hene⟩ :=
    interpolazione (facePolytope P hA) hx₀face hgap
  have hde : faceDim e = 1 := by
    have h1 := faceDim_lt_of_ssubset (facePolytope P hA) hx₀face he hxe
    rw [faceDim_singleton] at h1
    have hss : e ⊂ (facePolytope P hA).toSet :=
      ⟨face_subset_toSet (facePolytope P hA) he, fun hsup => hene
        (Set.Subset.antisymm
          (face_subset_toSet (facePolytope P hA) he) hsup)⟩
    have h2 := faceDim_lt_of_ssubset (facePolytope P hA) he
      (toSet_isFace (facePolytope P hA)) hss
    have h3 : faceDim (facePolytope P hA).toSet = 2 := hQdim
    omega
  have heP : P.IsFace e := isFace_of_facePolytope P hA he
  have heA : e ⊆ A := by
    have h1 := face_subset_toSet (facePolytope P hA) he
    rwa [facePolytope_toSet P hA] at h1
  obtain ⟨F, _, _, hF2⟩ := bandiera_di_pezzi P (vertex_isFace P hx₀V)
    heP hde (hxe.subset rfl) hA hdA heA
  exact ⟨F, hF2⟩

/-- Il coniugio itera come l'immagine dell'iterato. -/
theorem coniugio_iterato (τ ρ : Isom 3) (x : E 3) :
    ∀ k : ℕ, (⇑((τ.symm.trans ρ).trans τ))^[k] (τ x) = τ ((⇑ρ)^[k] x) := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      show τ (ρ (τ.symm (τ ((⇑ρ)^[n] x)))) = _
      rw [τ.symm_apply_apply]

/-- **IL TRASPORTO DELLA FACCETTA REGOLARE**: una simmetria trasporta
`IsRegularFacet` con gli stessi p ed ℓ. -/
theorem isRegularFacet_trasporto (P : ConvexPolytope 3)
    {τ : Isom 3} (hτ : P.isSymmetry τ)
    {A : Set (E 3)} {p : ℕ} {ℓ : ℝ}
    (h : P.asFinite.IsRegularFacet A p ℓ) :
    P.asFinite.IsRegularFacet ((⇑τ) '' A) p ℓ := by
  classical
  obtain ⟨hFacet, hℓ, hp, ρ, x₀, hx₀A, hρA, hinj, hcl, hhull, hdist⟩ := h
  refine ⟨?_, hℓ, hp, (τ.symm.trans ρ).trans τ, τ x₀, ⟨x₀, hx₀A, rfl⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- la faccetta immagine
    rw [P.asFinite_isFacet_iff] at hFacet ⊢
    exact ⟨isFace_image_isom τ hτ hFacet.1, by
      rw [faceDim_image_isom]
      exact hFacet.2⟩
  · -- la rotazione coniugata fissa l'immagine
    have h1 : (⇑((τ.symm.trans ρ).trans τ) : E 3 → E 3) =
        (⇑τ) ∘ (⇑ρ) ∘ (⇑τ.symm) := by
      funext z
      rfl
    rw [h1, Set.image_comp, Set.image_comp]
    have h2 : (⇑τ.symm) '' ((⇑τ) '' A) = A := by
      rw [← Set.image_comp]
      have h3 : (⇑τ.symm) ∘ (⇑τ) = id := by
        funext z
        simp
      rw [h3, Set.image_id]
    rw [h2, hρA]
  · -- iniettività dell'orbita coniugata
    intro i j hij
    apply hinj
    have h1 := coniugio_iterato τ ρ x₀ (i : ℕ)
    have h2 := coniugio_iterato τ ρ x₀ (j : ℕ)
    have h3 : τ ((⇑ρ)^[(i : ℕ)] x₀) = τ ((⇑ρ)^[(j : ℕ)] x₀) := by
      rw [← h1, ← h2]
      exact hij
    exact τ.injective h3
  · -- chiusura a p passi
    rw [coniugio_iterato τ ρ x₀ p, hcl]
  · -- l'hull dell'orbita immagine
    have h1 : (Set.range fun i : Fin p =>
        (⇑((τ.symm.trans ρ).trans τ))^[(i : ℕ)] (τ x₀)) =
        (⇑τ) '' (Set.range fun i : Fin p => (⇑ρ)^[(i : ℕ)] x₀) := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨(⇑ρ)^[(i : ℕ)] x₀, ⟨i, rfl⟩, (coniugio_iterato τ ρ x₀ _).symm ▸ rfl⟩
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, coniugio_iterato τ ρ x₀ _⟩
    rw [h1, hhull]
    -- l'immagine affine dell'hull è l'hull dell'immagine
    have h2 := (τ.toAffineEquiv.toAffineMap).image_convexHull
      (Set.range fun i : Fin p => (⇑ρ)^[(i : ℕ)] x₀)
    have hco : (⇑τ.toAffineEquiv.toAffineMap : E 3 → E 3) = ⇑τ := by
      funext z
      simp
    rw [hco] at h2
    exact h2
  · -- la distanza si conserva
    have h1 : (⇑((τ.symm.trans ρ).trans τ)) (τ x₀) = τ (ρ x₀) := by
      have := coniugio_iterato τ ρ x₀ 1
      simpa using this
    rw [h1]
    rw [τ.dist_map]
    exact hdist

end LeanEval.Geometry.PlatonicClassification
