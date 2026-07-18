import UnicoProofs.Platonici.Fondamenta

/-!
FASE 1B — TRASFERIMENTO PER ISOMETRIE (18 lug 2026).

Il pezzo condiviso da cubo e dodecaedro: una faccetta regolare trasportata da
un'isometria affine che preserva il politopo resta una faccetta regolare.
Con questo, basta UNA faccetta per solido: le altre seguono per simmetria.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace FiniteConvexPolytope

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- Il fatto puntuale: un'isometria affine deforma un funzionale lineare in un
funzionale lineare più una costante. -/
theorem funzionale_coniugato (g : A ≃ᵃⁱ[ℝ] A) (l : A →L[ℝ] ℝ) :
    ∃ (l' : A →L[ℝ] ℝ) (c : ℝ), ∀ x : A, l (g.symm x) = l' x + c := by
  refine ⟨l.comp (g.symm.toAffineIsometry.linearIsometry.toContinuousLinearMap),
    l (g.symm 0), ?_⟩
  intro x
  have hdec : g.symm x = g.symm.toAffineIsometry.linearIsometry x + g.symm 0 := by
    have hd := (g.symm.toAffineIsometry.toAffineMap).decomp
    have hx := congrFun hd x
    simpa using hx
  rw [hdec, map_add]
  rfl

/-- L'esposizione si trasporta lungo un'isometria affine. -/
theorem isExposed_image (g : A ≃ᵃⁱ[ℝ] A) {s F : Set A}
    (hF : IsExposed ℝ s F) : IsExposed ℝ ((⇑g) '' s) ((⇑g) '' F) := by
  intro hne
  obtain ⟨l, hl⟩ := hF (hne.of_image)
  obtain ⟨l', c, hlc⟩ := funzionale_coniugato g l
  have chiave : ∀ u : A, l' (g u) = l u - c := by
    intro u
    have := hlc (g u)
    rw [g.symm_apply_apply] at this
    linarith
  refine ⟨l', ?_⟩
  ext x
  constructor
  · rintro ⟨u, huF, rfl⟩
    have hu : u ∈ {x ∈ s | ∀ y ∈ s, l y ≤ l x} := hl ▸ huF
    refine ⟨⟨u, hu.1, rfl⟩, ?_⟩
    rintro y ⟨w, hw, rfl⟩
    rw [chiave, chiave]
    have := hu.2 w hw
    linarith
  · rintro ⟨⟨u, hu, rfl⟩, hmax⟩
    refine ⟨u, ?_, rfl⟩
    rw [hl]
    refine ⟨hu, ?_⟩
    intro y hy
    have h := hmax (g y) ⟨y, hy, rfl⟩
    rw [chiave, chiave] at h
    linarith

/-- L'immagine sotto il coniugio: (g σ g⁻¹) '' X = g '' (σ '' (g⁻¹ '' X)). -/
theorem immagine_coniugata (g σ : A ≃ᵃⁱ[ℝ] A) (X : Set A) :
    (⇑((g.symm.trans σ).trans g)) '' X
      = (⇑g) '' ((⇑σ) '' ((⇑g.symm) '' X)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨σ (g.symm x), ⟨g.symm x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
    simp [AffineIsometryEquiv.coe_trans, Function.comp]
  · rintro ⟨y, ⟨w, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp [AffineIsometryEquiv.coe_trans, Function.comp]

/-- La preservazione passa all'inversa. -/
theorem preserva_symm (g : A ≃ᵃⁱ[ℝ] A) {s : Set A} (hg : (⇑g) '' s = s) :
    (⇑g.symm) '' s = s := by
  conv_lhs => rw [← hg]
  rw [Set.image_image]
  simp

section FinDim

variable [FiniteDimensional ℝ A]

/-- Metà della invarianza del rango: l'immagine non lo aumenta. -/
theorem finrank_vectorSpan_image_le (g : A ≃ᵃⁱ[ℝ] A) (F : Set A) :
    Module.finrank ℝ (vectorSpan ℝ ((⇑g) '' F))
      ≤ Module.finrank ℝ (vectorSpan ℝ F) := by
  have himg : ((⇑g) '' F) -ᵥ ((⇑g) '' F)
      = ⇑g.toAffineIsometry.linearIsometry '' (F -ᵥ F) := by
    ext d
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, y, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨u -ᵥ v, ⟨u, hu, v, hv, rfl⟩, ?_⟩
      have h := g.toAffineIsometry.toAffineMap.linearMap_vsub u v
      simpa using h
    · rintro ⟨d', ⟨u, hu, v, hv, rfl⟩, rfl⟩
      refine ⟨g u, ⟨u, hu, rfl⟩, g v, ⟨v, hv, rfl⟩, ?_⟩
      have h := g.toAffineIsometry.toAffineMap.linearMap_vsub u v
      simpa using h.symm
  show Module.finrank ℝ (Submodule.span ℝ (((⇑g) '' F) -ᵥ ((⇑g) '' F))) ≤ _
  rw [himg, ← LinearIsometry.coe_toLinearMap, Submodule.span_image]
  exact Submodule.finrank_map_le _ _

/-- Il rango dello span direzionale è invariante per isometrie affini. -/
theorem finrank_vectorSpan_image (g : A ≃ᵃⁱ[ℝ] A) (F : Set A) :
    Module.finrank ℝ (vectorSpan ℝ ((⇑g) '' F))
      = Module.finrank ℝ (vectorSpan ℝ F) := by
  refine le_antisymm (finrank_vectorSpan_image_le g F) ?_
  have h2 := finrank_vectorSpan_image_le g.symm ((⇑g) '' F)
  have hgs : ⇑g.symm '' ((⇑g) '' F) = F := by
    rw [Set.image_image]
    simp
  rwa [hgs] at h2

/-- Una faccetta trasportata da un'isometria che preserva il politopo è una
faccetta. -/
theorem isFacet_image (P : FiniteConvexPolytope A) (g : A ≃ᵃⁱ[ℝ] A)
    (hg : (⇑g) '' P.toSet = P.toSet) {F : Set A} (hF : P.IsFacet F) :
    P.IsFacet ((⇑g) '' F) := by
  refine ⟨⟨?_, hF.1.2.image ⇑g⟩, ?_⟩
  · have h := isExposed_image g hF.1.1
    rwa [hg] at h
  · rw [finrank_vectorSpan_image]
    exact hF.2

/-- Il coniugio degli iterati: (g ∘ ρ ∘ g⁻¹)ⁿ (g x) = g (ρⁿ x). -/
theorem iterato_coniugato (g ρ : A ≃ᵃⁱ[ℝ] A) (n : ℕ) (x : A) :
    (⇑((g.symm.trans ρ).trans g))^[n] (g x) = g ((⇑ρ)^[n] x) := by
  induction n generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have hstep : ((g.symm.trans ρ).trans g) (g x) = g (ρ x) := by
      simp [AffineIsometryEquiv.coe_trans, Function.comp]
    rw [hstep, ih]

/-- LA FACCETTA REGOLARE SI TRASPORTA: con g isometria che preserva il politopo,
g '' F è regolare dello stesso tipo e lato. -/
theorem isRegularFacet_image (P : FiniteConvexPolytope A) (g : A ≃ᵃⁱ[ℝ] A)
    (hg : (⇑g) '' P.toSet = P.toSet) {F : Set A} {p : ℕ} {ℓ : ℝ}
    (hF : P.IsRegularFacet F p ℓ) : P.IsRegularFacet ((⇑g) '' F) p ℓ := by
  obtain ⟨hfacet, hℓ, hp, ρ, x₀, hx₀, himg, hinj, hper, hhull, hdist⟩ := hF
  refine ⟨isFacet_image P g hg hfacet, hℓ, hp,
    (g.symm.trans ρ).trans g, g x₀, ⟨x₀, hx₀, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
      have hstep : ((g.symm.trans ρ).trans g) (g u) = g (ρ u) := by
        simp [AffineIsometryEquiv.coe_trans, Function.comp]
      rw [hstep]
      exact ⟨ρ u, himg ▸ ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      have hu' : u ∈ (⇑ρ) '' F := himg.symm ▸ hu
      obtain ⟨w, hw, rfl⟩ := hu'
      refine ⟨g w, ⟨w, hw, rfl⟩, ?_⟩
      simp [AffineIsometryEquiv.coe_trans, Function.comp]
  · intro i j hij
    simp only [iterato_coniugato] at hij
    exact hinj (g.injective hij)
  · rw [iterato_coniugato, hper]
  · have hg_hull : (⇑g) '' F = (⇑g) '' convexHull ℝ
        (Set.range fun i : Fin p => (⇑ρ)^[(i : ℕ)] x₀) := by rw [← hhull]
    have haff : (⇑g) '' convexHull ℝ (Set.range fun i : Fin p => (⇑ρ)^[(i : ℕ)] x₀)
        = convexHull ℝ ((⇑g) '' (Set.range fun i : Fin p => (⇑ρ)^[(i : ℕ)] x₀)) :=
      AffineMap.image_convexHull g.toAffineIsometry.toAffineMap _
    rw [hg_hull, haff]
    congr 1
    ext z
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      show (⇑((g.symm.trans ρ).trans g))^[(i : ℕ)] (g x₀)
        = g ((⇑ρ)^[(i : ℕ)] x₀)
      exact iterato_coniugato g ρ (i : ℕ) x₀
    · rintro ⟨i, rfl⟩
      refine ⟨(⇑ρ)^[(i : ℕ)] x₀, ⟨i, rfl⟩, ?_⟩
      show g ((⇑ρ)^[(i : ℕ)] x₀)
        = (⇑((g.symm.trans ρ).trans g))^[(i : ℕ)] (g x₀)
      exact (iterato_coniugato g ρ (i : ℕ) x₀).symm
  · have hstep : ((g.symm.trans ρ).trans g) (g x₀) = g (ρ x₀) := by
      simp [AffineIsometryEquiv.coe_trans, Function.comp]
    rw [hstep, g.dist_map]
    exact hdist

/-- IL FAN SI TRASPORTA: se v è q-ciclico e g preserva il politopo,
g v è q-ciclico. -/
theorem isCyclicVertex_image (P : FiniteConvexPolytope A) (g : A ≃ᵃⁱ[ℝ] A)
    (hg : (⇑g) '' P.toSet = P.toSet) {v : A} {q : ℕ}
    (hv : P.IsCyclicVertex v q) : P.IsCyclicVertex (g v) q := by
  obtain ⟨D⟩ := hv
  have hgsymm : (⇑g.symm) '' P.toSet = P.toSet := preserva_symm g hg
  refine ⟨⟨fun i => (⇑g) '' D.faccetta i,
    fun i => isFacet_image P g hg (D.isFacet i),
    fun i => ⟨v, D.mem_v i, rfl⟩,
    ?_, ?_,
    (g.symm.trans D.σ).trans g,
    ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- distinte
    intro i j hij
    exact D.distinte ((Set.image_injective.mpr g.injective) hij)
  · -- complete
    intro F hF hgvF
    have hF' : P.IsFacet ((⇑g.symm) '' F) := isFacet_image P g.symm hgsymm hF
    have hvF' : v ∈ (⇑g.symm) '' F := ⟨g v, hgvF, g.symm_apply_apply v⟩
    obtain ⟨i, hi⟩ := D.complete _ hF' hvF'
    refine ⟨i, ?_⟩
    rw [← hi, Set.image_image]
    simp
  · -- fissa il vertice
    show ((g.symm.trans D.σ).trans g) (g v) = g v
    have h1 : ((g.symm.trans D.σ).trans g) (g v) = g (D.σ (g.symm (g v))) := by
      simp [AffineIsometryEquiv.coe_trans, Function.comp]
    rw [h1, g.symm_apply_apply, D.fissa_v]
  · -- preserva il politopo
    rw [immagine_coniugata, hgsymm, D.preserva, hg]
  · -- ruota il fan
    intro i
    rw [immagine_coniugata]
    have hpre : (⇑g.symm) '' ((⇑g) '' D.faccetta i) = D.faccetta i := by
      rw [Set.image_image]; simp
    rw [hpre, D.ruota]
  · -- spigolo
    intro i
    obtain ⟨x, hxv, hx⟩ := D.spigolo i
    refine ⟨g x, fun h => hxv (g.injective h), ?_⟩
    exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
  · -- spigolo_due
    intro i j x hx hxv hxj
    obtain ⟨⟨u1, hu1, hu1e⟩, ⟨u2, hu2, hu2e⟩⟩ := hx
    obtain ⟨u3, hu3, hu3e⟩ := hxj
    have h12 : u2 = u1 := g.injective (by rw [hu1e, hu2e])
    have h13 : u3 = u1 := g.injective (by rw [hu1e, hu3e])
    rw [h12] at hu2
    rw [h13] at hu3
    have hu1v : u1 ≠ v := fun h => hxv (by rw [← hu1e, h])
    exact D.spigolo_due i j u1 ⟨hu1, hu2⟩ hu1v hu3

end FinDim

end FiniteConvexPolytope
