import Mathlib
import UnicoProofs.Platonici.Fondamenta
import UnicoProofs.Platonici.Carta
import UnicoProofs.Platonici.OrbitaTraslata
import UnicoProofs.Platonici.R2Base
import UnicoProofs.Platonici.AngoloVicini
import UnicoProofs.Platonici.SpigoloVicino

/-!
A15 — L'ANGOLO DELLA FACCETTA (campagna #50, il penultimo raccordo).

Da una faccetta p-gonale regolare e due sue facce esposte (gli spigoli del
fan, via A13), i cui punti non-vertice si escludono a vicenda e non sono
positivamente paralleli: l'angolo in v tra i due punti è (p−2)π/p.
Catena: carta della faccetta (A8) → orbita traslata (A10) → A14 due volte
(ciascuno spigolo punta a un vicino ±2π/p) → vicini distinti → L4
(angolo dei vicini = π − 2π/p, in coordinate) → ritorno in A.
-/

open Real
open scoped RealInnerProductSpace
open FiniteConvexPolytope PlatoniciA7 PlatoniciA8 PlatoniciA10 PlatoniciA14
open PlatoniciL4

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- L'ANGOLO DELLA FACCETTA: due facce esposte della faccetta regolare
per v, con punti non-vertice reciprocamente esclusi e non paralleli,
aprono in v l'angolo interno (p−2)π/p. -/
theorem angolo_della_faccetta (P : FiniteConvexPolytope A)
    {F : Set A} {p : ℕ} {ℓ : ℝ} (hreg : P.IsRegularFacet F p ℓ)
    {v : A} (hvF : v ∈ F) (hvex : v ∈ P.toSet.extremePoints ℝ)
    {B₁ B₂ : Set A} (hB₁ : IsExposed ℝ F B₁) (hB₂ : IsExposed ℝ F B₂)
    {x₁ x₂ : A}
    (hvB₁ : v ∈ B₁) (hvB₂ : v ∈ B₂)
    (hx₁ : x₁ ∈ B₁) (hx₂ : x₂ ∈ B₂)
    (hx₁v : x₁ ≠ v) (hx₂v : x₂ ≠ v)
    (hx₂B₁ : x₂ ∉ B₁) (hx₁B₂ : x₁ ∉ B₂)
    (hdir : ∀ c : ℝ, 0 < c → x₂ - v ≠ c • (x₁ - v)) :
    EuclideanGeometry.angle x₁ v x₂ = ((p : ℝ) - 2) * π / p := by
  classical
  have hπ : (0 : ℝ) < π := Real.pi_pos
  obtain ⟨hFacet, hℓ0, hp3, ρ, x₀, hx₀F, hρF, hinj₀, hclosed₀, hFhull, hdist⟩ :=
    hreg
  have hp0 : 0 < p := by omega
  have hp0R : (0 : ℝ) < p := by positivity
  -- ══ v nell'orbita, ciclo riletto da v ══
  have hvexF : v ∈ F.extremePoints ℝ :=
    estremo_ereditato hFacet.1.1.subset hvex hvF
  have hvorb : ∃ k : Fin p, (⇑ρ)^[(k : ℕ)] x₀ = v := by
    rw [hFhull] at hvexF
    exact estremo_in_orbita _ hvexF
  obtain ⟨k, hk⟩ := hvorb
  have hclosedv : (⇑ρ)^[p] v = v := by
    rw [← hk]
    exact orbita_traslata_chiusa (⇑ρ) x₀ p hclosed₀ (k : ℕ)
  have hinjv : Function.Injective (fun i : Fin p => (⇑ρ)^[(i : ℕ)] v) := by
    rw [← hk]
    exact orbita_traslata_iniettiva (⇑ρ) x₀ p hp0 hclosed₀ hinj₀ (k : ℕ)
  have hFv : F = convexHull ℝ
      (Set.range fun i : Fin p => (⇑ρ)^[(i : ℕ)] v) := by
    rw [hFhull]
    congr 1
    rw [← hk]
    exact (orbita_traslata_range (⇑ρ) x₀ p hp0 hclosed₀ (k : ℕ)).symm
  have hmemF : ∀ j : ℕ, (⇑ρ)^[j] v ∈ F := by
    intro j
    induction j with
    | zero => exact hvF
    | succ nn ih =>
        rw [Function.iterate_succ_apply']
        exact mem_of_invariante ρ hρF ih
  -- ══ la carta ══
  set W₂ : Submodule ℝ A := vectorSpan ℝ F with hW₂def
  have h2 : Module.finrank ℝ W₂ = 2 := hFacet.2
  haveI hfin2 : FiniteDimensional ℝ W₂ := by
    have h21 : Module.finrank ℝ W₂ = 1 + 1 := by omega
    exact Module.finite_of_finrank_eq_succ h21
  haveI hfact2 : Fact (Module.finrank ℝ W₂ = 2) := ⟨h2⟩
  set o₂ : Orientation ℝ W₂ (Fin 2) := orientazione2 W₂ h2 with ho₂def
  set χ := carta ρ F hρF v hvF with hχdef
  have hχclosed : (⇑χ)^[p] (0 : ↥W₂) = 0 :=
    carta_orbita_chiusa ρ F hρF v hvF p hclosedv
  have hχinj : Function.Injective
      (fun i : Fin p => (⇑χ)^[(i : ℕ)] (0 : ↥W₂)) :=
    carta_orbita_iniettiva ρ F hρF v hvF p hinjv
  -- ══ il baricentro come centro fisso ══
  have hccfix : ∃ cc : ↥W₂, χ cc = cc := by
    obtain ⟨mp, rfl⟩ : ∃ mp, p = mp + 1 := ⟨p - 1, by omega⟩
    exact ⟨Finset.univ.centroid ℝ
        (fun i : Fin (mp + 1) => (⇑χ)^[(i : ℕ)] 0),
      orbita_centroid_fisso χ 0 hχclosed⟩
  obtain ⟨cc, hcc⟩ := hccfix
  -- ══ corrispondenza F ↔ hull della carta ══
  set am : ↥W₂ →ᵃ[ℝ] A :=
    ((AffineEquiv.constVAdd ℝ A v).toAffineMap).comp
      W₂.subtype.toAffineMap with hamdef
  have ham_apply : ∀ y : ↥W₂, am y = v + (y : A) := fun y => rfl
  have ham_inj : Function.Injective am := by
    intro a b hab
    rw [ham_apply, ham_apply] at hab
    exact Subtype.ext (add_left_cancel hab)
  have ham_orbit : ∀ i : ℕ, am ((⇑χ)^[i] 0) = (⇑ρ)^[i] v := by
    intro i
    rw [ham_apply]
    exact carta_iterate ρ F hρF v hvF i
  have himg : am '' (Set.range fun i : Fin p => (⇑χ)^[(i : ℕ)] (0 : ↥W₂))
      = Set.range fun i : Fin p => (⇑ρ)^[(i : ℕ)] v := by
    ext z
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (ham_orbit (i : ℕ)).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(⇑χ)^[(i : ℕ)] 0, ⟨i, rfl⟩, ham_orbit (i : ℕ)⟩
  have hFimm : F = am '' (convexHull ℝ
      (Set.range fun i : Fin p => (⇑χ)^[(i : ℕ)] (0 : ↥W₂))) := by
    calc F = convexHull ℝ
          (Set.range fun i : Fin p => (⇑ρ)^[(i : ℕ)] v) := hFv
      _ = convexHull ℝ (am '' (Set.range fun i : Fin p =>
            (⇑χ)^[(i : ℕ)] (0 : ↥W₂))) := by rw [himg]
      _ = am '' (convexHull ℝ (Set.range fun i : Fin p =>
            (⇑χ)^[(i : ℕ)] (0 : ↥W₂))) :=
          (AffineMap.image_convexHull am _).symm
  have hmem_carta : ∀ {x : A}, x ∈ F → x - v ∈ W₂ := by
    intro x hx
    simpa using vsub_mem_vectorSpan ℝ hx hvF
  have hchart_mem : ∀ {x : A} (hx : x ∈ F),
      (⟨x - v, hmem_carta hx⟩ : ↥W₂) ∈ convexHull ℝ
        (Set.range fun i : Fin p => (⇑χ)^[(i : ℕ)] (0 : ↥W₂)) := by
    intro x hx
    have h1 : x ∈ am '' (convexHull ℝ
        (Set.range fun i : Fin p => (⇑χ)^[(i : ℕ)] (0 : ↥W₂))) := by
      rw [← hFimm]; exact hx
    obtain ⟨y, hy, hyx⟩ := h1
    have h2 : y = ⟨x - v, hmem_carta hx⟩ := by
      apply ham_inj
      rw [hyx, ham_apply]
      show x = v + (x - v)
      abel
    rw [← h2]
    exact hy
  -- ══ BLOCCO 1: A14 per B₁ ══
  obtain ⟨l₁, hl₁⟩ := hB₁ ⟨v, hvB₁⟩
  have hl₁v : ∀ w ∈ F, l₁ w ≤ l₁ v := by
    have h := hvB₁
    rw [hl₁] at h
    exact h.2
  have hx₁max : l₁ x₁ = l₁ v := by
    have h := hx₁
    rw [hl₁] at h
    exact le_antisymm (hl₁v x₁ h.1) (h.2 v (hB₁.subset hvB₁))
  set lam₁ : ↥W₂ →L[ℝ] ℝ := l₁.comp W₂.subtypeL with hlam₁def
  have hlam₁z : ∀ z : ↥W₂, lam₁ z = l₁ (z : A) := fun z => rfl
  have hzcoe : ∀ i : ℕ, (((⇑χ)^[i] (0 : ↥W₂) : ↥W₂) : A)
      = (⇑ρ)^[i] v - v := by
    intro i
    have h := ham_orbit i
    rw [ham_apply] at h
    exact eq_sub_of_add_eq' h
  have hl0₁ : ∀ i : Fin p, lam₁ ((⇑χ)^[(i : ℕ)] 0) ≤ lam₁ 0 := by
    intro i
    rw [hlam₁z, hlam₁z, hzcoe (i : ℕ)]
    show l₁ ((⇑ρ)^[(i : ℕ)] v - v) ≤ l₁ ((0 : ↥W₂) : A)
    rw [map_sub, show ((0 : ↥W₂) : A) = 0 from rfl, map_zero]
    have := hl₁v _ (hmemF (i : ℕ))
    linarith
  have hnc₁ : ∃ i : Fin p, lam₁ ((⇑χ)^[(i : ℕ)] 0) < lam₁ 0 := by
    by_contra hno
    push_neg at hno
    have hvert : ∀ i : Fin p, l₁ v ≤ l₁ ((⇑ρ)^[(i : ℕ)] v) := by
      intro i
      have h1 := hno i
      rw [hlam₁z, hlam₁z, hzcoe (i : ℕ)] at h1
      rw [map_sub, show ((0 : ↥W₂) : A) = 0 from rfl, map_zero] at h1
      linarith
    have hcx : Convex ℝ {w : A | l₁ v ≤ l₁ w} :=
      convex_halfSpace_ge (LinearMap.isLinear l₁.toLinearMap) (l₁ v)
    have hsub : (Set.range fun i : Fin p => (⇑ρ)^[(i : ℕ)] v)
        ⊆ {w : A | l₁ v ≤ l₁ w} := by
      rintro z ⟨i, rfl⟩
      exact hvert i
    have hall : F ⊆ {w : A | l₁ v ≤ l₁ w} := by
      rw [hFv]
      exact convexHull_min hsub hcx
    have hx₂mem : x₂ ∈ B₁ := by
      rw [hl₁]
      refine ⟨hB₂.subset hx₂, ?_⟩
      intro w hw
      have h1 : l₁ v ≤ l₁ x₂ := hall (hB₂.subset hx₂)
      have h2 : l₁ w ≤ l₁ v := hl₁v w hw
      linarith
    exact hx₂B₁ hx₂mem
  set y₁ : ↥W₂ := ⟨x₁ - v, hmem_carta (hB₁.subset hx₁)⟩ with hy₁def
  have hy₁mem := hchart_mem (hB₁.subset hx₁)
  have hy₁0 : y₁ ≠ 0 := by
    intro h0
    apply hx₁v
    have h1 : x₁ - v = 0 := congrArg Subtype.val h0
    exact sub_eq_zero.mp h1
  have hly₁ : lam₁ y₁ = lam₁ 0 := by
    rw [hlam₁z, hlam₁z, hy₁def]
    show l₁ (x₁ - v) = l₁ ((0 : ↥W₂) : A)
    rw [map_sub, show ((0 : ↥W₂) : A) = 0 from rfl, map_zero, hx₁max]
    ring
  obtain ⟨n₁, hn₁form, t₁, ht₁, hy₁n⟩ :=
    spigolo_verso_vicino o₂ χ cc hcc hp3 hχclosed hχinj lam₁ hl0₁ hnc₁
      hy₁mem hy₁0 hly₁
  -- ══ BLOCCO 2: A14 per B₂ ══
  obtain ⟨l₂, hl₂⟩ := hB₂ ⟨v, hvB₂⟩
  have hl₂v : ∀ w ∈ F, l₂ w ≤ l₂ v := by
    have h := hvB₂
    rw [hl₂] at h
    exact h.2
  have hx₂max : l₂ x₂ = l₂ v := by
    have h := hx₂
    rw [hl₂] at h
    exact le_antisymm (hl₂v x₂ h.1) (h.2 v (hB₂.subset hvB₂))
  set lam₂ : ↥W₂ →L[ℝ] ℝ := l₂.comp W₂.subtypeL with hlam₂def
  have hlam₂z : ∀ z : ↥W₂, lam₂ z = l₂ (z : A) := fun z => rfl
  have hl0₂ : ∀ i : Fin p, lam₂ ((⇑χ)^[(i : ℕ)] 0) ≤ lam₂ 0 := by
    intro i
    rw [hlam₂z, hlam₂z, hzcoe (i : ℕ)]
    show l₂ ((⇑ρ)^[(i : ℕ)] v - v) ≤ l₂ ((0 : ↥W₂) : A)
    rw [map_sub, show ((0 : ↥W₂) : A) = 0 from rfl, map_zero]
    have := hl₂v _ (hmemF (i : ℕ))
    linarith
  have hnc₂ : ∃ i : Fin p, lam₂ ((⇑χ)^[(i : ℕ)] 0) < lam₂ 0 := by
    by_contra hno
    push_neg at hno
    have hvert : ∀ i : Fin p, l₂ v ≤ l₂ ((⇑ρ)^[(i : ℕ)] v) := by
      intro i
      have h1 := hno i
      rw [hlam₂z, hlam₂z, hzcoe (i : ℕ)] at h1
      rw [map_sub, show ((0 : ↥W₂) : A) = 0 from rfl, map_zero] at h1
      linarith
    have hcx : Convex ℝ {w : A | l₂ v ≤ l₂ w} :=
      convex_halfSpace_ge (LinearMap.isLinear l₂.toLinearMap) (l₂ v)
    have hsub : (Set.range fun i : Fin p => (⇑ρ)^[(i : ℕ)] v)
        ⊆ {w : A | l₂ v ≤ l₂ w} := by
      rintro z ⟨i, rfl⟩
      exact hvert i
    have hall : F ⊆ {w : A | l₂ v ≤ l₂ w} := by
      rw [hFv]
      exact convexHull_min hsub hcx
    have hx₁mem : x₁ ∈ B₂ := by
      rw [hl₂]
      refine ⟨hB₁.subset hx₁, ?_⟩
      intro w hw
      have h1 : l₂ v ≤ l₂ x₁ := hall (hB₁.subset hx₁)
      have h2 : l₂ w ≤ l₂ v := hl₂v w hw
      linarith
    exact hx₁B₂ hx₁mem
  set y₂ : ↥W₂ := ⟨x₂ - v, hmem_carta (hB₂.subset hx₂)⟩ with hy₂def
  have hy₂mem := hchart_mem (hB₂.subset hx₂)
  have hy₂0 : y₂ ≠ 0 := by
    intro h0
    apply hx₂v
    have h1 : x₂ - v = 0 := congrArg Subtype.val h0
    exact sub_eq_zero.mp h1
  have hly₂ : lam₂ y₂ = lam₂ 0 := by
    rw [hlam₂z, hlam₂z, hy₂def]
    show l₂ (x₂ - v) = l₂ ((0 : ↥W₂) : A)
    rw [map_sub, show ((0 : ↥W₂) : A) = 0 from rfl, map_zero, hx₂max]
    ring
  obtain ⟨n₂, hn₂form, t₂, ht₂, hy₂n⟩ :=
    spigolo_verso_vicino o₂ χ cc hcc hp3 hχclosed hχinj lam₂ hl0₂ hnc₂
      hy₂mem hy₂0 hly₂
  -- ══ i due vicini sono distinti ══
  have hnne : n₁ ≠ n₂ := by
    intro heq
    apply hdir (t₂ / t₁) (div_pos ht₂ ht₁)
    have h1 : x₁ - v = t₁ • (n₁ : A) := by
      have := congrArg Subtype.val hy₁n
      simpa [hy₁def] using this
    have h2 : x₂ - v = t₂ • (n₂ : A) := by
      have := congrArg Subtype.val hy₂n
      simpa [hy₂def] using this
    rw [h1, h2, ← heq, smul_smul]
    congr 1
    exact (div_mul_cancel₀ t₂ (ne_of_gt ht₁)).symm
  -- ══ l'angolo dei vicini via L4 ══
  set d₀ : ↥W₂ := (0 : ↥W₂) - cc with hd₀def
  have hd₀ne : d₀ ≠ 0 := by
    intro h0
    have hcc0 : cc = 0 := by
      have h1 := congrArg (fun z : ↥W₂ => z + cc) h0
      simp [hd₀def] at h1
      exact h1.symm
    -- cc = 0 = χ^[0] 0 è un punto dell'orbita fisso: χ 0 = 0 e χ v-orbita...
    have hz1 : (⇑χ)^[1] (0 : ↥W₂) = 0 := by
      have := hcc
      rw [hcc0] at this
      simpa using this
    have h10 : (⟨1, by omega⟩ : Fin p) = ⟨0, by omega⟩ := by
      apply hχinj
      show (⇑χ)^[1] (0 : ↥W₂) = (⇑χ)^[0] 0
      rw [hz1]
      rfl
    have := congrArg Fin.val h10
    simp at this
  have hα0 : (0 : ℝ) < 2 * π / p := by positivity
  have hαπ : 2 * π / p < π := by
    rw [div_lt_iff₀ hp0R]
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    nlinarith
  have hL4 := angolo_vicini o₂ d₀ hd₀ne (2 * π / p) hα0 hαπ
  -- forma dei vicini come corde
  have hn₁c : (n₁ : ↥W₂) = cc + o₂.rotation ((2 * π / p : ℝ) : Real.Angle) d₀
      ∨ (n₁ : ↥W₂) = cc + o₂.rotation ((-(2 * π / p) : ℝ) : Real.Angle) d₀ := by
    rcases hn₁form with h | h
    · left; rw [h, hd₀def]
    · right; rw [h, hd₀def]
  have hn₂c : (n₂ : ↥W₂) = cc + o₂.rotation ((2 * π / p : ℝ) : Real.Angle) d₀
      ∨ (n₂ : ↥W₂) = cc + o₂.rotation ((-(2 * π / p) : ℝ) : Real.Angle) d₀ := by
    rcases hn₂form with h | h
    · left; rw [h, hd₀def]
    · right; rw [h, hd₀def]
  have hchord : ∀ (θs : Real.Angle),
      cc + o₂.rotation θs d₀ = o₂.rotation θs d₀ - d₀ := by
    intro θs
    rw [hd₀def]
    abel
  -- l'angolo tra n₁ e n₂ è π − 2π/p (nei due ordini)
  have hangolo_nn : InnerProductGeometry.angle (n₁ : ↥W₂) (n₂ : ↥W₂)
      = π - 2 * π / p := by
    rcases hn₁c with h1 | h1 <;> rcases hn₂c with h2 | h2
    · exact absurd (h1.trans h2.symm) hnne
    · rw [h1, h2, hchord, hchord]
      exact hL4
    · rw [h1, h2, hchord, hchord]
      rw [InnerProductGeometry.angle_comm]
      exact hL4
    · exact absurd (h1.trans h2.symm) hnne
  -- ══ ritorno in A ══
  have hx₁sub : x₁ - v = t₁ • ((n₁ : ↥W₂) : A) := by
    have := congrArg Subtype.val hy₁n
    simpa [hy₁def] using this
  have hx₂sub : x₂ - v = t₂ • ((n₂ : ↥W₂) : A) := by
    have := congrArg Subtype.val hy₂n
    simpa [hy₂def] using this
  have hcoeangle : InnerProductGeometry.angle ((n₁ : ↥W₂) : A) ((n₂ : ↥W₂) : A)
      = InnerProductGeometry.angle (n₁ : ↥W₂) (n₂ : ↥W₂) := rfl
  calc EuclideanGeometry.angle x₁ v x₂
      = InnerProductGeometry.angle (x₁ - v) (x₂ - v) := rfl
    _ = InnerProductGeometry.angle ((n₁ : ↥W₂) : A) ((n₂ : ↥W₂) : A) := by
        rw [hx₁sub, hx₂sub,
          InnerProductGeometry.angle_smul_left_of_pos _ _ ht₁,
          InnerProductGeometry.angle_smul_right_of_pos _ _ ht₂]
    _ = π - 2 * π / p := by rw [hcoeangle, hangolo_nn]
    _ = ((p : ℝ) - 2) * π / p := by
        field_simp
