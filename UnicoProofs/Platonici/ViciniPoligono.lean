import Mathlib
import UnicoProofs.Platonici.Fondamenta
import UnicoProofs.Platonici.Carta
import UnicoProofs.Platonici.OrbitaTraslata
import UnicoProofs.Platonici.R2Base
import UnicoProofs.Platonici.AngoloInterno

/-!
A12a — I VICINI DEL POLIGONO (campagna #50, assemblaggio, lato faccetta).

L'istanza del teorema dell'angolo interno (AngoloInterno, certificato) nella
carta della faccetta regolare: da `IsRegularFacet F p ℓ` e un vertice v
estremo, esistono due punti y, z della faccetta, distinti da v e tra loro,
con ∠ y v z = (p−2)π/p. La salita: v sta nell'orbita del poligono
(`estremo_in_orbita`), l'orbita si rilegge da v (`orbita_traslata_*`), la
carta la porta nel modello 2D (`carta_*`), il baricentro ρ-fisso fa da
centro (`orbita_centroid_fisso`), e l'angolo torna in A (`angolo_carta`).

Il pezzo mancante (A12b, con G1): y e z stanno sui raggi degli spigoli
del fan, quindi questo angolo È l'angolo tra le direzioni del fan.
-/

open Real
open scoped RealInnerProductSpace
open FiniteConvexPolytope PlatoniciA7 PlatoniciA8 PlatoniciA10

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- I VICINI DEL POLIGONO: in una faccetta p-gonale regolare, da ogni
vertice estremo v escono due punti della faccetta che aprono l'angolo
interno (p−2)π/p. -/
theorem vicini_del_poligono (P : FiniteConvexPolytope A)
    {F : Set A} {p : ℕ} {ℓ : ℝ} (hreg : P.IsRegularFacet F p ℓ)
    {v : A} (hvF : v ∈ F) (hvex : v ∈ P.toSet.extremePoints ℝ) :
    ∃ y z : A, y ∈ F ∧ z ∈ F ∧ y ≠ v ∧ z ≠ v ∧ y ≠ z ∧
      EuclideanGeometry.angle y v z = ((p : ℝ) - 2) * π / p := by
  obtain ⟨hFacet, hℓ0, hp3, ρ, x₀, hx₀F, hρF, hinj₀, hclosed₀, hFhull, hdist⟩ :=
    hreg
  have hp0 : 0 < p := by omega
  -- ══ v sta nell'orbita del poligono ══
  have hvexF : v ∈ F.extremePoints ℝ :=
    estremo_ereditato hFacet.1.1.subset hvex hvF
  have hvorb : ∃ k : Fin p, (⇑ρ)^[(k : ℕ)] x₀ = v := by
    rw [hFhull] at hvexF
    exact estremo_in_orbita _ hvexF
  obtain ⟨k, hk⟩ := hvorb
  -- ══ il ciclo si rilegge da v ══
  have hclosedv : (⇑ρ)^[p] v = v := by
    rw [← hk]
    exact orbita_traslata_chiusa (⇑ρ) x₀ p hclosed₀ (k : ℕ)
  have hinjv : Function.Injective (fun i : Fin p => (⇑ρ)^[(i : ℕ)] v) := by
    rw [← hk]
    exact orbita_traslata_iniettiva (⇑ρ) x₀ p hp0 hclosed₀ hinj₀ (k : ℕ)
  -- ogni punto dell'orbita da v resta nella faccetta
  have hmemF : ∀ j : ℕ, (⇑ρ)^[j] v ∈ F := by
    intro j
    induction j with
    | zero => exact hvF
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact mem_of_invariante ρ hρF ih
  -- ══ la carta della faccetta ══
  set W₂ : Submodule ℝ A := vectorSpan ℝ F with hW₂def
  have h2 : Module.finrank ℝ W₂ = 2 := hFacet.2
  haveI hfin2 : FiniteDimensional ℝ W₂ := by
    have h21 : Module.finrank ℝ W₂ = 1 + 1 := by omega
    exact Module.finite_of_finrank_eq_succ h21
  haveI hfact2 : Fact (Module.finrank ℝ W₂ = 2) := ⟨h2⟩
  haveI hor2 : Module.Oriented ℝ W₂ (Fin 2) := ⟨orientazione2 W₂ h2⟩
  set χ := carta ρ F hρF v hvF with hχdef
  -- chiusura e iniettività nella carta
  have hχclosed : (⇑χ)^[p] (0 : ↥W₂) = 0 :=
    carta_orbita_chiusa ρ F hρF v hvF p hclosedv
  have hχinj : Function.Injective
      (fun i : Fin p => (⇑χ)^[(i : ℕ)] (0 : ↥W₂)) :=
    carta_orbita_iniettiva ρ F hρF v hvF p hinjv
  -- ══ il centro fisso: il baricentro dell'orbita nella carta ══
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  set cc : ↥W₂ :=
    Finset.univ.centroid ℝ (fun i : Fin (m + 1) => (⇑χ)^[(i : ℕ)] 0)
    with hccdef
  have hccfix : χ cc = cc :=
    orbita_centroid_fisso χ 0 hχclosed
  -- ══ l'istanza del teorema dell'angolo interno ══
  have hmain := AngoloInterno.affine_isometry_orbit_hull_internal_angle
    (m + 1) hp3 χ 0 cc hccfix
    (by
      show (⇑χ)^[m + 1] (0 : ↥W₂) = 0
      exact hχclosed)
    (by
      intro i j hij
      exact hχinj hij)
    ⟨0, by omega⟩
  obtain ⟨iy, iz, hiy, hiz, hyz, _, hangle⟩ := hmain
  -- ══ ritorno in A ══
  refine ⟨v + ((AngoloInterno.orbitPoint χ 0 (iy : ℕ) : ↥W₂) : A),
    v + ((AngoloInterno.orbitPoint χ 0 (iz : ℕ) : ↥W₂) : A), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := carta_iterate ρ F hρF v hvF (iy : ℕ)
    show v + (((⇑χ)^[(iy : ℕ)] 0 : ↥W₂) : A) ∈ F
    rw [hχdef] at *
    rw [this]
    exact hmemF _
  · have := carta_iterate ρ F hρF v hvF (iz : ℕ)
    show v + (((⇑χ)^[(iz : ℕ)] 0 : ↥W₂) : A) ∈ F
    rw [hχdef] at *
    rw [this]
    exact hmemF _
  · intro h0
    apply hiy
    apply hχinj
    show (⇑χ)^[(iy : ℕ)] (0 : ↥W₂) = (⇑χ)^[((⟨0, by omega⟩ : Fin (m + 1)) : ℕ)] 0
    have h1 : ((AngoloInterno.orbitPoint χ 0 (iy : ℕ) : ↥W₂) : A) = 0 := by
      have := add_right_injective v (h0.trans (add_zero v).symm)
      exact this
    have h2 : (AngoloInterno.orbitPoint χ 0 (iy : ℕ) : ↥W₂) = 0 :=
      Subtype.ext h1
    exact h2
  · intro h0
    apply hiz
    apply hχinj
    show (⇑χ)^[(iz : ℕ)] (0 : ↥W₂) = (⇑χ)^[((⟨0, by omega⟩ : Fin (m + 1)) : ℕ)] 0
    have h1 : ((AngoloInterno.orbitPoint χ 0 (iz : ℕ) : ↥W₂) : A) = 0 := by
      have := add_right_injective v (h0.trans (add_zero v).symm)
      exact this
    exact Subtype.ext h1
  · intro h0
    apply hyz
    apply hχinj
    show (⇑χ)^[(iy : ℕ)] (0 : ↥W₂) = (⇑χ)^[(iz : ℕ)] 0
    have h1 := add_right_injective v h0
    exact Subtype.ext h1
  · have htrasp := angolo_carta (W := W₂) v
      (AngoloInterno.orbitPoint χ 0 ((⟨0, by omega⟩ : Fin (m + 1)) : ℕ))
      (AngoloInterno.orbitPoint χ 0 (iy : ℕ))
      (AngoloInterno.orbitPoint χ 0 (iz : ℕ))
    have hzero : v + ((AngoloInterno.orbitPoint χ 0
        ((⟨0, by omega⟩ : Fin (m + 1)) : ℕ) : ↥W₂) : A) = v := by
      show v + (((⇑χ)^[0] (0 : ↥W₂) : ↥W₂) : A) = v
      simp
    rw [hzero] at htrasp
    rw [htrasp]
    exact hangle
