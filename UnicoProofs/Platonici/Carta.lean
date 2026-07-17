import Mathlib

/-!
A7 — LA DISCESA AL PIANO (campagna #50, assemblaggio).

Il primo gradino della discesa A → V₃ → W:

* `vectorSpan_invariante` — un insieme σ-invariante ha vectorSpan invariante
  per la parte lineare di σ;
* `discesa` — la restrizione della parte lineare a ↥(vectorSpan): l'isometria
  lineare del 3-spazio del politopo. Da qui `restrizione` (CatenaAE) scende
  ulteriormente al piano ortogonale all'asse;
* `discesa_apply` — la discesa agisce come la parte lineare;
* `orientazione2` — ogni spazio 2D reale ammette un'orientazione (per il
  killer, A4 e A5 serve un testimone, non una scelta canonica);
* `riesz_sotto` + `riesz_sotto_spec` — il vettore di Riesz della restrizione
  di un funzionale a un sottospazio finito-dimensionale: trasforma il
  funzionale della faccetta (A3) nel vettore n del killer.
-/

open Real
open scoped RealInnerProductSpace

namespace PlatoniciA7

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- Il vectorSpan di un insieme σ-invariante è invariante per la parte
lineare di σ. -/
theorem vectorSpan_invariante (σ : A ≃ᵃⁱ[ℝ] A) (S : Set A)
    (hS : (⇑σ) '' S = S) :
    (vectorSpan ℝ S).map
      (σ.linearIsometryEquiv.toLinearEquiv : A →ₗ[ℝ] A) = vectorSpan ℝ S := by
  have h := AffineMap.map_vectorSpan (k := ℝ)
    (f := (σ.toAffineEquiv : A →ᵃ[ℝ] A)) (s := S)
  have hcoe : (⇑(σ.toAffineEquiv : A →ᵃ[ℝ] A)) '' S = (⇑σ) '' S := by
    congr 1
  rw [hcoe, hS] at h
  rw [← h]
  congr 1

/-- La discesa: la parte lineare di σ ristretta al vectorSpan di un insieme
σ-invariante, come isometria lineare del sottospazio. -/
noncomputable def discesa (σ : A ≃ᵃⁱ[ℝ] A) (S : Set A)
    (hS : (⇑σ) '' S = S) :
    ↥(vectorSpan ℝ S) ≃ₗᵢ[ℝ] ↥(vectorSpan ℝ S) :=
  (LinearIsometryEquiv.submoduleMap (vectorSpan ℝ S) σ.linearIsometryEquiv).trans
    (LinearIsometryEquiv.ofEq _ _ (vectorSpan_invariante σ S hS))

/-- La discesa agisce come la parte lineare di σ. -/
@[simp]
theorem discesa_apply (σ : A ≃ᵃⁱ[ℝ] A) (S : Set A) (hS : (⇑σ) '' S = S)
    (z : ↥(vectorSpan ℝ S)) :
    (discesa σ S hS z : A) = σ.linearIsometryEquiv (z : A) := rfl

/-- Ogni spazio reale 2-dimensionale ammette un'orientazione. -/
noncomputable def orientazione2 (W : Type*) [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (h2 : Module.finrank ℝ W = 2) : Orientation ℝ W (Fin 2) :=
  (Module.finBasisOfFinrankEq ℝ W h2).orientation

/-- Il vettore di Riesz della restrizione di un funzionale a un sottospazio
finito-dimensionale. -/
noncomputable def riesz_sotto (W : Submodule ℝ A) [FiniteDimensional ℝ ↥W]
    (l : A →L[ℝ] ℝ) : ↥W :=
  (InnerProductSpace.toDual ℝ ↥W).symm (l.comp W.subtypeL)

/-- Il vettore di Riesz rappresenta la restrizione: ⟪n, z⟫ = l z per z ∈ W. -/
theorem riesz_sotto_spec (W : Submodule ℝ A) [FiniteDimensional ℝ ↥W]
    (l : A →L[ℝ] ℝ) (z : ↥W) :
    ⟪riesz_sotto W l, z⟫ = l (z : A) := by
  rw [riesz_sotto, InnerProductSpace.toDual_symm_apply]
  rfl

end PlatoniciA7

/-!
A8 — LA CARTA DELLA FACCETTA (campagna #50, assemblaggio).

La faccetta F vive in un piano affine di A; il suo poligono orbitale va letto
nel modello vettoriale ↥(vectorSpan ℝ F) con origine in un vertice v. La
scoperta che semplifica tutto: l'azione di σ nella carta è
y ↦ (discesa σ) y + (σ v − v), cioè parte lineare GIÀ CERTIFICATA più una
traslazione costante. Da qui: coniugazione, orbita, iniettività, chiusura e
trasporto dell'angolo. Con questi pezzi il teorema dell'angolo interno di
sol si istanzia con E := ↥(vectorSpan ℝ F).
-/

namespace PlatoniciA8

open PlatoniciA7

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- Un insieme σ-invariante trattiene le immagini dei suoi punti. -/
theorem mem_of_invariante (σ : A ≃ᵃⁱ[ℝ] A) {F : Set A}
    (hF : (⇑σ) '' F = F) {v : A} (hv : v ∈ F) : σ v ∈ F := by
  rw [← hF]
  exact Set.mem_image_of_mem _ hv

/-- La traslazione della carta appartiene al piano della faccetta. -/
theorem trasl_mem (σ : A ≃ᵃⁱ[ℝ] A) {F : Set A} (hF : (⇑σ) '' F = F)
    {v : A} (hv : v ∈ F) : σ v - v ∈ vectorSpan ℝ F := by
  have h1 : σ v ∈ F := mem_of_invariante σ hF hv
  simpa using vsub_mem_vectorSpan ℝ h1 hv

/-- La carta della faccetta: l'azione di σ sul piano di F letta dall'origine
v, cioè y ↦ (discesa σ) y + (σ v − v). -/
noncomputable def carta (σ : A ≃ᵃⁱ[ℝ] A) (F : Set A) (hF : (⇑σ) '' F = F)
    (v : A) (hv : v ∈ F) :
    ↥(vectorSpan ℝ F) ≃ᵃⁱ[ℝ] ↥(vectorSpan ℝ F) :=
  (discesa σ F hF).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ ↥(vectorSpan ℝ F)
      ⟨σ v - v, trasl_mem σ hF hv⟩)

/-- La carta coniuga σ: v + carta y = σ (v + y). -/
theorem carta_apply (σ : A ≃ᵃⁱ[ℝ] A) (F : Set A) (hF : (⇑σ) '' F = F)
    (v : A) (hv : v ∈ F) (y : ↥(vectorSpan ℝ F)) :
    v + (carta σ F hF v hv y : A) = σ (v + (y : A)) := by
  have hlin : σ.linearIsometryEquiv ((v + (y : A)) -ᵥ v) = σ (v + (y : A)) -ᵥ σ v :=
    σ.map_vsub (v + (y : A)) v
  simp only [vsub_eq_sub, add_sub_cancel_left] at hlin
  have hcoe : (carta σ F hF v hv y : A)
      = (σ v - v) + σ.linearIsometryEquiv (y : A) := rfl
  rw [hcoe, hlin]
  abel

/-- L'orbita della carta da 0 è l'orbita di σ da v, riletta dall'origine. -/
theorem carta_iterate (σ : A ≃ᵃⁱ[ℝ] A) (F : Set A) (hF : (⇑σ) '' F = F)
    (v : A) (hv : v ∈ F) (k : ℕ) :
    v + (((⇑(carta σ F hF v hv))^[k] 0 : ↥(vectorSpan ℝ F)) : A)
      = (⇑σ)^[k] v := by
  induction k with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        carta_apply, ih]

/-- L'iniettività del ciclo di σ su v si trasporta alla carta. -/
theorem carta_orbita_iniettiva (σ : A ≃ᵃⁱ[ℝ] A) (F : Set A)
    (hF : (⇑σ) '' F = F) (v : A) (hv : v ∈ F) (p : ℕ)
    (hinj : Function.Injective (fun i : Fin p => (⇑σ)^[(i : ℕ)] v)) :
    Function.Injective
      (fun i : Fin p => (⇑(carta σ F hF v hv))^[(i : ℕ)] (0 : ↥(vectorSpan ℝ F))) := by
  intro i j hij
  apply hinj
  have hij' : (⇑(carta σ F hF v hv))^[(i : ℕ)] (0 : ↥(vectorSpan ℝ F))
      = (⇑(carta σ F hF v hv))^[(j : ℕ)] (0 : ↥(vectorSpan ℝ F)) := hij
  show (⇑σ)^[(i : ℕ)] v = (⇑σ)^[(j : ℕ)] v
  rw [← carta_iterate σ F hF v hv (i : ℕ), ← carta_iterate σ F hF v hv (j : ℕ),
    hij']

/-- La chiusura del ciclo di σ su v si trasporta alla carta. -/
theorem carta_orbita_chiusa (σ : A ≃ᵃⁱ[ℝ] A) (F : Set A)
    (hF : (⇑σ) '' F = F) (v : A) (hv : v ∈ F) (p : ℕ)
    (hclosed : (⇑σ)^[p] v = v) :
    (⇑(carta σ F hF v hv))^[p] (0 : ↥(vectorSpan ℝ F)) = 0 := by
  have h := carta_iterate σ F hF v hv p
  rw [hclosed] at h
  have h2 : (((⇑(carta σ F hF v hv))^[p] 0 : ↥(vectorSpan ℝ F)) : A) = 0 := by
    have := congrArg (fun z => z - v) h
    simpa using this
  exact Subtype.ext h2

/-- L'angolo euclideo si legge indifferentemente nella carta o nell'ambiente. -/
theorem angolo_carta {W : Submodule ℝ A} (v : A) (x y z : ↥W) :
    EuclideanGeometry.angle (v + (y : A)) (v + (x : A)) (v + (z : A))
      = EuclideanGeometry.angle y x z := by
  unfold EuclideanGeometry.angle
  have h1 : (v + (y : A)) -ᵥ (v + (x : A)) = ((y -ᵥ x : ↥W) : A) := by
    simp
  have h2 : (v + (z : A)) -ᵥ (v + (x : A)) = ((z -ᵥ x : ↥W) : A) := by
    simp
  rw [h1, h2]
  rfl

end PlatoniciA8
