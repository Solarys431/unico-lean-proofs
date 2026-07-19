import Mathlib
import Challenge
import Solution.FanVertice
import Solution.Scala
import Solution.ScalaFacce
import Solution.SimilarEquiv

/-!
RIGIDITÀ — IL TIPO CICLICO È INVARIANTE SOTTO OMOTETIA (19 lug 2026).

Il gemello-scaling dei trasporti isometrici (TrasportoData e
TrasportoFaccetta): il coniugio `coniugioScala` porta le rotazioni di
faccetta e le simmetrie cicliche di vertice sul politopo scalato, il lato
diventa `a * ℓ`, e `IsCyclicallyRegularOfType p q` si conserva. Questo è
il pezzo R′0 completo: nella rigidità si può normalizzare il lato del
rivale senza perdere il tipo.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- Il coniugio-scaling itera come lo scaling dell'iterata. -/
theorem coniugioScala_iterato (a : ℝ) (ha : a ≠ 0) (ρ : Isom 3)
    (x : E 3) (n : ℕ) :
    (⇑(coniugioScala a ha ρ))^[n] (a • x) = a • (⇑ρ)^[n] x := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih,
      Function.iterate_succ_apply']
    exact coniugioScala_smul a ha ρ ((⇑ρ)^[k] x)

/-- **IL TRASPORTO-SCALING DELLA FACCETTA REGOLARE**. -/
theorem isRegularFacet_scala (P : ConvexPolytope 3) {a : ℝ} (ha : 0 < a)
    {A : Set (E 3)} {p : ℕ} {ℓ : ℝ}
    (h : P.asFinite.IsRegularFacet A p ℓ) :
    (scala a (ne_of_gt ha) P).asFinite.IsRegularFacet
      ((fun x : E 3 => a • x) '' A) p (a * ℓ) := by
  classical
  have hane : a ≠ 0 := ne_of_gt ha
  obtain ⟨hFacet, hℓ, hp, ρ, x₀, hx₀A, hρA, hinj, hcl, hhull, hdist⟩ := h
  refine ⟨isFacet_scala hane hFacet, mul_pos ha hℓ, hp,
    coniugioScala a hane ρ, a • x₀, ⟨x₀, hx₀A, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- la faccetta immagine è fissata dal coniugio
    calc (⇑(coniugioScala a hane ρ)) '' ((fun x : E 3 => a • x) '' A)
        = (fun x : E 3 => coniugioScala a hane ρ (a • x)) '' A :=
          Set.image_image _ _ _
      _ = (fun x : E 3 => a • ρ x) '' A := by
          have hcomp : (fun x : E 3 => coniugioScala a hane ρ (a • x)) =
              fun x : E 3 => a • ρ x := by
            funext z
            exact coniugioScala_smul a hane ρ z
          rw [hcomp]
      _ = (fun x : E 3 => a • x) '' ((⇑ρ) '' A) :=
          (Set.image_image _ _ _).symm
      _ = (fun x : E 3 => a • x) '' A := by rw [hρA]
  · -- iniettività dell'orbita scalata
    intro i j hij
    apply hinj
    have h1 := coniugioScala_iterato a hane ρ x₀ (i : ℕ)
    have h2 := coniugioScala_iterato a hane ρ x₀ (j : ℕ)
    have h3 : a • (⇑ρ)^[(i : ℕ)] x₀ = a • (⇑ρ)^[(j : ℕ)] x₀ := by
      rw [← h1, ← h2]
      exact hij
    exact smul_right_injective (E 3) hane h3
  · -- chiusura a p passi
    rw [coniugioScala_iterato a hane ρ x₀ p, hcl]
  · -- l'hull dell'orbita scalata
    have hr : (Set.range fun i : Fin p =>
        (⇑(coniugioScala a hane ρ))^[(i : ℕ)] (a • x₀)) =
        (fun x : E 3 => a • x) ''
          (Set.range fun i : Fin p => (⇑ρ)^[(i : ℕ)] x₀) := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨(⇑ρ)^[(i : ℕ)] x₀, ⟨i, rfl⟩,
          (coniugioScala_iterato a hane ρ x₀ (i : ℕ)).symm⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, coniugioScala_iterato a hane ρ x₀ (i : ℕ)⟩
    rw [hr]
    have himg := (omotetia a hane (n := 3)).toAffineMap.image_convexHull
      (Set.range fun i : Fin p => (⇑ρ)^[(i : ℕ)] x₀)
    have hco : (⇑(omotetia a hane (n := 3)).toAffineMap : E 3 → E 3) =
        fun x : E 3 => a • x := rfl
    rw [hco] at himg
    rw [hhull]
    exact himg
  · -- il passo dell'orbita scala del fattore a
    rw [coniugioScala_smul a hane ρ x₀, dist_smul_pos ha, hdist]

/-- **IL TRASPORTO-SCALING DEI DATI DI VERTICE CICLICO**. -/
theorem cyclicVertexData_scala (P : ConvexPolytope 3) {a : ℝ} (ha : 0 < a)
    {v : E 3} {q : ℕ} (h : P.asFinite.CyclicVertexData v q) :
    Nonempty ((scala a (ne_of_gt ha) P).asFinite.CyclicVertexData
      (a • v) q) := by
  classical
  have hane : a ≠ 0 := ne_of_gt ha
  have hinj_smul : Function.Injective (fun x : E 3 => a • x) :=
    smul_right_injective (E 3) hane
  have hinj_img : Function.Injective
      (Set.image (fun x : E 3 => a • x)) :=
    Set.image_injective.mpr hinj_smul
  refine ⟨{
    faccetta := fun i => (fun x : E 3 => a • x) '' h.faccetta i
    isFacet := fun i => isFacet_scala hane (h.isFacet i)
    mem_v := fun i => ⟨v, h.mem_v i, rfl⟩
    distinte := fun i j hij => h.distinte (hinj_img hij)
    complete := ?_
    σ := coniugioScala a hane h.σ
    fissa_v := ?_
    preserva := ?_
    ruota := ?_
    spigolo := ?_
    spigolo_due := ?_ }⟩
  · -- completezza del fan scalato
    intro F hF hvF
    obtain ⟨hfacetP, hround⟩ := isFacet_of_scala hane hF
    have hvmem : v ∈ (fun x : E 3 => a⁻¹ • x) '' F := by
      refine ⟨a • v, hvF, ?_⟩
      show a⁻¹ • a • v = v
      rw [smul_smul, inv_mul_cancel₀ hane, one_smul]
    obtain ⟨i, hFi⟩ := h.complete _ hfacetP hvmem
    exact ⟨i, by rw [hround, hFi]⟩
  · -- il coniugio fissa il vertice scalato
    rw [coniugioScala_smul a hane h.σ v, h.fissa_v]
  · -- il coniugio preserva il corpo scalato
    rw [toSet_scala_finite a hane P]
    calc (⇑(coniugioScala a hane h.σ)) ''
          ((fun x : E 3 => a • x) '' P.asFinite.toSet)
        = (fun x : E 3 => coniugioScala a hane h.σ (a • x)) ''
            P.asFinite.toSet := Set.image_image _ _ _
      _ = (fun x : E 3 => a • h.σ x) '' P.asFinite.toSet := by
          have hcomp : (fun x : E 3 =>
              coniugioScala a hane h.σ (a • x)) =
              fun x : E 3 => a • h.σ x := by
            funext z
            exact coniugioScala_smul a hane h.σ z
          rw [hcomp]
      _ = (fun x : E 3 => a • x) '' ((⇑h.σ) '' P.asFinite.toSet) :=
          (Set.image_image _ _ _).symm
      _ = (fun x : E 3 => a • x) '' P.asFinite.toSet := by
          rw [h.preserva]
  · -- il coniugio ruota il fan scalato
    intro i
    calc (⇑(coniugioScala a hane h.σ)) ''
          ((fun x : E 3 => a • x) '' h.faccetta i)
        = (fun x : E 3 => coniugioScala a hane h.σ (a • x)) ''
            h.faccetta i := Set.image_image _ _ _
      _ = (fun x : E 3 => a • h.σ x) '' h.faccetta i := by
          have hcomp : (fun x : E 3 =>
              coniugioScala a hane h.σ (a • x)) =
              fun x : E 3 => a • h.σ x := by
            funext z
            exact coniugioScala_smul a hane h.σ z
          rw [hcomp]
      _ = (fun x : E 3 => a • x) '' ((⇑h.σ) '' h.faccetta i) :=
          (Set.image_image _ _ _).symm
      _ = (fun x : E 3 => a • x) '' h.faccetta (finRotate q i) := by
          rw [h.ruota i]
  · -- lo spigolo condiviso sopravvive allo scaling
    intro i
    obtain ⟨x, hxv, hx⟩ := h.spigolo i
    refine ⟨a • x, ?_, ⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
    intro hcontra
    exact hxv (hinj_smul hcontra)
  · -- ogni spigolo ha due sole facce, anche scalato
    intro i j x hx hxv hxj
    obtain ⟨y₁, hy₁, hxy₁⟩ := hx.1
    obtain ⟨y₂, hy₂, hxy₂⟩ := hx.2
    have hxy₁' : a • y₁ = x := hxy₁
    have hxy₂' : a • y₂ = x := hxy₂
    have hy12 : y₁ = y₂ := by
      apply hinj_smul
      show a • y₁ = a • y₂
      rw [hxy₁', hxy₂']
    obtain ⟨y₃, hy₃, hxy₃⟩ := hxj
    have hxy₃' : a • y₃ = x := hxy₃
    have hy13 : y₁ = y₃ := by
      apply hinj_smul
      show a • y₁ = a • y₃
      rw [hxy₁', hxy₃']
    have hyv : y₁ ≠ v := by
      intro hcontra
      apply hxv
      rw [← hxy₁', hcontra]
    refine h.spigolo_due i j y₁ ⟨hy₁, ?_⟩ hyv ?_
    · rw [hy12]
      exact hy₂
    · rw [hy13]
      exact hy₃

/-- **IL TIPO CICLICO È INVARIANTE SOTTO OMOTETIA POSITIVA**. -/
theorem cyclicallyRegular_scala (P : ConvexPolytope 3) {a : ℝ}
    (ha : 0 < a) {p q : ℕ}
    (h : P.asFinite.IsCyclicallyRegularOfType p q) :
    (scala a (ne_of_gt ha) P).asFinite.IsCyclicallyRegularOfType p q := by
  classical
  have hane : a ≠ 0 := ne_of_gt ha
  obtain ⟨hrank, hp, hq, ℓ, hℓ, hfacets, hvertices⟩ := h
  refine ⟨?_, hp, hq, a * ℓ, mul_pos ha hℓ, ?_, ?_⟩
  · -- il rank pieno si conserva
    have hset : (((scala a (ne_of_gt ha) P).vertices :
        Finset (E 3)) : Set (E 3)) =
        (fun x : E 3 => a • x) ''
          ((P.vertices : Finset (E 3)) : Set (E 3)) := by
      show ((P.vertices.image (a • ·) : Finset (E 3)) : Set (E 3)) = _
      ext x
      simp
    show Module.finrank ℝ (vectorSpan ℝ
      (((scala a (ne_of_gt ha) P).vertices : Finset (E 3)) :
        Set (E 3))) = 3
    rw [hset, finrank_vectorSpan_smul a hane]
    exact hrank
  · -- ogni faccetta scalata è regolare di lato a*ℓ
    intro F hF
    obtain ⟨hfacetP, hround⟩ := isFacet_of_scala hane hF
    have hreg := isRegularFacet_scala P ha (hfacets _ hfacetP)
    rw [← hround] at hreg
    exact hreg
  · -- ogni vertice scalato è q-ciclico
    intro w hw
    have hw' : w ∈ P.vertices.image (a • ·) := hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw'
    obtain ⟨D⟩ := hvertices v hv
    exact cyclicVertexData_scala P ha D

end LeanEval.Geometry.PlatonicClassification
