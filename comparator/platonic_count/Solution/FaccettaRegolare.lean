import Mathlib
import Challenge
import Solution.PerturbazioneFinita
import Solution.VerticiEsposti
import Solution.SottoPolitopo
import Solution.DimStretta
import Solution.Interpolazione
import Solution.ScalaBandiere
import Solution.BandieraCompagna
import Solution.Diamante
import Solution.Diamante2D
import Solution.SecondoSpigolo
import Solution.SecondaFaccetta
import Solution.BandieraVertice
import Solution.ConoVertice
import Solution.PassoFan
import Solution.Immagini
import Solution.OrbitaFan
import Solution.PoligonoConnesso
import Solution.CicloPoligono
import Solution.Camminata
import Solution.ScaricoSpigolo
import Solution.FanVertice
import Solution.Fondamenta
import Solution.ConnessioneVentaglio
import Solution.Liberta

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

theorem ciclo_poligono_orbita_completa
    (P : ConvexPolytope 3) {A : Set (E 3)} (hA : P.IsFace A)
    (hdA : faceDim A = 2) {x₀ : E 3} {σ : Isom 3} {m : ℕ}
    (C : CicloPoligono P A x₀ σ m) :
    ∀ z ∈ (facePolytope P hA).vertices,
      ∃ k : ℕ, k < m ∧ z = (⇑σ)^[k] x₀ := by
  classical
  let v : ℕ → E 3 := fun k => (⇑σ)^[k] x₀
  let e : ℕ → Set (E 3) :=
    fun k => (⇑σ)^[k] '' (segment ℝ x₀ (σ x₀))
  have hv (k : ℕ) : v k ∈ P.vertices ∧ v k ∈ A := by
    simpa [v] using C.vertice k
  have he (k : ℕ) : P.IsFace (e k) ∧ faceDim (e k) = 1 ∧ e k ⊆ A ∧
      e k = segment ℝ (v k) (v (k + 1)) := by
    simpa [e, v] using C.spigolo k
  have hvperiod (j : ℕ) : v (j + m) = v j := by
    dsimp [v]
    rw [Function.iterate_add]
    simp only [Function.comp_apply, C.ritorno]
  have hvm : v m = v 0 := by
    simpa using hvperiod 0
  have hem : e m = e 0 := by
    calc
      e m = segment ℝ (v m) (v (m + 1)) := (he m).2.2.2
      _ = segment ℝ (v 0) (v 1) := by
        rw [hvm]
        have h := hvperiod 1
        rw [Nat.add_comm 1 m] at h
        rw [h]
      _ = e 0 := (he 0).2.2.2.symm
  have hv_in_e (k : ℕ) : v k ∈ e k := by
    rw [(he k).2.2.2]
    exact left_mem_segment ℝ _ _
  have hends (k : ℕ) {z : E 3}
      (hzQ : z ∈ (facePolytope P hA).vertices) (hze : z ∈ e k) :
      z = v k ∨ z = v (k + 1) := by
    have hzV : z ∈ P.vertices := (Finset.mem_filter.mp hzQ).1
    apply vertice_estremo_del_segmento P (he k).1 (he k).2.2.2
    · simpa [v] using (C.passo_nuovo k).symm
    · exact hzV
    · exact hze
  have htwo (k r : ℕ) (hvr : v k ∈ e r) (hne : e r ≠ e k)
      {δ : Set (E 3)} (hδQ : (facePolytope P hA).IsFace δ)
      (hdδ : faceDim δ = 1) (hvδ : v k ∈ δ) :
      δ = e r ∨ δ = e k := by
    have hδP : P.IsFace δ := isFace_of_facePolytope P hA hδQ
    have hδA : δ ⊆ A := by
      have hsub := face_subset_toSet (facePolytope P hA) hδQ
      rwa [facePolytope_toSet P hA] at hsub
    exact spigoli_della_faccetta P hA hdA
      (he r).1 (he r).2.1 hvr
      (he k).1 (he k).2.1 (hv_in_e k)
      (he r).2.2.1 (he k).2.2.1 hne
      hδP hdδ hvδ hδA
  have hvicino (k : ℕ) (hk : k < m) {z : E 3}
      (hzQ : z ∈ (facePolytope P hA).vertices) (hkz : v k ≠ z)
      {δ : Set (E 3)} (hδQ : (facePolytope P hA).IsFace δ)
      (hdδ : faceDim δ = 1) (hkδ : v k ∈ δ) (hzδ : z ∈ δ) :
      ∃ j : ℕ, j < m ∧ z = v j := by
    by_cases hk0 : k = 0
    · subst k
      have hrm : m - 1 + 1 = m := by omega
      have hvprev : v 0 ∈ e (m - 1) := by
        rw [(he (m - 1)).2.2.2]
        rw [hrm, hvm]
        exact right_mem_segment ℝ _ _
      have hprev_ne : e (m - 1) ≠ e 0 := by
        have hn : e (m - 1 + 1) ≠ e (m - 1) := by
          simpa [e] using C.spigolo_nuovo (m - 1)
        rw [hrm, hem] at hn
        exact hn.symm
      rcases htwo 0 (m - 1) hvprev hprev_ne hδQ hdδ hkδ with hδ | hδ
      · rcases hends (m - 1) hzQ (hδ ▸ hzδ) with hz | hz
        · exact ⟨m - 1, by omega, hz⟩
        · exfalso
          apply hkz
          rw [hz, hrm, hvm]
      · rcases hends 0 hzQ (hδ ▸ hzδ) with hz | hz
        · exact absurd hz.symm hkz
        · by_cases h1m : 1 < m
          · exact ⟨1, h1m, hz⟩
          · have hm1 : m = 1 := by omega
            refine ⟨0, C.m_pos, ?_⟩
            rw [hz, ← hm1]
            exact hvperiod 0
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hrk : k - 1 + 1 = k := by omega
      have hvprev : v k ∈ e (k - 1) := by
        rw [(he (k - 1)).2.2.2]
        rw [hrk]
        exact right_mem_segment ℝ _ _
      have hprev_ne : e (k - 1) ≠ e k := by
        have hn : e (k - 1 + 1) ≠ e (k - 1) := by
          simpa [e] using C.spigolo_nuovo (k - 1)
        rw [hrk] at hn
        exact hn.symm
      rcases htwo k (k - 1) hvprev hprev_ne hδQ hdδ hkδ with hδ | hδ
      · rcases hends (k - 1) hzQ (hδ ▸ hzδ) with hz | hz
        · exact ⟨k - 1, by omega, hz⟩
        · exfalso
          apply hkz
          rw [hrk] at hz
          exact hz.symm
      · rcases hends k hzQ (hδ ▸ hzδ) with hz | hz
        · exact absurd hz.symm hkz
        · by_cases hsucc : k + 1 < m
          · exact ⟨k + 1, hsucc, hz⟩
          · have hkm : k + 1 = m := by omega
            refine ⟨0, C.m_pos, ?_⟩
            rw [hz, hkm, hvm]
  intro z hzQ
  have hQdim : Module.finrank ℝ
      (vectorSpan ℝ (facePolytope P hA).toSet) = 2 := by
    rw [facePolytope_toSet P hA]
    exact hdA
  have hx₀Q : x₀ ∈ (facePolytope P hA).vertices := by
    show x₀ ∈ P.vertices.filter (· ∈ A)
    exact Finset.mem_filter.mpr (C.vertice 0)
  have hpath := poligono_connesso (facePolytope P hA) hQdim hx₀Q hzQ
  have horbit_path : ∀ {y : E 3},
      Relation.ReflTransGen
        (fun p q => q ∈ (facePolytope P hA).vertices ∧ p ≠ q ∧
          ∃ δ : Set (E 3), (facePolytope P hA).IsFace δ ∧
            faceDim δ = 1 ∧ p ∈ δ ∧ q ∈ δ)
        x₀ y → ∃ k : ℕ, k < m ∧ y = v k := by
    intro y hy
    induction hy with
    | refl => exact ⟨0, C.m_pos, by simp [v]⟩
    | tail hpath hstep ih =>
        rcases ih with ⟨k, hk, rfl⟩
        rcases hstep with ⟨hyV, hkz, δ, hδQ, hdδ, hkδ, hyδ⟩
        exact hvicino k hk hyV hkz hδQ hdδ hkδ hyδ
  have horbit : ∃ k : ℕ, k < m ∧ z = v k := horbit_path hpath
  simpa [v] using horbit

/-- Ogni faccetta bidimensionale di un politopo regolare è un poligono
regolare nel senso orbitale usato dal motore di classificazione. -/
theorem faccetta_regolare (P : ConvexPolytope 3) (hreg : P.IsRegular)
    {A : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2) :
    ∃ (p : ℕ) (ℓ : ℝ), P.asFinite.IsRegularFacet A p ℓ := by
  classical
  obtain ⟨x₀, hx₀Q⟩ := (facePolytope P hA).vertices_nonempty
  have hx₀V : x₀ ∈ P.vertices := (Finset.mem_filter.mp hx₀Q).1
  have hx₀A : x₀ ∈ A := (Finset.mem_filter.mp hx₀Q).2
  obtain ⟨σ, m, C⟩ := ciclo_poligono_esiste P hreg hA hdA hx₀V hx₀A
  have hcomplete := ciclo_poligono_orbita_completa P hA hdA C
  let orb : Fin m → E 3 := fun i => (⇑σ)^[(i : ℕ)] x₀
  have hvertici :
      ((facePolytope P hA).vertices : Set (E 3)) = Set.range orb := by
    ext z
    constructor
    · intro hz
      obtain ⟨k, hk, hzk⟩ := hcomplete z hz
      exact ⟨⟨k, hk⟩, hzk.symm⟩
    · rintro ⟨i, rfl⟩
      show (⇑σ)^[(i : ℕ)] x₀ ∈ P.vertices.filter (· ∈ A)
      exact Finset.mem_filter.mpr (C.vertice i)
  have hAhull : A = convexHull ℝ (Set.range orb) := by
    rw [face_eq_hull_vertices P hA]
    change convexHull ℝ ((facePolytope P hA).vertices : Set (E 3)) = _
    rw [hvertici]
  have hspan : vectorSpan ℝ A = vectorSpan ℝ (Set.range orb) := by
    rw [hAhull, ← direction_affineSpan, affineSpan_convexHull,
      direction_affineSpan]
  haveI : Nonempty (Fin m) := ⟨⟨0, C.m_pos⟩⟩
  have hdA' : Module.finrank ℝ (vectorSpan ℝ A) = 2 := hdA
  have horbDim : Module.finrank ℝ (vectorSpan ℝ (Set.range orb)) = 2 := by
    rw [← hspan]
    exact hdA'
  have hm3 : 3 ≤ m := by
    have hbound := finrank_vectorSpan_range_add_one_le ℝ orb
    rw [horbDim, Fintype.card_fin] at hbound
    exact hbound
  have horbInj : Function.Injective orb := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact (C.distinti i j hlt j.isLt) hij
    · exact (C.distinti j i hlt i.isLt) hij.symm
  have hσne : σ x₀ ≠ x₀ := by
    simpa using C.passo_nuovo 0
  have hℓpos : 0 < dist x₀ (σ x₀) := dist_pos.mpr hσne.symm
  refine ⟨m, dist x₀ (σ x₀), ?_⟩
  refine ⟨(asFinite_isFacet_iff P A).2 ⟨hA, hdA⟩, hℓpos, hm3, ?_⟩
  refine ⟨σ, x₀, hx₀A, C.fissa, ?_, C.ritorno, hAhull, rfl⟩
  exact horbInj

end LeanEval.Geometry.PlatonicClassification
