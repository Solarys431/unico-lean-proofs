import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.VerticiEsposti
import UnicoProofs.Platonici.SottoPolitopo
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.Interpolazione
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.BandieraCompagna
import UnicoProofs.Platonici.Diamante
import UnicoProofs.Platonici.Diamante2D
import UnicoProofs.Platonici.SecondoSpigolo
import UnicoProofs.Platonici.SecondaFaccetta
import UnicoProofs.Platonici.BandieraVertice
import UnicoProofs.Platonici.ConoVertice
import UnicoProofs.Platonici.PassoFan
import UnicoProofs.Platonici.Immagini
import UnicoProofs.Platonici.OrbitaFan
import UnicoProofs.Platonici.PoligonoConnesso
import UnicoProofs.Platonici.Liberta

/-!
FASE 3A, F9b — IL CICLO DEL POLIGONO (18 lug 2026).

L'analogo 2D del ciclo del fan: in un politopo regolare, per una faccetta A
e un suo vertice x₀, il trasportatore σ della bandiera (x₀, e₀, A) sulla
bandiera (w, eS, A) — dove w è l'altro estremo di e₀ ed eS il secondo spigolo
di A in w — fissa A insiemisticamente e fa camminare x₀ lungo i vertici del
poligono. Il ciclo si chiude al minimo m > 0; le prime m tappe sono distinte;
ogni spigolo-immagine E_k è il segmento fra v_k e v_{k+1}; e l'orbita copre
TUTTI i vertici di A (chiusura per vicini + connettività del poligono, con
la periodicità che copre il predecessore di v₀ senza inversi).
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Il verbale del ciclo del poligono. -/
structure CicloPoligono (P : ConvexPolytope 3) (A : Set (E 3)) (x₀ : E 3)
    (σ : Isom 3) (m : ℕ) : Prop where
  simmetria : P.isSymmetry σ
  fissa : (⇑σ) '' A = A
  vertice : ∀ k : ℕ, (⇑σ)^[k] x₀ ∈ P.vertices ∧ (⇑σ)^[k] x₀ ∈ A
  passo_nuovo : ∀ k : ℕ, (⇑σ)^[k+1] x₀ ≠ (⇑σ)^[k] x₀
  spigolo : ∀ k : ℕ, P.IsFace ((⇑σ)^[k] '' (segment ℝ x₀ (σ x₀))) ∧
    faceDim ((⇑σ)^[k] '' (segment ℝ x₀ (σ x₀))) = 1 ∧
    (⇑σ)^[k] '' (segment ℝ x₀ (σ x₀)) ⊆ A ∧
    (⇑σ)^[k] '' (segment ℝ x₀ (σ x₀)) =
      segment ℝ ((⇑σ)^[k] x₀) ((⇑σ)^[k+1] x₀)
  spigolo_nuovo : ∀ k : ℕ,
    (⇑σ)^[k+1] '' (segment ℝ x₀ (σ x₀)) ≠ (⇑σ)^[k] '' (segment ℝ x₀ (σ x₀))
  m_pos : 0 < m
  ritorno : (⇑σ)^[m] x₀ = x₀
  distinti : ∀ i j : ℕ, i < j → j < m → (⇑σ)^[i] x₀ ≠ (⇑σ)^[j] x₀

/-- **IL CICLO DEL POLIGONO ESISTE** in ogni politopo regolare. -/
theorem ciclo_poligono_esiste (P : ConvexPolytope 3) (hreg : P.IsRegular)
    {A : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2)
    {x₀ : E 3} (hx₀V : x₀ ∈ P.vertices) (hx₀A : x₀ ∈ A) :
    ∃ (σ : Isom 3) (m : ℕ), CicloPoligono P A x₀ σ m := by
  classical
  have hfull : P.IsFullDim := hreg.1
  -- il poligono della faccetta
  have hQdim : Module.finrank ℝ
      (vectorSpan ℝ (facePolytope P hA).toSet) = 2 := by
    rw [facePolytope_toSet P hA]
    exact hdA
  have hx₀Q : x₀ ∈ (facePolytope P hA).vertices := by
    show x₀ ∈ P.vertices.filter (· ∈ A)
    exact Finset.mem_filter.mpr ⟨hx₀V, hx₀A⟩
  -- il primo spigolo di A in x₀
  have hx₀face : (facePolytope P hA).IsFace ({x₀} : Set (E 3)) :=
    vertex_isFace (facePolytope P hA) hx₀Q
  have hgap : faceDim ({x₀} : Set (E 3)) + 2 ≤
      Module.finrank ℝ (vectorSpan ℝ (facePolytope P hA).toSet) := by
    rw [faceDim_singleton, hQdim]
  obtain ⟨e₀Q, he₀Q, hxe₀, he₀ne⟩ :=
    interpolazione (facePolytope P hA) hx₀face hgap
  have hde₀ : faceDim e₀Q = 1 := by
    have h1 := faceDim_lt_of_ssubset (facePolytope P hA) hx₀face he₀Q hxe₀
    rw [faceDim_singleton] at h1
    have hss : e₀Q ⊂ (facePolytope P hA).toSet :=
      ⟨face_subset_toSet (facePolytope P hA) he₀Q, fun hsup => he₀ne
        (Set.Subset.antisymm
          (face_subset_toSet (facePolytope P hA) he₀Q) hsup)⟩
    have h2 := faceDim_lt_of_ssubset (facePolytope P hA) he₀Q
      (toSet_isFace (facePolytope P hA)) hss
    have h3 : faceDim (facePolytope P hA).toSet = 2 := hQdim
    omega
  have hx₀e₀ : x₀ ∈ e₀Q := hxe₀.subset rfl
  have he₀P : P.IsFace e₀Q := isFace_of_facePolytope P hA he₀Q
  have he₀A : e₀Q ⊆ A := by
    have h1 := face_subset_toSet (facePolytope P hA) he₀Q
    rwa [facePolytope_toSet P hA] at h1
  -- l'altro estremo w
  obtain ⟨w, hwV, hwe₀, hwx₀, hsege₀⟩ :=
    spigolo_segmento P he₀P hde₀ hx₀V hx₀e₀
  have hwA : w ∈ A := he₀A hwe₀
  have hwQ : w ∈ (facePolytope P hA).vertices := by
    show w ∈ P.vertices.filter (· ∈ A)
    exact Finset.mem_filter.mpr ⟨hwV, hwA⟩
  -- il secondo spigolo in w
  have hwe₀Q : w ∈ e₀Q := hwe₀
  obtain ⟨eSQ, heSQ, hdeS, hweS, heSne⟩ := secondo_spigolo (facePolytope P hA)
    hQdim hwQ he₀Q hde₀ hwe₀Q
  have heSP : P.IsFace eSQ := isFace_of_facePolytope P hA heSQ
  have heSA : eSQ ⊆ A := by
    have h1 := face_subset_toSet (facePolytope P hA) heSQ
    rwa [facePolytope_toSet P hA] at h1
  -- le due bandiere del passo del poligono
  obtain ⟨FA, hFA0, hFA1, hFA2⟩ := bandiera_di_pezzi P
    (vertex_isFace P hx₀V) he₀P hde₀ hx₀e₀ hA hdA he₀A
  obtain ⟨GA, hGA0, hGA1, hGA2⟩ := bandiera_di_pezzi P
    (vertex_isFace P hwV) heSP hdeS hweS hA hdA heSA
  obtain ⟨σ, hσP, hσflag⟩ := hreg.2 FA GA
  -- i trasporti fondamentali
  have hσx₀ : σ x₀ = w := by
    have h1 : σ x₀ ∈ (σ : E 3 → E 3) '' FA.face 0 :=
      ⟨x₀, by rw [hFA0]; rfl, rfl⟩
    rw [hσflag 0, hGA0] at h1
    exact h1
  have hσe₀ : (σ : E 3 → E 3) '' e₀Q = eSQ := by
    have h1 := hσflag 1
    rw [hFA1, hGA1] at h1
    exact h1
  have hσA : (σ : E 3 → E 3) '' A = A := by
    have h1 := hσflag 2
    rw [hFA2, hGA2] at h1
    exact h1
  refine ⟨σ, ?_⟩
  have hsucc : ∀ (k : ℕ) (X : Set (E 3)),
      (⇑σ)^[k+1] '' X = (⇑σ)^[k] '' ((⇑σ) '' X) := by
    intro k X
    rw [Function.iterate_succ]
    exact Set.image_comp _ _ _
  have hsuccpt : ∀ (k : ℕ) (x : E 3),
      (⇑σ)^[k+1] x = (⇑σ)^[k] (σ x) := by
    intro k x
    rw [Function.iterate_succ]
    rfl
  have hinj : ∀ k : ℕ, Function.Injective ((⇑σ)^[k]) :=
    fun k => Function.Injective.iterate σ.injective k
  -- A è fissa a ogni iterata
  have hAfix : ∀ k : ℕ, (⇑σ)^[k] '' A = A := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
        rw [hsucc n A, hσA]
        exact ih
  -- i vertici restano vertici e dentro A
  have hvert : ∀ k : ℕ, (⇑σ)^[k] x₀ ∈ P.vertices ∧ (⇑σ)^[k] x₀ ∈ A := by
    intro k
    induction k with
    | zero => exact ⟨hx₀V, hx₀A⟩
    | succ n ih =>
        constructor
        · have h1 : σ ((⇑σ)^[n] x₀) ∈ (σ : E 3 → E 3) ''
              (P.vertices : Set (E 3)) := ⟨_, Finset.mem_coe.mpr ih.1, rfl⟩
          rw [simmetria_immagine_vertici P hσP] at h1
          rw [Function.iterate_succ_apply']
          exact Finset.mem_coe.mp h1
        · have h1 : σ ((⇑σ)^[n] x₀) ∈ (σ : E 3 → E 3) '' A := ⟨_, ih.2, rfl⟩
          rw [hσA] at h1
          rw [Function.iterate_succ_apply']
          exact h1
  -- e₀ come segmento e le sue iterate
  have he₀seg : e₀Q = segment ℝ x₀ (σ x₀) := by
    rw [hσx₀]
    exact hsege₀
  have hspig : ∀ k : ℕ, P.IsFace ((⇑σ)^[k] '' (segment ℝ x₀ (σ x₀))) ∧
      faceDim ((⇑σ)^[k] '' (segment ℝ x₀ (σ x₀))) = 1 ∧
      (⇑σ)^[k] '' (segment ℝ x₀ (σ x₀)) ⊆ A ∧
      (⇑σ)^[k] '' (segment ℝ x₀ (σ x₀)) =
        segment ℝ ((⇑σ)^[k] x₀) ((⇑σ)^[k+1] x₀) := by
    intro k
    have hiter : ∀ j : ℕ, ∀ {X : Set (E 3)}, P.IsFace X →
        P.IsFace ((⇑σ)^[j] '' X) ∧
        faceDim ((⇑σ)^[j] '' X) = faceDim X := by
      intro j
      induction j with
      | zero =>
          intro X hX
          constructor
          · simpa using hX
          · simp
      | succ n ih =>
          intro X hX
          constructor
          · rw [hsucc n X]
            exact (ih (isFace_image_isom σ hσP hX)).1
          · rw [hsucc n X]
            rw [(ih (isFace_image_isom σ hσP hX)).2, faceDim_image_isom]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← he₀seg]
      exact (hiter k he₀P).1
    · rw [← he₀seg]
      rw [(hiter k he₀P).2]
      exact hde₀
    · rw [← he₀seg]
      have h1 : (⇑σ)^[k] '' e₀Q ⊆ (⇑σ)^[k] '' A := Set.image_mono he₀A
      rwa [hAfix k] at h1
    · -- l'immagine del segmento è il segmento delle immagini
      have hco : (⇑σ.toAffineEquiv.toAffineMap : E 3 → E 3) = ⇑σ := by
        ext x
        simp
      have hσseg : ∀ a b : E 3,
          (⇑σ) '' segment ℝ a b = segment ℝ (σ a) (σ b) := by
        intro a b
        have h2 := image_segment ℝ σ.toAffineEquiv.toAffineMap a b
        rw [hco] at h2
        exact h2
      have h1 : ∀ j : ℕ, (⇑σ)^[j] '' segment ℝ x₀ (σ x₀) =
          segment ℝ ((⇑σ)^[j] x₀) ((⇑σ)^[j] (σ x₀)) := by
        intro j
        induction j with
        | zero => simp
        | succ n ih =>
            have hstep : (⇑σ)^[n+1] '' segment ℝ x₀ (σ x₀) =
                (⇑σ) '' ((⇑σ)^[n] '' segment ℝ x₀ (σ x₀)) := by
              rw [Function.iterate_succ']
              exact Set.image_comp _ _ _
            rw [hstep, ih, hσseg]
            rw [← Function.iterate_succ_apply' (⇑σ) n x₀,
              ← Function.iterate_succ_apply' (⇑σ) n (σ x₀)]
      rw [h1 k, hsuccpt k x₀]
  -- il passo è sempre nuovo
  have hpnuovo : ∀ k : ℕ, (⇑σ)^[k+1] x₀ ≠ (⇑σ)^[k] x₀ := by
    intro k h
    rw [hsuccpt k x₀] at h
    have h2 : σ x₀ = x₀ := hinj k h
    rw [hσx₀] at h2
    exact hwx₀ h2
  have hsnuovo : ∀ k : ℕ,
      (⇑σ)^[k+1] '' (segment ℝ x₀ (σ x₀)) ≠
      (⇑σ)^[k] '' (segment ℝ x₀ (σ x₀)) := by
    intro k h
    rw [hsucc k _] at h
    have h2 : (⇑σ) '' segment ℝ x₀ (σ x₀) = segment ℝ x₀ (σ x₀) :=
      Set.image_injective.mpr (hinj k) h
    rw [← he₀seg, hσe₀] at h2
    exact heSne h2
  -- il pigeonhole sui vertici del poligono
  have hoQ : ∀ k : ℕ, (⇑σ)^[k] x₀ ∈ (facePolytope P hA).vertices := by
    intro k
    show (⇑σ)^[k] x₀ ∈ P.vertices.filter (· ∈ A)
    exact Finset.mem_filter.mpr ⟨(hvert k).1, (hvert k).2⟩
  have hshiftpt : ∀ i d : ℕ, (⇑σ)^[i + d] x₀ = (⇑σ)^[i] ((⇑σ)^[d] x₀) := by
    intro i d
    rw [Function.iterate_add]
    rfl
  have hpigeon : ∃ d : ℕ, 0 < d ∧ (⇑σ)^[d] x₀ = x₀ := by
    have hcard : (facePolytope P hA).vertices.card <
        (Finset.range ((facePolytope P hA).vertices.card + 1)).card := by
      rw [Finset.card_range]
      omega
    obtain ⟨i, hi, j, hj, hij, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
        (fun k _ => hoQ k)
    rcases Nat.lt_or_ge i j with hlt | hge
    · refine ⟨j - i, by omega, ?_⟩
      have h1 := hshiftpt i (j - i)
      have h2 : i + (j - i) = j := by omega
      rw [h2] at h1
      apply hinj i
      rw [← h1]
      exact heq.symm
    · have hlt' : j < i := by omega
      refine ⟨i - j, by omega, ?_⟩
      have h1 := hshiftpt j (i - j)
      have h2 : j + (i - j) = i := by omega
      rw [h2] at h1
      apply hinj j
      rw [← h1]
      exact heq
  set m := Nat.find hpigeon with hmdef
  obtain ⟨hmpos', hmret'⟩ := Nat.find_spec hpigeon
  have hmpos : 0 < m := hmpos'
  have hmret : (⇑σ)^[m] x₀ = x₀ := hmret'
  have hmmin : ∀ d : ℕ, 0 < d → d < m → (⇑σ)^[d] x₀ ≠ x₀ := by
    intro d hd hdm hcon
    exact Nat.find_min hpigeon hdm ⟨hd, hcon⟩
  have hdist : ∀ i j : ℕ, i < j → j < m → (⇑σ)^[i] x₀ ≠ (⇑σ)^[j] x₀ := by
    intro i j hij hjm hcon
    have h1 := hshiftpt i (j - i)
    have h2 : i + (j - i) = j := by omega
    rw [h2] at h1
    have h3 : (⇑σ)^[j - i] x₀ = x₀ := by
      apply hinj i
      rw [← h1]
      exact hcon.symm
    exact hmmin (j - i) (by omega) (by omega) h3
  exact ⟨m, {
    simmetria := hσP
    fissa := hσA
    vertice := hvert
    passo_nuovo := hpnuovo
    spigolo := hspig
    spigolo_nuovo := hsnuovo
    m_pos := hmpos
    ritorno := hmret
    distinti := hdist
  }⟩

end LeanEval.Geometry.PlatonicClassification
