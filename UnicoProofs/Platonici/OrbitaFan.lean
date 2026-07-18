import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.VerticiEsposti
import UnicoProofs.Platonici.SottoPolitopo
import UnicoProofs.Platonici.DimStretta
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
import UnicoProofs.Platonici.ScaricoSpigolo
import UnicoProofs.Platonici.FanVertice

/-!
FASE 3A, F5b — IL CICLO DELL'ORBITA DEL FAN (18 lug 2026).

Dato un politopo regolare, un vertice v e una bandiera F in v, il passo del
fan fornisce G e la flag-transitività un trasportatore σ con σ(v) = v.
Le iterate A_k := σ^[k] '' (faccetta di F) ed ε_k := σ^[k] '' (spigolo di F)
formano il camminamento deterministico del ventaglio: faccette e spigoli in
v, ε_{k+1} ⊆ A_k ∩ A_{k+1}, passi sempre nuovi; il ciclo si chiude al minimo
m > 0 con A_m = A_0, le prime m faccette sono a due a due distinte, e IL
RITORNO DELLA FACCETTA FORZA IL RITORNO DELLO SPIGOLO: ε_m è uno spigolo di
A_0, quindi ε_0 oppure ε_1 (tetto del diamante 2D); il ramo ε_1 muore su
minimalità e novità dei passi. Conclusioni impacchettate in `CicloFan`.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Il verbale del ciclo del fan: iterate, invarianti, chiusura. -/
structure CicloFan (P : ConvexPolytope 3) (v : E 3) (F : P.Flag)
    (σ : Isom 3) (m : ℕ) : Prop where
  simmetria : P.isSymmetry σ
  fisso : σ v = v
  faccetta : ∀ k : ℕ, P.IsFace ((⇑σ)^[k] '' F.face 2) ∧
    faceDim ((⇑σ)^[k] '' F.face 2) = 2 ∧ v ∈ (⇑σ)^[k] '' F.face 2
  spigolo : ∀ k : ℕ, P.IsFace ((⇑σ)^[k] '' F.face 1) ∧
    faceDim ((⇑σ)^[k] '' F.face 1) = 1 ∧ v ∈ (⇑σ)^[k] '' F.face 1
  spigolo_dentro : ∀ k : ℕ, (⇑σ)^[k] '' F.face 1 ⊆ (⇑σ)^[k] '' F.face 2
  spigolo_avanti : ∀ k : ℕ, (⇑σ)^[k+1] '' F.face 1 ⊆ (⇑σ)^[k] '' F.face 2
  spigolo_nuovo : ∀ k : ℕ, (⇑σ)^[k+1] '' F.face 1 ≠ (⇑σ)^[k] '' F.face 1
  faccetta_nuova : ∀ k : ℕ, (⇑σ)^[k+1] '' F.face 2 ≠ (⇑σ)^[k] '' F.face 2
  m_pos : 0 < m
  ritorno : (⇑σ)^[m] '' F.face 2 = F.face 2
  ritorno_spigolo : (⇑σ)^[m] '' F.face 1 = F.face 1
  distinte : ∀ i j : ℕ, i < j → j < m →
    (⇑σ)^[i] '' F.face 2 ≠ (⇑σ)^[j] '' F.face 2
  trasporto : ∃ G L R : P.Flag, G.face 0 = {v} ∧ L.face 0 = {v} ∧
    L.face 2 = F.face 2 ∧ R.face 2 = G.face 2 ∧ L.face 1 = R.face 1 ∧
    ∀ k : Fin 3, (⇑σ) '' F.face k = G.face k

/-- Il tetto del diamante 2D per gli spigoli di una faccetta in v. -/
theorem spigoli_della_faccetta (P : ConvexPolytope 3)
    {A : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2)
    {v : E 3}
    {e₁ e₂ : Set (E 3)}
    (he₁ : P.IsFace e₁) (hde₁ : faceDim e₁ = 1) (hv₁ : v ∈ e₁)
    (he₂ : P.IsFace e₂) (hde₂ : faceDim e₂ = 1) (hv₂ : v ∈ e₂)
    (hsub₁ : e₁ ⊆ A) (hsub₂ : e₂ ⊆ A) (hne : e₁ ≠ e₂)
    {δ : Set (E 3)} (hδ : P.IsFace δ) (hdδ : faceDim δ = 1) (hvδ : v ∈ δ)
    (hδA : δ ⊆ A) : δ = e₁ ∨ δ = e₂ := by
  classical
  by_contra hcon
  push_neg at hcon
  have hQ1 : (facePolytope P hA).IsFace e₁ :=
    facePolytope_isFace_of P hA he₁ hsub₁
  have hQ2 : (facePolytope P hA).IsFace e₂ :=
    facePolytope_isFace_of P hA he₂ hsub₂
  have hQδ : (facePolytope P hA).IsFace δ :=
    facePolytope_isFace_of P hA hδ hδA
  have hQdim : Module.finrank ℝ
      (vectorSpan ℝ (facePolytope P hA).toSet) = 2 := by
    rw [facePolytope_toSet P hA]
    exact hdA
  exact diamante_poligono (facePolytope P hA) hQdim hQ1 hde₁ hQ2 hde₂ hQδ hdδ
    hne (fun h => hcon.1 h.symm) (fun h => hcon.2 h.symm) hv₁ hv₂ hvδ

/-- **IL CICLO DEL FAN**: in un politopo regolare, per ogni bandiera in v
il trasportatore del passo chiude un ciclo di faccette distinte con ritorno
simultaneo dello spigolo. -/
theorem ciclo_fan_esiste (P : ConvexPolytope 3) (hreg : P.IsRegular)
    {v : E 3} (hv : v ∈ P.vertices)
    (F : P.Flag) (hF0 : F.face 0 = {v}) :
    ∃ (σ : Isom 3) (m : ℕ), CicloFan P v F σ m := by
  classical
  have hfull : P.IsFullDim := hreg.1
  obtain ⟨G, L, R, hG0, hL0, hL2, hR2, hLR, hGne, hLne, hGL⟩ :=
    passo_del_fan P hfull hv F hF0
  obtain ⟨σ, hσP, hσflag⟩ := hreg.2 F G
  have hσv : σ v = v := by
    have h1 : σ v ∈ (σ : E 3 → E 3) '' F.face 0 :=
      ⟨v, by rw [hF0]; rfl, rfl⟩
    rw [hσflag 0, hG0] at h1
    exact h1
  have hσvit : ∀ k : ℕ, (⇑σ)^[k] v = v := fun k =>
    (show Function.IsFixedPt (⇑σ) v from hσv).iterate k
  have hv1 : v ∈ F.face 1 := (F.strict_mono 0 1 (by decide)).subset
    (hF0 ▸ rfl)
  have hv2 : v ∈ F.face 2 := (F.strict_mono 1 2 (by decide)).subset hv1
  have hδ1 : (σ : E 3 → E 3) '' F.face 1 = G.face 1 := hσflag 1
  have hδ2 : (σ : E 3 → E 3) '' F.face 2 = G.face 2 := hσflag 2
  have hGdentro : G.face 1 ⊆ F.face 2 := by
    rw [hGL]
    have h1 : L.face 1 ⊆ L.face 2 := (L.strict_mono 1 2 (by decide)).subset
    rwa [hL2] at h1
  have hG1ne : G.face 1 ≠ F.face 1 := by
    rw [hGL]
    exact hLne
  -- la successione delle immagini: passo in avanti
  have hsucc : ∀ (k : ℕ) (X : Set (E 3)),
      (⇑σ)^[k+1] '' X = (⇑σ)^[k] '' ((⇑σ) '' X) := by
    intro k X
    rw [Function.iterate_succ]
    exact Set.image_comp _ _ _
  have hinj : ∀ k : ℕ, Function.Injective ((⇑σ)^[k]) :=
    fun k => Function.Injective.iterate σ.injective k
  -- immagini iterate: faccia e dimensione si conservano
  have hiter : ∀ k : ℕ, ∀ {X : Set (E 3)}, P.IsFace X →
      P.IsFace ((⇑σ)^[k] '' X) ∧
      faceDim ((⇑σ)^[k] '' X) = faceDim X := by
    intro k
    induction k with
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
  -- i campi invarianti
  have hfaccetta : ∀ k : ℕ, P.IsFace ((⇑σ)^[k] '' F.face 2) ∧
      faceDim ((⇑σ)^[k] '' F.face 2) = 2 ∧ v ∈ (⇑σ)^[k] '' F.face 2 := by
    intro k
    refine ⟨(hiter k (F.isFace 2)).1, ?_, ⟨v, hv2, hσvit k⟩⟩
    rw [(hiter k (F.isFace 2)).2]
    exact F.dim_eq 2
  have hspigolo : ∀ k : ℕ, P.IsFace ((⇑σ)^[k] '' F.face 1) ∧
      faceDim ((⇑σ)^[k] '' F.face 1) = 1 ∧ v ∈ (⇑σ)^[k] '' F.face 1 := by
    intro k
    refine ⟨(hiter k (F.isFace 1)).1, ?_, ⟨v, hv1, hσvit k⟩⟩
    rw [(hiter k (F.isFace 1)).2]
    exact F.dim_eq 1
  have hdentro : ∀ k : ℕ,
      (⇑σ)^[k] '' F.face 1 ⊆ (⇑σ)^[k] '' F.face 2 := fun k =>
    Set.image_mono (F.strict_mono 1 2 (by decide)).subset
  have havanti : ∀ k : ℕ,
      (⇑σ)^[k+1] '' F.face 1 ⊆ (⇑σ)^[k] '' F.face 2 := by
    intro k
    rw [hsucc k (F.face 1), hδ1]
    exact Set.image_mono hGdentro
  have hnuovo : ∀ k : ℕ,
      (⇑σ)^[k+1] '' F.face 1 ≠ (⇑σ)^[k] '' F.face 1 := by
    intro k h
    rw [hsucc k (F.face 1), hδ1] at h
    exact hG1ne (Set.image_injective.mpr (hinj k) h)
  have hfnuova : ∀ k : ℕ,
      (⇑σ)^[k+1] '' F.face 2 ≠ (⇑σ)^[k] '' F.face 2 := by
    intro k h
    rw [hsucc k (F.face 2), hδ2] at h
    exact hGne (Set.image_injective.mpr (hinj k) h)
  -- lo scorrimento: cancellare un prefisso di iterate
  have hshift : ∀ i d : ℕ,
      (⇑σ)^[i + d] '' F.face 2 = (⇑σ)^[i] '' ((⇑σ)^[d] '' F.face 2) := by
    intro i d
    rw [Function.iterate_add]
    exact Set.image_comp _ _ _
  -- il pigeonhole sul Finset delle faccette in v
  have hFVfin : {A : Set (E 3) | P.IsFace A ∧ faceDim A = 2 ∧
      v ∈ A}.Finite :=
    Set.Finite.subset (facce_finite P) (fun A hA => hA.1)
  set FV : Finset (Set (E 3)) := hFVfin.toFinset with hFV
  have hoFV : ∀ k : ℕ, (⇑σ)^[k] '' F.face 2 ∈ FV := by
    intro k
    rw [hFV, Set.Finite.mem_toFinset]
    exact hfaccetta k
  have hpigeon : ∃ d : ℕ, 0 < d ∧ (⇑σ)^[d] '' F.face 2 = F.face 2 := by
    have hcard : FV.card < (Finset.range (FV.card + 1)).card := by
      rw [Finset.card_range]
      omega
    obtain ⟨i, hi, j, hj, hij, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
        (fun k _ => hoFV k)
    rcases Nat.lt_or_ge i j with hlt | hge
    · refine ⟨j - i, by omega, ?_⟩
      have h1 : (⇑σ)^[i + (j - i)] '' F.face 2 =
          (⇑σ)^[i] '' ((⇑σ)^[j - i] '' F.face 2) := hshift i (j - i)
      have h2 : i + (j - i) = j := by omega
      rw [h2] at h1
      have h3 : (⇑σ)^[i] '' ((⇑σ)^[j - i] '' F.face 2) =
          (⇑σ)^[i] '' F.face 2 := by
        rw [← h1]
        exact heq.symm
      exact Set.image_injective.mpr (hinj i) h3
    · have hlt' : j < i := by omega
      refine ⟨i - j, by omega, ?_⟩
      have h1 : (⇑σ)^[j + (i - j)] '' F.face 2 =
          (⇑σ)^[j] '' ((⇑σ)^[i - j] '' F.face 2) := hshift j (i - j)
      have h2 : j + (i - j) = i := by omega
      rw [h2] at h1
      have h3 : (⇑σ)^[j] '' ((⇑σ)^[i - j] '' F.face 2) =
          (⇑σ)^[j] '' F.face 2 := by
        rw [← h1]
        exact heq
      exact Set.image_injective.mpr (hinj j) h3
  -- il minimo periodo
  set m := Nat.find hpigeon with hmdef
  obtain ⟨hmpos', hmret'⟩ := Nat.find_spec hpigeon
  have hmpos : 0 < m := hmpos'
  have hmret : (⇑σ)^[m] '' F.face 2 = F.face 2 := hmret'
  have hmmin : ∀ d : ℕ, 0 < d → d < m →
      (⇑σ)^[d] '' F.face 2 ≠ F.face 2 := by
    intro d hd hdm hcon
    exact Nat.find_min hpigeon hdm ⟨hd, hcon⟩
  -- le prime m faccette sono distinte
  have hdist : ∀ i j : ℕ, i < j → j < m →
      (⇑σ)^[i] '' F.face 2 ≠ (⇑σ)^[j] '' F.face 2 := by
    intro i j hij hjm hcon
    have h1 : (⇑σ)^[i + (j - i)] '' F.face 2 =
        (⇑σ)^[i] '' ((⇑σ)^[j - i] '' F.face 2) := hshift i (j - i)
    have h2 : i + (j - i) = j := by omega
    rw [h2] at h1
    have h3 : (⇑σ)^[i] '' ((⇑σ)^[j - i] '' F.face 2) =
        (⇑σ)^[i] '' F.face 2 := by
      rw [← h1]
      exact hcon.symm
    have h4 : (⇑σ)^[j - i] '' F.face 2 = F.face 2 :=
      Set.image_injective.mpr (hinj i) h3
    exact hmmin (j - i) (by omega) (by omega) h4
  -- IL RITORNO DELLO SPIGOLO
  have hritspig : (⇑σ)^[m] '' F.face 1 = F.face 1 := by
    -- ε_m è uno spigolo in v dentro A_0
    have hεm := hspigolo m
    have hεmA0 : (⇑σ)^[m] '' F.face 1 ⊆ F.face 2 := by
      have h1 := hdentro m
      rwa [hmret] at h1
    -- gli spigoli di A_0 in v sono ε_0 e ε_1
    have hε1 : P.IsFace ((⇑σ)^[1] '' F.face 1) ∧
        faceDim ((⇑σ)^[1] '' F.face 1) = 1 ∧
        v ∈ (⇑σ)^[1] '' F.face 1 := hspigolo 1
    have hε1A0 : (⇑σ)^[1] '' F.face 1 ⊆ F.face 2 := by
      have h1 := havanti 0
      simpa using h1
    have hε1ne : (⇑σ)^[1] '' F.face 1 ≠ F.face 1 := by
      have h1 := hnuovo 0
      simpa using h1
    have halt := spigoli_della_faccetta P (F.isFace 2) (F.dim_eq 2)
      (F.isFace 1) (F.dim_eq 1) hv1
      hε1.1 hε1.2.1 hε1.2.2 (F.strict_mono 1 2 (by decide)).subset hε1A0
      (Ne.symm hε1ne) hεm.1 hεm.2.1 hεm.2.2 hεmA0
    rcases halt with h | h
    · exact h
    · -- il ramo ε_m = ε_1: muore su minimalità e novità
      exfalso
      -- A_{m−1} contiene ε_m = ε_1; le faccette per ε_1 sono A_0 e A_1
      have hm1 : m - 1 + 1 = m := by omega
      have hεmAm1 : (⇑σ)^[m] '' F.face 1 ⊆ (⇑σ)^[m-1] '' F.face 2 := by
        have h1 := havanti (m - 1)
        rwa [hm1] at h1
      -- il punto secondo di ε_1
      obtain ⟨x, hxε, hxv⟩ := faccia_ha_secondo_punto
        (hε1.2.1) (v := v)
      have hxA0 : x ∈ F.face 2 := hε1A0 hxε
      have hxA1 : x ∈ (⇑σ)^[1] '' F.face 2 := by
        have h1 := hdentro 1
        exact h1 hxε
      have hxAm1 : x ∈ (⇑σ)^[m-1] '' F.face 2 := by
        apply hεmAm1
        rw [h]
        exact hxε
      -- A_1 ≠ A_0
      have hA1ne : (⇑σ)^[1] '' F.face 2 ≠ F.face 2 := by
        have h1 := hfnuova 0
        simpa using h1
      have hA1 := hfaccetta 1
      have hAm1 := hfaccetta (m - 1)
      -- il tetto: A_{m−1} = A_0 oppure A_{m−1} = A_1
      have hdue := spigolo_in_due_faccette P v
        (A := F.face 2) (F.isFace 2) (F.dim_eq 2)
        (B := (⇑σ)^[1] '' F.face 2) hA1.1 hA1.2.1
        (C := (⇑σ)^[m-1] '' F.face 2) hAm1.1 hAm1.2.1
        (Ne.symm hA1ne) hv2 hA1.2.2 hAm1.2.2
        (x := x) ⟨hxA0, hxA1⟩ hxv hxAm1
      rcases hdue with hcase | hcase
      · -- A_{m−1} = A_0
        rcases Nat.lt_or_ge 1 m with hm2 | hm2
        · exact hmmin (m - 1) (by omega) (by omega) hcase
        · -- m = 1: A_1 = A_0 contro la novità
          have hm1' : m = 1 := by omega
          rw [hm1'] at hmret
          exact hA1ne (by simpa using hmret)
      · -- A_{m−1} = A_1
        rcases Nat.lt_or_ge 2 m with hm3 | hm3
        · exact hdist 1 (m - 1) (by omega) (by omega) hcase.symm
        · rcases Nat.lt_or_ge 1 m with hm2 | hm2
          · -- m = 2: ε_2 = ε_1 contro la novità dello spigolo
            have hm2' : m = 1 + 1 := by omega
            rw [hm2'] at h
            exact hnuovo 1 h
          · -- m = 1: A_0 = A_1
            have hm1' : m = 1 := by omega
            rw [hm1'] at hcase
            exact hA1ne (by simpa using hcase.symm)
  refine ⟨σ, m, ?_⟩
  exact {
    simmetria := hσP
    fisso := hσv
    faccetta := hfaccetta
    spigolo := hspigolo
    spigolo_dentro := hdentro
    spigolo_avanti := havanti
    spigolo_nuovo := hnuovo
    faccetta_nuova := hfnuova
    m_pos := hmpos
    ritorno := hmret
    ritorno_spigolo := hritspig
    distinte := hdist
    trasporto := ⟨G, L, R, hG0, hL0, hL2, hR2, hLR, hσflag⟩
  }

end LeanEval.Geometry.PlatonicClassification
