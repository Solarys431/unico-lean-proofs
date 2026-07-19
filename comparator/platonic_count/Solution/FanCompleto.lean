import Mathlib
import Challenge
import Solution.VerticiEsposti
import Solution.SottoPolitopo
import Solution.DimStretta
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
import Solution.ScaricoSpigolo
import Solution.ConnessioneVentaglio
import Solution.Liberta

/-!
FASE 3A, F5c — LA COMPLETEZZA DELL'ORBITA DEL FAN (18 lug 2026).

Con la connettività del ventaglio (fascicolo 17 di sol) e il ciclo del fan,
l'orbita σ-iterata della faccetta di partenza copre TUTTE le faccette per v:
l'orbita è periodica e chiusa per vicinato (gli spigoli di A_k in v sono
esattamente ε_k ed ε_{k+1}; le faccette per ciascuno spigolo sono esattamente
le due consecutive dell'orbita, con il ritorno dello spigolo a coprire il
predecessore di A_0), e l'induzione sul cammino di ReflTransGen fa il resto.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **LA COMPLETEZZA DELL'ORBITA**: ogni faccetta per v è una delle prime m
iterate del ciclo del fan. -/
theorem fan_completo (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {v : E 3} (hv : v ∈ P.vertices) {F : P.Flag} (hF0 : F.face 0 = {v})
    {σ : Isom 3} {m : ℕ} (hC : CicloFan P v F σ m) :
    ∀ B : Set (E 3), P.IsFace B → faceDim B = 2 → v ∈ B →
      ∃ k : ℕ, k < m ∧ B = (⇑σ)^[k] '' F.face 2 := by
  classical
  -- periodicità dell'orbita
  have hshift : ∀ j : ℕ, ∀ X : Set (E 3),
      (⇑σ)^[j + m] '' X = (⇑σ)^[j] '' ((⇑σ)^[m] '' X) := by
    intro j X
    rw [Function.iterate_add]
    exact Set.image_comp _ _ _
  have hper : ∀ j : ℕ, (⇑σ)^[j + m] '' F.face 2 = (⇑σ)^[j] '' F.face 2 := by
    intro j
    rw [hshift j (F.face 2), hC.ritorno]
  have hperε : ∀ j : ℕ, (⇑σ)^[j + m] '' F.face 1 = (⇑σ)^[j] '' F.face 1 := by
    intro j
    rw [hshift j (F.face 1), hC.ritorno_spigolo]
  -- normalizzazione dell'indice
  have hnorm : ∀ k : ℕ, ∃ k' : ℕ, k' < m ∧
      (⇑σ)^[k] '' F.face 2 = (⇑σ)^[k'] '' F.face 2 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
        rcases Nat.lt_or_ge k m with hk | hk
        · exact ⟨k, hk, rfl⟩
        · have hk' : k - m < k := by
            have := hC.m_pos
            omega
          obtain ⟨k', hk'm, hk'eq⟩ := ih (k - m) hk'
          refine ⟨k', hk'm, ?_⟩
          have h1 : k - m + m = k := by omega
          rw [← hk'eq, ← hper (k - m), h1]
  -- il punto secondo di uno spigolo dell'orbita
  have hsp := hC.spigolo
  -- vicinato: una faccetta che condivide uno spigolo con A_k sta nell'orbita
  have hvicini : ∀ k : ℕ, ∀ B : Set (E 3),
      P.IsFace B → faceDim B = 2 → v ∈ B →
      SpigoloComune P v ((⇑σ)^[k] '' F.face 2) B →
      ∃ j : ℕ, B = (⇑σ)^[j] '' F.face 2 := by
    intro k B hB hdB hvB ⟨δ, hδ, hdδ, hvδ, hδA, hδB⟩
    -- δ è uno dei due spigoli di A_k
    have hAk := hC.faccetta k
    have hεk := hC.spigolo k
    have hεk1 := hC.spigolo (k + 1)
    have halt := spigoli_della_faccetta P hAk.1 hAk.2.1
      hεk.1 hεk.2.1 hεk.2.2 hεk1.1 hεk1.2.1 hεk1.2.2
      (hC.spigolo_dentro k) (hC.spigolo_avanti k)
      (Ne.symm (hC.spigolo_nuovo k)) hδ hdδ hvδ hδA
    -- il tetto per le faccette di uno spigolo dell'orbita
    have htetto : ∀ j : ℕ, ∀ C₁ C₂ : Set (E 3),
        P.IsFace C₁ → faceDim C₁ = 2 → v ∈ C₁ →
        P.IsFace C₂ → faceDim C₂ = 2 → v ∈ C₂ → C₁ ≠ C₂ →
        (⇑σ)^[j+1] '' F.face 1 ⊆ C₁ → (⇑σ)^[j+1] '' F.face 1 ⊆ C₂ →
        (⇑σ)^[j+1] '' F.face 1 ⊆ B → B = C₁ ∨ B = C₂ := by
      intro j C₁ C₂ hC₁ hdC₁ hvC₁ hC₂ hdC₂ hvC₂ hne hsub₁ hsub₂ hsubB
      have hεj := hC.spigolo (j + 1)
      obtain ⟨x, hxε, hxv⟩ := faccia_ha_secondo_punto hεj.2.1 (v := v)
      exact spigolo_in_due_faccette P v hC₁ hdC₁ hC₂ hdC₂ hB hdB hne
        hvC₁ hvC₂ hvB ⟨hsub₁ hxε, hsub₂ hxε⟩ hxv (hsubB hxε)
    rcases halt with hδε | hδε
    · -- δ = ε_k: le faccette sono A_{k−1-modulare} e A_k
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · -- k = 0: il predecessore è A_{m−1} via il ritorno dello spigolo
        subst hk0
        have hm1 : m - 1 + 1 = m := by
          have := hC.m_pos
          omega
        have hsubm : (⇑σ)^[m - 1 + 1] '' F.face 1 ⊆
            (⇑σ)^[m - 1] '' F.face 2 := hC.spigolo_avanti (m - 1)
        have hε0m : (⇑σ)^[m] '' F.face 1 = F.face 1 := hC.ritorno_spigolo
        have hAm1 := hC.faccetta (m - 1)
        have hA0 := hC.faccetta 0
        have hne : (⇑σ)^[m - 1] '' F.face 2 ≠ (⇑σ)^[0] '' F.face 2 := by
          rcases Nat.lt_or_ge 1 m with hm2 | hm2
          · exact fun h => hC.distinte 0 (m - 1) (by omega) (by omega) h.symm
          · have hm1' : m = 1 := by
              have := hC.m_pos
              omega
            have h1 := hC.faccetta_nuova 0
            intro _
            apply h1
            have h2 : (⇑σ)^[0 + 1] '' F.face 2 = F.face 2 := by
              have h4 : (0:ℕ) + 1 = m := by omega
              rw [h4]
              exact hC.ritorno
            rw [h2]
            simp
        have hδ' : δ = (⇑σ)^[m - 1 + 1] '' F.face 1 := by
          rw [hm1, hε0m]
          simpa using hδε
        have hres := htetto (m - 1) _ _ hAm1.1 hAm1.2.1 hAm1.2.2
          hA0.1 hA0.2.1 hA0.2.2 hne
          hsubm (by rw [hm1, hε0m]; simpa using hC.spigolo_dentro 0)
          (by rw [← hδ']; exact hδB)
        rcases hres with h | h
        · exact ⟨m - 1, h⟩
        · exact ⟨0, h⟩
      · -- k ≥ 1: le faccette per ε_k sono A_{k−1} e A_k
        have hk1 : k - 1 + 1 = k := by omega
        have hsub1 : (⇑σ)^[k - 1 + 1] '' F.face 1 ⊆
            (⇑σ)^[k - 1] '' F.face 2 := hC.spigolo_avanti (k - 1)
        have hAk1 := hC.faccetta (k - 1)
        have hne : (⇑σ)^[k - 1] '' F.face 2 ≠ (⇑σ)^[k] '' F.face 2 := by
          intro h
          have h1 := hC.faccetta_nuova (k - 1)
          rw [hk1] at h1
          exact h1 h.symm
        have hres := htetto (k - 1) _ _ hAk1.1 hAk1.2.1 hAk1.2.2
          hAk.1 hAk.2.1 hAk.2.2 hne hsub1
          (by rw [hk1]; exact hC.spigolo_dentro k)
          (by rw [hk1, ← hδε]; exact hδB)
        rcases hres with h | h
        · exact ⟨k - 1, h⟩
        · exact ⟨k, h⟩
    · -- δ = ε_{k+1}: le faccette sono A_k e A_{k+1}
      have hAk1 := hC.faccetta (k + 1)
      have hne : (⇑σ)^[k] '' F.face 2 ≠ (⇑σ)^[k+1] '' F.face 2 :=
        fun h => hC.faccetta_nuova k h.symm
      have hres := htetto k _ _ hAk.1 hAk.2.1 hAk.2.2
        hAk1.1 hAk1.2.1 hAk1.2.2 hne
        (hC.spigolo_avanti k) (hC.spigolo_dentro (k + 1))
        (by rw [← hδε]; exact hδB)
      rcases hres with h | h
      · exact ⟨k, h⟩
      · exact ⟨k + 1, h⟩
  -- l'induzione sul cammino del ventaglio
  intro B hB hdB hvB
  have hA0 := hC.faccetta 0
  have hA0eq : (⇑σ)^[0] '' F.face 2 = F.face 2 := by simp
  have hcam := ventaglio_connesso P hfull hv
    (A := F.face 2) (F.isFace 2) (F.dim_eq 2)
    ((F.strict_mono 1 2 (by decide)).subset
      ((F.strict_mono 0 1 (by decide)).subset (hF0 ▸ rfl)))
    (B := B) hB hdB hvB
  -- l'induzione: ogni tappa del cammino è nell'orbita
  have hinv : ∀ X : Set (E 3),
      Relation.ReflTransGen
        (fun X Y => (P.IsFace Y ∧ faceDim Y = 2 ∧ v ∈ Y) ∧
          SpigoloComune P v X Y) (F.face 2) X →
      ∃ j : ℕ, X = (⇑σ)^[j] '' F.face 2 := by
    intro X hX
    induction hX with
    | refl => exact ⟨0, by simp⟩
    | tail hab hbc ih =>
        obtain ⟨j, hj⟩ := ih
        obtain ⟨⟨hcF, hcd, hcv⟩, hsc⟩ := hbc
        obtain ⟨jf, hjf⟩ := hvicini j _ hcF hcd hcv
          (by rw [← hj]; exact hsc)
        exact ⟨jf, hjf⟩
  obtain ⟨j, hj⟩ := hinv B hcam
  obtain ⟨k', hk'm, hk'eq⟩ := hnorm j
  exact ⟨k', hk'm, by rw [hj, hk'eq]⟩

end LeanEval.Geometry.PlatonicClassification
