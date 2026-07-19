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
import Solution.FanCompleto
import Solution.FanVertice
import Solution.Fondamenta

/-!
FASE 3A, F8-VERTICE — IL VERTICE CICLICO DEL REGOLARE (18 lug 2026).

Il gemello KG-3A2 si scarica: in un politopo regolare ogni vertice è
q-ciclico, con q = il periodo del ciclo del fan. Gli ingredienti: il ciclo
del fan (col campo `trasporto` che esporta la bandiera G del passo), la
completezza dell'orbita (F5c), l'unicità del trasportatore (che collassa il
quantificatore ∀σ' del kill-gate sul σ del ciclo), il tetto dello spigolo
(EdgeInAtMostTwoFacets) e le tre faccette (q ≥ 3).
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **IL VERTICE CICLICO**: in un politopo regolare ogni vertice è q-ciclico
per un q ≥ 3. -/
theorem verticeCiclico_del_regolare (P : ConvexPolytope 3)
    (hreg : P.IsRegular) {v : E 3} (hv : v ∈ P.vertices) :
    ∃ q : ℕ, 3 ≤ q ∧ Nonempty (P.asFinite.CyclicVertexData v q) := by
  classical
  have hfull : P.IsFullDim := hreg.1
  obtain ⟨F, hF0⟩ := bandiera_al_vertice P hfull hv
  obtain ⟨σ, m, hC⟩ := ciclo_fan_esiste P hreg hv F hF0
  obtain ⟨G, L, R, hG0, hL0, hL2, hR2, hLR, hσflag⟩ := hC.trasporto
  -- q = m ≥ 3 dalle tre faccette e dalla completezza
  have hq3 : 3 ≤ m := by
    obtain ⟨A, B, C, hA, hB, hC3, hAB, hAC, hBC⟩ :=
      tre_faccette_al_vertice P hfull hv
    obtain ⟨ka, hka, hkaeq⟩ := fan_completo P hfull hv hF0 hC A
      hA.1 hA.2.1 hA.2.2
    obtain ⟨kb, hkb, hkbeq⟩ := fan_completo P hfull hv hF0 hC B
      hB.1 hB.2.1 hB.2.2
    obtain ⟨kc, hkc, hkceq⟩ := fan_completo P hfull hv hF0 hC C
      hC3.1 hC3.2.1 hC3.2.2
    by_contra hcon
    push_neg at hcon
    have hcasi : ka = kb ∨ ka = kc ∨ kb = kc := by omega
    rcases hcasi with h | h | h
    · exact hAB (by rw [hkaeq, hkbeq, h])
    · exact hAC (by rw [hkaeq, hkceq, h])
    · exact hBC (by rw [hkbeq, hkceq, h])
  refine ⟨m, hq3, ?_⟩
  -- il kill-gate con il quantificatore collassato
  apply ConvexPolytope.fan_vertice_condizionale P hreg hq3 F G L R
    hF0 hG0 hL0 hL2 hR2 hLR
  · -- horbit: ogni trasportatore F→G dà il certificato
    intro σ' hσ'P hσ'flag
    have huni : ∀ z : E 3, σ z = σ' z :=
      trasportatore_unico P hfull hC.simmetria hσ'P F G hσflag hσ'flag
    have hfun : (⇑σ' : E 3 → E 3) = ⇑σ := funext (fun z => (huni z).symm)
    refine {
      period := ?_
      isFacet := ?_
      injective := ?_
      complete := ?_ }
    · show ((σ' : E 3 → E 3))^[m] '' F.face 2 = F.face 2
      rw [hfun]
      exact hC.ritorno
    · intro i
      show P.IsFace (((σ' : E 3 → E 3))^[i.val] '' F.face 2) ∧
        faceDim (((σ' : E 3 → E 3))^[i.val] '' F.face 2) = 2
      rw [hfun]
      exact ⟨(hC.faccetta i.val).1, (hC.faccetta i.val).2.1⟩
    · intro i j hij
      have hij' : ((σ' : E 3 → E 3))^[i.val] '' F.face 2 =
          ((σ' : E 3 → E 3))^[j.val] '' F.face 2 := hij
      rw [hfun] at hij'
      by_contra hne
      have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
      rcases Nat.lt_or_ge i.val j.val with h | h
      · exact hC.distinte i.val j.val h j.isLt hij'
      · have h2 : j.val < i.val := by omega
        exact hC.distinte j.val i.val h2 i.isLt hij'.symm
    · intro A hA hdA hvA
      obtain ⟨k, hkm, hkeq⟩ := fan_completo P hfull hv hF0 hC A hA hdA hvA
      refine ⟨⟨k, hkm⟩, ?_⟩
      show A = ((σ' : E 3 → E 3))^[k] '' F.face 2
      rw [hfun]
      exact hkeq
  · -- il tetto dello spigolo è un teorema
    exact edgeInAtMostTwoFacets_vale P v

end LeanEval.Geometry.PlatonicClassification
