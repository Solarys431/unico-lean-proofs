import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.MossaInvolutiva
import UnicoProofs.Platonici.Trasportatore
import UnicoProofs.Platonici.RelazioniCoxeter
import UnicoProofs.Platonici.Ordini
import UnicoProofs.Platonici.Coniugazione
import UnicoProofs.Platonici.TreIntermedie
import UnicoProofs.Platonici.FaccetteConnesse
import UnicoProofs.Platonici.OrdineAdiacente
import UnicoProofs.Platonici.BandieraDelResiduo
import UnicoProofs.Platonici.PonteMosse

/-!
MOTORE COXETER, PASSO 24 — GLI ORDINI ADIACENTI SONO ALMENO 3
(19 lug 2026).

Il montaggio finale. Se `mᵢ,ᵢ₊₁ = 2`:

  ordine 2  →  le riflessioni commutano nel gruppo      (`simpleGen_comm_of_order_two`)
            →  le MOSSE commutano sulle bandiere         (`mosse_commutano_di_riflessioni`)
            →  l'orbita ha ≤ 4 bandiere                  (`residuo_chiuso_di_commutazione`)
            →  ≤ 2 facce distinte al rango i             (`facce_del_residuo_chiuso`)

mentre dall'altro lato:

  intervallo di rango 3  →  ≥ 3 facce intermedie distinte (`tre_intermedie_di_rango_tre`)
                         →  ciascuna sta in una bandiera del residuo (`bandiera_del_residuo_generale`)
                         →  ciascuna bandiera è raggiungibile          (`residuo_rango_tre_connesso`)

Tre facce distinte non stanno in un insieme di due.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Ogni faccia intermedia dell'intervallo di rango 3 compare al rango
`i` di una bandiera raggiungibile, dunque è una delle due ammesse dalla
commutazione. -/
theorem faccia_intermedia_e_una_delle_due (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    (hi2 : (i : ℕ) + 2 < n)
    (hcomm : adjacentFlag P hfull (adjacentFlag P hfull F i)
        ⟨(i : ℕ) + 1, hi⟩ =
      adjacentFlag P hfull (adjacentFlag P hfull F ⟨(i : ℕ) + 1, hi⟩) i)
    {C : Set (E n)} (hC : P.IsFace C) (hdC : faceDim C = (i : ℕ))
    (hsotto : ∀ k : Fin n, (k : ℕ) < (i : ℕ) → F.face k ⊂ C)
    (hsopra : C ⊂ F.face ⟨(i : ℕ) + 2, hi2⟩) :
    C = F.face i ∨ C = (adjacentFlag P hfull F i).face i := by
  obtain ⟨G, hGout, hGi⟩ :=
    bandiera_del_residuo_generale P hfull F i hi hi2 hC hdC hsotto hsopra
  have hgal := residuo_rango_tre_connesso P hfull F G i hi
    (fun k hk hk2 => (hGout k hk hk2).symm)
  have h := facce_del_residuo_chiuso P hfull F i hi hcomm hgal
  rw [hGi] at h
  exact h

/-- **GLI ORDINI ADIACENTI SONO ALMENO 3.** Per i ranghi interni, la
matrice di Coxeter soddisfa `mᵢ,ᵢ₊₁ ≥ 3`. -/
theorem coxeterMatrix_adiacente_ge_tre (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    (hi2 : (i : ℕ) + 2 < n) (hipos : 0 < (i : ℕ)) :
    3 ≤ coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ := by
  classical
  set ip : Fin n := ⟨(i : ℕ) + 1, hi⟩ with hip
  have hne : i ≠ ip := by
    intro he
    have : (i : ℕ) = (i : ℕ) + 1 := congrArg Fin.val he
    omega
  have hge2 : 2 ≤ coxeterMatrix P hreg F i ip :=
    coxeterMatrix_off_diag_ge P hreg F hne
  rcases Nat.lt_or_ge (coxeterMatrix P hreg F i ip) 3 with hlt | hge
  · exfalso
    have h2 : coxeterMatrix P hreg F i ip = 2 := by omega
    -- le mosse commutano
    have hcomm := mosse_commutano_di_ordine_due P hreg F hne h2
    -- l'intervallo di rango 3 sotto F.face (i+2) e sopra F.face (i-1)
    obtain ⟨im, him⟩ : ∃ im : ℕ, (i : ℕ) = im + 1 := ⟨(i : ℕ) - 1, by omega⟩
    have himn : im < n := by omega
    let A : Fin n := ⟨im, himn⟩
    let B : Fin n := ⟨(i : ℕ) + 2, hi2⟩
    have hAval : (A : ℕ) = im := rfl
    have hBval : (B : ℕ) = (i : ℕ) + 2 := rfl
    have hAB : F.face A ⊂ F.face B := by
      refine F.strict_mono A B ?_
      rw [Fin.lt_def, hAval, hBval]
      omega
    have hrank : faceDim (F.face B) = faceDim (F.face A) + 3 := by
      rw [F.dim_eq, F.dim_eq, hAval, hBval]
      omega
    obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, h12, h13, h23⟩ :=
      tre_intermedie_di_rango_tre P (F.isFace A) (F.isFace B) hAB hrank
    -- ciascuna ha rango i ed è incastrata come richiesto
    have hdim : ∀ {C : Set (E n)}, faceDim C = faceDim (F.face A) + 1 →
        faceDim C = (i : ℕ) := by
      intro C hC
      rw [hC, F.dim_eq, hAval]
      omega
    have hsotto : ∀ {C : Set (E n)}, F.face A ⊂ C →
        ∀ k : Fin n, (k : ℕ) < (i : ℕ) → F.face k ⊂ C := by
      intro C hAC k hk
      rcases Nat.lt_or_ge (k : ℕ) im with hklt | hkge
      · refine lt_of_lt_of_le ?_ hAC.le
        refine F.strict_mono k A ?_
        rw [Fin.lt_def, hAval]
        exact hklt
      · have hkA : k = A := by
          apply Fin.ext
          show (k : ℕ) = im
          omega
        rw [hkA]
        exact hAC
    have hone : ∀ {C : Set (E n)}, P.IsFace C → F.face A ⊂ C →
        C ⊂ F.face B → faceDim C = faceDim (F.face A) + 1 →
        C = F.face i ∨ C = (adjacentFlag P hreg.1 F i).face i := by
      intro C hCface hAC hCB hCdim
      exact faccia_intermedia_e_una_delle_due P hreg.1 F i hi hi2 hcomm
        hCface (hdim hCdim) (hsotto hAC) hCB
    have r₁ := hone hC₁.1 hC₁.2.1 hC₁.2.2.1 hC₁.2.2.2
    have r₂ := hone hC₂.1 hC₂.2.1 hC₂.2.2.1 hC₂.2.2.2
    have r₃ := hone hC₃.1 hC₃.2.1 hC₃.2.2.1 hC₃.2.2.2
    -- tre valori distinti in un insieme di due
    rcases r₁ with e₁ | e₁ <;> rcases r₂ with e₂ | e₂ <;>
      rcases r₃ with e₃ | e₃
    · exact h12 (e₁.trans e₂.symm)
    · exact h12 (e₁.trans e₂.symm)
    · exact h13 (e₁.trans e₃.symm)
    · exact h23 (e₂.trans e₃.symm)
    · exact h23 (e₂.trans e₃.symm)
    · exact h13 (e₁.trans e₃.symm)
    · exact h12 (e₁.trans e₂.symm)
    · exact h12 (e₁.trans e₂.symm)
  · exact hge

end LeanEval.Geometry.PlatonicClassification
