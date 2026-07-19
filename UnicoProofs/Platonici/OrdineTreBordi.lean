import Mathlib
import UnicoProofs.Platonici.OrdineTre

/-!
Gli ordini di Coxeter adiacenti sono almeno tre anche ai due bordi della
catena dei ranghi.  Il teorema unificato assume `3 ≤ n`: la dimensione due,
dove i due bordi coincidono e non esiste un intervallo di rango tre, resta
fuori da questo argomento.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Una faccia intermedia nell'intervallo che termina in `P.toSet` compare
al rango `i` di una bandiera del residuo. -/
theorem faccia_intermedia_e_una_delle_due_al_bordo (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hbordo : (i : ℕ) + 2 = n)
    (hcomm : adjacentFlag P hfull (adjacentFlag P hfull F i)
        ⟨(i : ℕ) + 1, hi⟩ =
      adjacentFlag P hfull (adjacentFlag P hfull F ⟨(i : ℕ) + 1, hi⟩) i)
    {C : Set (E n)} (hC : P.IsFace C) (hdC : faceDim C = (i : ℕ))
    (hsotto : ∀ k : Fin n, (k : ℕ) < (i : ℕ) → F.face k ⊂ C)
    (hsopra : C ⊂ P.toSet) :
    C = F.face i ∨ C = (adjacentFlag P hfull F i).face i := by
  obtain ⟨G, hGout, hGi⟩ :=
    bandiera_del_residuo_al_bordo P hfull F i hi hbordo
      hC hdC hsotto hsopra
  have hgal := residuo_rango_tre_connesso P hfull F G i hi
    (fun k hk hk2 => (hGout k hk hk2).symm)
  have h := facce_del_residuo_chiuso P hfull F i hi hcomm hgal
  rw [hGi] at h
  exact h

/-- Caso del bordo alto: `(i : ℕ) + 2 = n` e `0 < i`. -/
theorem ordine_tre_bordo_alto (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hbordo : (i : ℕ) + 2 = n)
    (hipos : 0 < (i : ℕ)) :
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
    have hcomm := mosse_commutano_di_ordine_due P hreg F hne h2
    obtain ⟨im, him⟩ : ∃ im : ℕ, (i : ℕ) = im + 1 :=
      ⟨(i : ℕ) - 1, by omega⟩
    have himn : im < n := by omega
    let A : Fin n := ⟨im, himn⟩
    have hAval : (A : ℕ) = im := rfl
    have hAtop : F.face A ⊆ P.toSet :=
      face_subset_toSet P (F.isFace A)
    have hAB : F.face A ⊂ P.toSet := by
      refine ⟨hAtop, ?_⟩
      intro htopA
      have heq : F.face A = P.toSet :=
        Set.Subset.antisymm hAtop htopA
      have hdim := congrArg faceDim heq
      have htopdim : faceDim P.toSet = n := hreg.1
      rw [F.dim_eq A, hAval, htopdim] at hdim
      omega
    have hrank : faceDim P.toSet = faceDim (F.face A) + 3 := by
      have htopdim : faceDim P.toSet = n := hreg.1
      rw [htopdim, F.dim_eq A, hAval]
      omega
    obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, h12, h13, h23⟩ :=
      tre_intermedie_di_rango_tre P (F.isFace A) (toSet_isFace P) hAB hrank
    have hdim : ∀ {C : Set (E n)}, faceDim C = faceDim (F.face A) + 1 →
        faceDim C = (i : ℕ) := by
      intro C hC
      rw [hC, F.dim_eq A, hAval]
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
        C ⊂ P.toSet → faceDim C = faceDim (F.face A) + 1 →
        C = F.face i ∨ C = (adjacentFlag P hreg.1 F i).face i := by
      intro C hCface hAC hCTop hCdim
      exact faccia_intermedia_e_una_delle_due_al_bordo P hreg.1 F i hi
        hbordo hcomm hCface (hdim hCdim) (hsotto hAC) hCTop
    have r₁ := hone hC₁.1 hC₁.2.1 hC₁.2.2.1 hC₁.2.2.2
    have r₂ := hone hC₂.1 hC₂.2.1 hC₂.2.2.1 hC₂.2.2.2
    have r₃ := hone hC₃.1 hC₃.2.1 hC₃.2.2.1 hC₃.2.2.2
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

/-- Una faccia di rango zero contenuta nella faccia di rango due compare
al rango zero di una bandiera del residuo.  L'ipotesi sotto il rango zero
è esplicitamente scaricata per vacuità. -/
theorem faccia_zero_e_una_delle_due (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hi2 : (i : ℕ) + 2 < n)
    (hi0 : (i : ℕ) = 0)
    (hcomm : adjacentFlag P hfull (adjacentFlag P hfull F i)
        ⟨(i : ℕ) + 1, hi⟩ =
      adjacentFlag P hfull (adjacentFlag P hfull F ⟨(i : ℕ) + 1, hi⟩) i)
    {C : Set (E n)} (hC : P.IsFace C) (hdC : faceDim C = 0)
    (hsopra : C ⊂ F.face ⟨(i : ℕ) + 2, hi2⟩) :
    C = F.face i ∨ C = (adjacentFlag P hfull F i).face i := by
  have hsotto : ∀ k : Fin n, (k : ℕ) < (i : ℕ) → F.face k ⊂ C := by
    intro k hk
    omega
  obtain ⟨G, hGout, hGi⟩ :=
    bandiera_del_residuo_generale P hfull F i hi hi2 hC
      (by simpa [hi0] using hdC) hsotto hsopra
  have hgal := residuo_rango_tre_connesso P hfull F G i hi
    (fun k hk hk2 => (hGout k hk hk2).symm)
  have h := facce_del_residuo_chiuso P hfull F i hi hcomm hgal
  rw [hGi] at h
  exact h

/-- Caso del bordo basso: `i = 0`, purché esista il rango due. -/
theorem ordine_tre_bordo_zero (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hi2 : (i : ℕ) + 2 < n)
    (hi0 : (i : ℕ) = 0) :
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
    have hcomm := mosse_commutano_di_ordine_due P hreg F hne h2
    let i2 : Fin n := ⟨(i : ℕ) + 2, hi2⟩
    let Q := facePolytope P (F.isFace i2)
    have hQdim : faceDim Q.toSet = 2 := by
      change faceDim (facePolytope P (F.isFace i2)).toSet = 2
      rw [facePolytope_toSet P (F.isFace i2), F.dim_eq i2]
      change (i : ℕ) + 2 = 2
      omega
    obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, h12, h13, h23⟩ :=
      tre_vertici_di_poligono Q hQdim
    have hlift : ∀ {C : Set (E n)}, Q.IsFace C → P.IsFace C := by
      intro C hCQ
      exact isFace_of_facePolytope P (F.isFace i2) hCQ
    have hstrict : ∀ {C : Set (E n)}, Q.IsFace C → faceDim C = 0 →
        C ⊂ F.face i2 := by
      intro C hCQ hCdim
      have hsubQ := face_subset_toSet Q hCQ
      have hsub : C ⊆ F.face i2 := by
        change C ⊆ (facePolytope P (F.isFace i2)).toSet at hsubQ
        rwa [facePolytope_toSet P (F.isFace i2)] at hsubQ
      refine ⟨hsub, ?_⟩
      intro hback
      have heq : C = F.face i2 := Set.Subset.antisymm hsub hback
      have hdimEq := congrArg faceDim heq
      rw [hCdim, F.dim_eq i2] at hdimEq
      change 0 = (i : ℕ) + 2 at hdimEq
      omega
    have hone : ∀ {C : Set (E n)}, Q.IsFace C → faceDim C = 0 →
        C = F.face i ∨ C = (adjacentFlag P hreg.1 F i).face i := by
      intro C hCQ hCdim
      exact faccia_zero_e_una_delle_due P hreg.1 F i hi hi2 hi0 hcomm
        (hlift hCQ) hCdim (hstrict hCQ hCdim)
    have r₁ := hone hC₁.1 hC₁.2
    have r₂ := hone hC₂.1 hC₂.2
    have r₃ := hone hC₃.1 hC₃.2
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

/-- In dimensione almeno tre ogni coppia di ranghi adiacenti ha ordine
di Coxeter almeno tre, inclusi entrambi i bordi. -/
theorem coxeterMatrix_adiacente_ge_tre_ovunque (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hn : 3 ≤ n) :
    3 ≤ coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ := by
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hipos
  · have hi2 : (i : ℕ) + 2 < n := by omega
    exact ordine_tre_bordo_zero P hreg F i hi hi2 hi0
  · have hi2le : (i : ℕ) + 2 ≤ n := by omega
    rcases Nat.lt_or_eq_of_le hi2le with hi2 | hbordo
    · exact coxeterMatrix_adiacente_ge_tre P hreg F i hi hi2 hipos
    · exact ordine_tre_bordo_alto P hreg F i hi hbordo hipos

end LeanEval.Geometry.PlatonicClassification
