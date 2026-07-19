import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.MossaInvolutiva
import UnicoProofs.Platonici.Equivarianza
import UnicoProofs.Platonici.Trasportatore
import UnicoProofs.Platonici.RelazioniCoxeter
import UnicoProofs.Platonici.GruppoFinito
import UnicoProofs.Platonici.Ordini
import UnicoProofs.Platonici.Coniugazione
import UnicoProofs.Platonici.TreIntermedie
import UnicoProofs.Platonici.FaccetteConnesse

/-!
MOTORE COXETER, PASSO 22 — GLI ORDINI ADIACENTI SONO ALMENO 3
(19 lug 2026).

Con la connettività del residuo (caduta col fascicolo 45), il gruppo
`⟨μᵢ, μᵢ₊₁⟩` agisce transitivamente sulle bandiere del residuo. Se
`mᵢ` fosse 2, le due mosse commuterebbero e l'orbita della bandiera base
conterrebbe al più QUATTRO bandiere, con al più DUE facce distinte al
rango `i`. Ma l'intervallo di rango 3 ne contiene almeno tre
(`tre_intermedie_di_rango_tre`), e per connettività ogni faccia del
residuo compare nell'orbita. Contraddizione.

Il cuore è il lemma di orbita: percorrendo una galleria del residuo, la
faccia di rango `i` raggiunta è sempre una di quelle che compaiono nelle
bandiere generate dalle due mosse.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Se le due mosse adiacenti commutano, le bandiere raggiungibili dal
residuo sono al più quattro: `F`, `adj_i F`, `adj_{i+1} F` e la comune
`adj_i (adj_{i+1} F) = adj_{i+1} (adj_i F)`. -/
theorem residuo_chiuso_di_commutazione (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    (hcomm : adjacentFlag P hfull (adjacentFlag P hfull F i)
        ⟨(i : ℕ) + 1, hi⟩ =
      adjacentFlag P hfull (adjacentFlag P hfull F ⟨(i : ℕ) + 1, hi⟩) i)
    {G : P.Flag}
    (hgal : Relation.ReflTransGen
      (fun X Y : P.Flag =>
        Y = adjacentFlag P hfull X i ∨
        Y = adjacentFlag P hfull X ⟨(i : ℕ) + 1, hi⟩)
      F G) :
    G = F ∨ G = adjacentFlag P hfull F i ∨
      G = adjacentFlag P hfull F ⟨(i : ℕ) + 1, hi⟩ ∨
      G = adjacentFlag P hfull (adjacentFlag P hfull F i)
        ⟨(i : ℕ) + 1, hi⟩ := by
  set ip : Fin n := ⟨(i : ℕ) + 1, hi⟩ with hip
  set A := adjacentFlag P hfull F i with hA
  set B := adjacentFlag P hfull F ip with hB
  set C := adjacentFlag P hfull A ip with hC
  induction hgal with
  | refl => exact Or.inl rfl
  | tail _ hstep ih =>
      rcases ih with h | h | h | h
      · subst h
        rcases hstep with hs | hs
        · exact Or.inr (Or.inl hs)
        · exact Or.inr (Or.inr (Or.inl hs))
      · subst h
        rcases hstep with hs | hs
        · rw [hs, adjacentFlag_involutive]
          exact Or.inl rfl
        · rw [hs]
          exact Or.inr (Or.inr (Or.inr rfl))
      · subst h
        rcases hstep with hs | hs
        · rw [hs, ← hcomm]
          exact Or.inr (Or.inr (Or.inr rfl))
        · rw [hs, adjacentFlag_involutive]
          exact Or.inl rfl
      · subst h
        rcases hstep with hs | hs
        · rw [hs, hcomm, adjacentFlag_involutive]
          exact Or.inr (Or.inr (Or.inl rfl))
        · rw [hs, adjacentFlag_involutive]
          exact Or.inr (Or.inl rfl)

/-- Le facce di rango `i` che compaiono nelle quattro bandiere sono al
più due: `F.face i` e `(adj_i F).face i`. -/
theorem facce_del_residuo_chiuso (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    (hcomm : adjacentFlag P hfull (adjacentFlag P hfull F i)
        ⟨(i : ℕ) + 1, hi⟩ =
      adjacentFlag P hfull (adjacentFlag P hfull F ⟨(i : ℕ) + 1, hi⟩) i)
    {G : P.Flag}
    (hgal : Relation.ReflTransGen
      (fun X Y : P.Flag =>
        Y = adjacentFlag P hfull X i ∨
        Y = adjacentFlag P hfull X ⟨(i : ℕ) + 1, hi⟩)
      F G) :
    G.face i = F.face i ∨
      G.face i = (adjacentFlag P hfull F i).face i := by
  set ip : Fin n := ⟨(i : ℕ) + 1, hi⟩ with hip
  have hne : i ≠ ip := by
    intro he
    have : (i : ℕ) = (i : ℕ) + 1 := congrArg Fin.val he
    omega
  rcases residuo_chiuso_di_commutazione P hfull F i hi hcomm hgal with
    h | h | h | h
  · rw [h]; exact Or.inl rfl
  · rw [h]; exact Or.inr rfl
  · rw [h]
    refine Or.inl ?_
    exact (adjacentFlag_isAdjacent P hfull F ip).1 i hne
  · rw [h]
    refine Or.inr ?_
    exact (adjacentFlag_isAdjacent P hfull
      (adjacentFlag P hfull F i) ip).1 i hne

end LeanEval.Geometry.PlatonicClassification
