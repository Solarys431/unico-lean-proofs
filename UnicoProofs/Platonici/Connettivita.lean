import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.MossaInvolutiva
import UnicoProofs.Platonici.Gallerie

/-!
MOTORE COXETER, PASSO 17 — INFRASTRUTTURA DELLE GALLERIE E IL MURO
(19 lug 2026).

Il muro grande del motore resta la connettività: che ogni due bandiere
siano collegate da una galleria. Qui NON lo si dimostra. Si certifica
l'infrastruttura che servirà alla dimostrazione, e si scrive il muro
nella sua forma corretta, che è locale e più debole della tesi:

`RidgeConnected P` — dentro ogni faccia `B`, due facce di codimensione 1
sono collegate da una catena in cui consecutive si incontrano in una
faccia di codimensione 2. È la connettività del grafo delle faccette
(Balinski in forma debole), il fatto geometrico da cui la connettività
per gallerie discende per induzione sul rango.

Attenzione a non confondere questo con l'enunciato «due bandiere che
coincidono sopra il rango massimo sono connesse», che è vacuo: coincidere
sopra `n − 1` non è un'ipotesi, è la tesi generale travestita.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Due bandiere coincidono dal rango `m` in su. -/
def AgreeAbove (P : ConvexPolytope n) (F G : P.Flag) (m : ℕ) : Prop :=
  ∀ k : Fin n, m ≤ (k : ℕ) → F.face k = G.face k

theorem agreeAbove_zero (P : ConvexPolytope n) {F G : P.Flag}
    (h : AgreeAbove P F G 0) : F = G := by
  apply flag_ext
  funext k
  exact h k (Nat.zero_le _)

theorem agreeAbove_mono (P : ConvexPolytope n) {F G : P.Flag} {m m' : ℕ}
    (hmm : m ≤ m') (h : AgreeAbove P F G m) : AgreeAbove P F G m' :=
  fun k hk => h k (le_trans hmm hk)

/-- Sopra il rango massimo l'ipotesi è vuota: `AgreeAbove _ _ n` non dice
nulla. Registrato esplicitamente per non scambiarlo per un'induzione. -/
theorem agreeAbove_of_ge (P : ConvexPolytope n) (F G : P.Flag) {m : ℕ}
    (hm : n ≤ m) : AgreeAbove P F G m := by
  intro k hk
  exfalso
  have := k.isLt
  omega

/-- Bandiere adiacenti coincidono sopra il rango della mossa più uno. -/
theorem agreeAbove_of_adjacent (P : ConvexPolytope n) {F G : P.Flag}
    {i : Fin n} (h : FlagAdjacentAt P F G i) :
    AgreeAbove P F G ((i : ℕ) + 1) := by
  intro k hk
  refine (h.1 k (fun hki => ?_)).symm
  rw [hki] at hk
  omega

/-- Se due bandiere coincidono fuori da un rango, sono connesse (uguali
oppure adiacenti). -/
theorem galleryConnected_of_agree_except (P : ConvexPolytope n)
    (F G : P.Flag) (i : Fin n)
    (h : ∀ j : Fin n, j ≠ i → F.face j = G.face j) :
    GalleryConnected P F G := by
  by_cases heq : G.face i = F.face i
  · have hFG : F = G := by
      apply flag_ext
      funext k
      by_cases hk : k = i
      · rw [hk, heq]
      · exact h k hk
    rw [hFG]
    exact galleryConnected_refl P G
  · exact Relation.ReflTransGen.single
      ⟨i, ⟨fun j hj => (h j hj).symm, heq⟩⟩

/-- **IL MURO, in forma locale.** Dentro ogni faccia `B`, due facce di
codimensione 1 in `B` sono collegate da una catena di facce di
codimensione 1 in cui due consecutive si incontrano in una faccia di
codimensione 2. È la connettività del grafo delle faccette. -/
def RidgeConnected (P : ConvexPolytope n) : Prop :=
  ∀ (B : Set (E n)), P.IsFace B →
    ∀ (A A' : Set (E n)), P.IsFace A → P.IsFace A' →
      A ⊂ B → A' ⊂ B →
      faceDim A + 1 = faceDim B → faceDim A' + 1 = faceDim B →
      Relation.ReflTransGen
        (fun X Y : Set (E n) =>
          P.IsFace X ∧ P.IsFace Y ∧ X ⊂ B ∧ Y ⊂ B ∧
            faceDim X + 1 = faceDim B ∧ faceDim Y + 1 = faceDim B ∧
            ∃ R : Set (E n), P.IsFace R ∧ R ⊂ X ∧ R ⊂ Y ∧
              faceDim R + 2 = faceDim B)
        A A'

/-- La relazione di adiacenza fra faccette è simmetrica. -/
theorem ridgeStep_symm (P : ConvexPolytope n) (B X Y : Set (E n))
    (h : P.IsFace X ∧ P.IsFace Y ∧ X ⊂ B ∧ Y ⊂ B ∧
      faceDim X + 1 = faceDim B ∧ faceDim Y + 1 = faceDim B ∧
      ∃ R : Set (E n), P.IsFace R ∧ R ⊂ X ∧ R ⊂ Y ∧
        faceDim R + 2 = faceDim B) :
    P.IsFace Y ∧ P.IsFace X ∧ Y ⊂ B ∧ X ⊂ B ∧
      faceDim Y + 1 = faceDim B ∧ faceDim X + 1 = faceDim B ∧
      ∃ R : Set (E n), P.IsFace R ∧ R ⊂ Y ∧ R ⊂ X ∧
        faceDim R + 2 = faceDim B := by
  obtain ⟨hX, hY, hXB, hYB, hdX, hdY, R, hR, hRX, hRY, hdR⟩ := h
  exact ⟨hY, hX, hYB, hXB, hdY, hdX, R, hR, hRY, hRX, hdR⟩

end LeanEval.Geometry.PlatonicClassification
