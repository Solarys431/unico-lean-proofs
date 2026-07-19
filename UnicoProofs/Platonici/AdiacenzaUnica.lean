import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.FlagAdiacente
import UnicoProofs.Platonici.SecondoIntermedio
import UnicoProofs.Platonici.DueVertici

/-!
MOTORE COXETER, PASSO 6 — L'ADIACENZA È UNICA (19 lug 2026).

Il teorema unificato: per ogni bandiera `F` di un politopo pieno e ogni
rango `i`, esiste UN'UNICA bandiera adiacente a `F` in `i`. I tre casi
del vaglio (i = 0, interno, i = n−1) si compattano in due grazie alla
«faccia sopra» unificata: `F.face (i+1)` per i ranghi interni, `P.toSet`
per il rango massimo — in entrambi i casi una faccia di dimensione
`i+1` che contiene strettamente `F.face i`.

- `i = 0`: l'altro vertice dello spigolo (`due_vertici_per_spigolo`).
- `i > 0`: il diamante relativo (`existsUnique_other_middle`).

Il rimontaggio in bandiera passa per `sostituisci` (Function.update),
l'unicità per l'estensionalità delle bandiere: la catena determina la
bandiera, perché gli altri campi sono proposizioni.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Estensionalità delle bandiere: la catena di facce determina la
bandiera (gli altri campi sono proposizioni). -/
theorem flag_ext {P : ConvexPolytope n} {F G : P.Flag}
    (h : F.face = G.face) : F = G := by
  cases F with
  | mk f hf hd hm =>
    cases G with
    | mk g hg hd' hm' =>
      dsimp only at h
      subst h
      rfl

/-- La «faccia sopra» il rango `i`: `F.face (i+1)` per i ranghi interni,
`P.toSet` per il rango massimo. In entrambi i casi: una faccia di
dimensione `i+1` sopra `F.face i`, sotto tutte le facce dei ranghi
superiori, e massimale fra le facce di dimensione `i` incastrate
nella coda della bandiera. -/
theorem faccia_sopra (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (F : P.Flag) (i : Fin n) :
    ∃ B : Set (E n), P.IsFace B ∧ faceDim B = (i : ℕ) + 1 ∧
      F.face i ⊂ B ∧
      (∀ j : Fin n, i < j → B ⊆ F.face j) ∧
      (∀ D : Set (E n), P.IsFace D → faceDim D = (i : ℕ) →
        (∀ j : Fin n, i < j → D ⊂ F.face j) → D ⊂ B) := by
  by_cases hi : (i : ℕ) + 1 < n
  · -- rango interno: B = F.face (i+1)
    refine ⟨F.face ⟨(i : ℕ) + 1, hi⟩, F.isFace _, ?_, ?_, ?_, ?_⟩
    · exact F.dim_eq _
    · refine F.strict_mono i ⟨(i : ℕ) + 1, hi⟩ ?_
      rw [Fin.lt_def]
      show (i : ℕ) < (i : ℕ) + 1
      omega
    · intro j hj
      rcases Nat.lt_or_ge ((i : ℕ) + 1) (j : ℕ) with hlt | hge
      · refine (F.strict_mono ⟨(i : ℕ) + 1, hi⟩ j ?_).subset
        rw [Fin.lt_def]
        show (i : ℕ) + 1 < (j : ℕ)
        exact hlt
      · have hje : j = ⟨(i : ℕ) + 1, hi⟩ := by
          apply Fin.ext
          show (j : ℕ) = (i : ℕ) + 1
          rw [Fin.lt_def] at hj
          omega
        subst hje
        exact subset_rfl
    · intro D _ _ hDj
      refine hDj ⟨(i : ℕ) + 1, hi⟩ ?_
      rw [Fin.lt_def]
      show (i : ℕ) < (i : ℕ) + 1
      omega
  · -- rango massimo: B = P.toSet
    have hin : (i : ℕ) + 1 = n := by
      have := i.isLt
      omega
    have hPdim : faceDim P.toSet = n := hfull
    refine ⟨P.toSet, toSet_isFace P, ?_, ?_, ?_, ?_⟩
    · rw [hPdim]
      omega
    · refine (face_subset_toSet P (F.isFace i)).ssubset_of_ne ?_
      intro heq
      have hdi := F.dim_eq i
      rw [heq, hPdim] at hdi
      have := i.isLt
      omega
    · intro j hj
      exfalso
      rw [Fin.lt_def] at hj
      have := j.isLt
      omega
    · intro D hD hdD _
      refine (face_subset_toSet P hD).ssubset_of_ne ?_
      intro heq
      rw [heq, hPdim] at hdD
      omega

/-- **Il teorema dell'adiacenza**: per ogni bandiera `F` di un politopo
pieno e ogni rango `i`, esiste un'unica bandiera adiacente a `F` in `i`.
È il primo cancello del motore Coxeter: la mossa elementare sulle
bandiere è ben definita e involutiva. -/
theorem existsUnique_flag_adjacent (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) (i : Fin n) :
    ∃! G : P.Flag, FlagAdjacentAt P F G i := by
  obtain ⟨B, hB, hdB, hFiB, hBsub, hDB⟩ := faccia_sopra P hfull F i
  -- Passo 1: l'unica faccia sostitutiva al rango i.
  have hQ : ∃! C : Set (E n),
      (P.IsFace C ∧ faceDim C = (i : ℕ) ∧
        (∀ j : Fin n, j < i → F.face j ⊂ C) ∧ C ⊂ B) ∧
      C ≠ F.face i := by
    by_cases hi0 : (i : ℕ) = 0
    · -- caso di bordo: l'altro vertice dello spigolo B
      have hdB1 : faceDim B = 1 := by rw [hdB, hi0]
      have hdV : faceDim (F.face i) = 0 := by
        rw [F.dim_eq]
        exact hi0
      have hVB : F.face i < B := hFiB
      obtain ⟨W, ⟨⟨hWface, hWdim, hWB⟩, hWne⟩, hWuniq⟩ :=
        due_vertici_per_spigolo P hB hdB1 (F.isFace i) hdV hVB
      refine ⟨W, ⟨⟨hWface, ?_, ?_, hWB⟩, hWne⟩, ?_⟩
      · rw [hWdim, hi0]
      · intro j hj
        exfalso
        rw [Fin.lt_def, hi0] at hj
        omega
      · intro C hC
        refine hWuniq C ⟨⟨hC.1.1, ?_, hC.1.2.2.2⟩, hC.2⟩
        rw [hC.1.2.1, hi0]
    · -- caso generale: il diamante relativo sotto B
      have hipos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi0
      obtain ⟨iv, hiv⟩ : ∃ iv : ℕ, (i : ℕ) = iv + 1 :=
        ⟨(i : ℕ) - 1, by omega⟩
      have hivn : iv < n := by
        have := i.isLt
        omega
      have him : ((⟨iv, hivn⟩ : Fin n) : ℕ) + 1 = (i : ℕ) := by
        show iv + 1 = (i : ℕ)
        omega
      have himlt : (⟨iv, hivn⟩ : Fin n) < i := by
        rw [Fin.lt_def]
        show iv < (i : ℕ)
        omega
      have hrank : faceDim B = faceDim (F.face ⟨iv, hivn⟩) + 2 := by
        rw [hdB, F.dim_eq]
        show (i : ℕ) + 1 = iv + 2
        omega
      have hAC : F.face ⟨iv, hivn⟩ < F.face i := F.strict_mono _ i himlt
      have hCB : F.face i < B := hFiB
      obtain ⟨C', ⟨⟨hC'face, hAC', hC'B⟩, hC'ne⟩, hC'uniq⟩ :=
        existsUnique_other_middle P (F.isFace ⟨iv, hivn⟩) hB hrank
          (F.isFace i) hAC hCB
      have hdC' : faceDim C' = (i : ℕ) := by
        have h1 := faceDim_lt_of_ssubset P (F.isFace ⟨iv, hivn⟩) hC'face hAC'
        have h2 := faceDim_lt_of_ssubset P hC'face hB hC'B
        rw [F.dim_eq] at h1
        rw [hdB] at h2
        have h1' : iv < faceDim C' := h1
        omega
      refine ⟨C', ⟨⟨hC'face, hdC', ?_, hC'B⟩, hC'ne⟩, ?_⟩
      · exact catena_sotto P F him hAC'
      · intro C hC
        exact hC'uniq C ⟨⟨hC.1.1, hC.1.2.2.1 _ himlt, hC.1.2.2.2⟩, hC.2⟩
  -- Passo 2: il rimontaggio in bandiera e l'unicità.
  obtain ⟨C, ⟨⟨hCface, hCdim, hCsotto, hCB⟩, hCne⟩, hCuniq⟩ := hQ
  have hCsopra : ∀ j : Fin n, i < j → C ⊂ F.face j := by
    intro j hj
    exact ssubset_of_ssubset_of_subset hCB (hBsub j hj)
  refine ⟨sostituisci P F i C hCface hCdim hCsotto hCsopra, ⟨?_, ?_⟩, ?_⟩
  · intro j hj
    exact sostituisci_face_ne P F i C hCface hCdim hCsotto hCsopra hj
  · rw [sostituisci_face_self]
    exact hCne
  · intro G' hG'
    obtain ⟨hG'eq, hG'ne⟩ := hG'
    have hQ' : (P.IsFace (G'.face i) ∧ faceDim (G'.face i) = (i : ℕ) ∧
        (∀ j : Fin n, j < i → F.face j ⊂ G'.face i) ∧ G'.face i ⊂ B) ∧
        G'.face i ≠ F.face i := by
      refine ⟨⟨G'.isFace i, G'.dim_eq i, ?_, ?_⟩, hG'ne⟩
      · intro j hj
        rw [← hG'eq j (ne_of_lt hj)]
        exact G'.strict_mono j i hj
      · refine hDB (G'.face i) (G'.isFace i) (G'.dim_eq i) ?_
        intro j hj
        rw [← hG'eq j (ne_of_gt hj)]
        exact G'.strict_mono i j hj
    have hCeq : G'.face i = C := hCuniq (G'.face i) hQ'
    apply flag_ext
    funext j
    by_cases hj : j = i
    · subst hj
      rw [sostituisci_face_self]
      exact hCeq
    · rw [sostituisci_face_ne P F i C hCface hCdim hCsotto hCsopra hj]
      exact hG'eq j hj

end LeanEval.Geometry.PlatonicClassification
