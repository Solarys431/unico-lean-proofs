import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.SottoPolitopo
import UnicoProofs.Platonici.Interpolazione
import UnicoProofs.Platonici.DimStretta

/-!
MOTORE COXETER, PASSO 1 — LA FACCIA INTERMEDIA ESISTE (19 lug 2026).

Il lato «almeno uno» del diamante in rango arbitrario, ottenuto SENZA
teoria nuova: la relativizzazione era già nell'infrastruttura. Il
sotto-politopo di una faccia (`facePolytope`) ha per corpo la faccia
stessa, eredita le facce nei due versi, e `interpolazione` non chiede la
piena dimensionalità nell'ambiente ma lavora sulla dimensione intrinseca
`finrank (vectorSpan toSet)`. Dunque, date `A ⊂ B` con salto di rango 2:
si scende nel sotto-politopo di `B`, si interpola, si risale.

Correzione del vaglio avversariale accolta: questo è il lato facile; il
kill-gate vero («esattamente due») è un teorema separato.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- **LA FACCIA INTERMEDIA**: fra due facce a salto di rango 2 ne esiste
una di rango intermedio. -/
theorem faccia_intermedia (P : ConvexPolytope n) {A B : Set (E n)}
    (hA : P.IsFace A) (hB : P.IsFace B) (hAB : A ⊂ B)
    (hrank : faceDim B = faceDim A + 2) :
    ∃ C : Set (E n), P.IsFace C ∧ A ⊂ C ∧ C ⊂ B ∧
      faceDim C = faceDim A + 1 := by
  classical
  -- si scende nel sotto-politopo della faccia superiore
  set Q : ConvexPolytope n := facePolytope P hB with hQ
  have hQtoSet : Q.toSet = B := facePolytope_toSet P hB
  have hAQ : Q.IsFace A := facePolytope_isFace_of P hB hA hAB.subset
  -- il salto di rango, letto sulla dimensione intrinseca di Q
  have hgap : faceDim A + 2 ≤ Module.finrank ℝ (vectorSpan ℝ Q.toSet) := by
    rw [hQtoSet]
    have hBdim : Module.finrank ℝ (vectorSpan ℝ B) = faceDim A + 2 := hrank
    omega
  -- l'interpolazione dentro Q
  obtain ⟨C, hCQ, hACss, hCne⟩ := interpolazione Q hAQ hgap
  -- risalita a P
  have hCP : P.IsFace C := isFace_of_facePolytope P hB hCQ
  have hCB : C ⊆ B := by
    have h1 := face_subset_toSet Q hCQ
    rwa [hQtoSet] at h1
  have hCssB : C ⊂ B := by
    refine hCB.ssubset_of_ne ?_
    intro hEq
    apply hCne
    rw [hEq, hQtoSet]
  -- la dimensione è esattamente quella intermedia
  have hlo0 := faceDim_lt_of_ssubset P hA hCP hACss
  have hhi0 := faceDim_lt_of_ssubset P hCP hB hCssB
  have hlo : Module.finrank ℝ (vectorSpan ℝ A) <
      Module.finrank ℝ (vectorSpan ℝ C) := hlo0
  have hhi : Module.finrank ℝ (vectorSpan ℝ C) <
      Module.finrank ℝ (vectorSpan ℝ B) := hhi0
  have hBd : Module.finrank ℝ (vectorSpan ℝ B) =
      Module.finrank ℝ (vectorSpan ℝ A) + 2 := hrank
  refine ⟨C, hCP, hACss, hCssB, ?_⟩
  show Module.finrank ℝ (vectorSpan ℝ C) =
    Module.finrank ℝ (vectorSpan ℝ A) + 1
  omega

/-- Forma d'uso sulle bandiere: fra `F.face (i-1)` e `F.face (i+1)` esiste
una faccia intermedia di rango `i` (in particolare la stessa `F.face i`,
ma il teorema dà l'esistenza in forma riutilizzabile per l'adiacenza). -/
theorem faccia_intermedia_di_bandiera (P : ConvexPolytope n) (F : P.Flag)
    {i j : Fin n} (hij : (i : ℕ) + 2 = (j : ℕ)) :
    ∃ C : Set (E n), P.IsFace C ∧ F.face i ⊂ C ∧ C ⊂ F.face j ∧
      faceDim C = faceDim (F.face i) + 1 := by
  have hlt : i < j := by
    rw [Fin.lt_def]
    omega
  refine faccia_intermedia P (F.isFace i) (F.isFace j)
    (F.strict_mono i j hlt) ?_
  rw [F.dim_eq i, F.dim_eq j]
  omega

end LeanEval.Geometry.PlatonicClassification
