import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.InvarianteSimilarita
import UnicoProofs.Platonici.Dim2Scheletro

/-!
CAMPAGNA #50 — IL MINORANTE GENERICO (19 lug 2026).

`k` politopi regolari a due a due non simili danno `k ≤ platonicCount d`,
in dimensione qualunque. Serve per tutte le dimensioni ancora aperte:
`d ≥ 5` (i tre: simplesso, ipercubo, ortoplesso) e `d = 4` (i sei).

Il minorante per la dimensione 3 era stato dimostrato ad hoc per k = 5
(`cinque_le_platonicCount3_di`); questa è la forma generale, e usa lo
stesso discriminante del caso infinito: classi distinte, quindi
cardinalità almeno k.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **IL MINORANTE GENERICO**: `k` politopi regolari a due a due non
simili danno `k ≤ platonicCount d`. -/
theorem le_platonicCount (d k : ℕ) (F : Fin k → regularPolytopes d)
    (hdist : ∀ i j : Fin k, i ≠ j → ¬ regularSimilar d (F i) (F j)) :
    (k : ℕ∞) ≤ platonicCount d := by
  classical
  have hinj : Function.Injective (fun i => classeSim d (F i)) := by
    intro i j hij
    by_contra hne
    apply hdist i j hne
    have hij' : classeSim d (F i) = classeSim d (F j) := hij
    have hmem : F j ∈ classeSim d (F j) :=
      similar_refl (F j : ConvexPolytope d)
    show F j ∈ classeSim d (F i)
    rw [hij']
    exact hmem
  have hsub : Set.range (fun i => classeSim d (F i)) ⊆
      {S : Set (regularPolytopes d) |
        ∃ P', S = {Q : regularPolytopes d | regularSimilar d P' Q}} := by
    rintro S ⟨i, rfl⟩
    exact classeSim_mem_quoziente d (F i)
  have hcard : (Set.range (fun i => classeSim d (F i))).encard = k := by
    rw [← Set.image_univ, hinj.encard_image, Set.encard_univ]
    simp
  calc (k : ℕ∞) = (Set.range (fun i => classeSim d (F i))).encard :=
        hcard.symm
    _ ≤ _ := Set.encard_le_encard hsub

/-- La forma d'uso quando i testimoni sono dati da una funzione con un
invariante che li separa (per esempio il numero di vertici). -/
theorem le_platonicCount_di_invariante (d k : ℕ)
    (F : Fin k → regularPolytopes d) {α : Type*}
    (inv : regularPolytopes d → α)
    (hinv : ∀ P Q : regularPolytopes d, regularSimilar d P Q →
      inv P = inv Q)
    (hsep : Function.Injective (fun i => inv (F i))) :
    (k : ℕ∞) ≤ platonicCount d := by
  refine le_platonicCount d k F ?_
  intro i j hij hsim
  exact hij (hsep (hinv (F i) (F j) hsim))

end LeanEval.Geometry.PlatonicClassification
