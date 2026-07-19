import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.MinoranteGenerico
import UnicoProofs.Platonici.Cardinalita
import UnicoProofs.Platonici.InvarianteSimilarita

/-!
IL CONFEZIONAMENTO DEL LOWER BOUND `3 ≤ platonicCount d` (19 lug 2026).

Il montaggio finale del lato basso per `d ≥ 5`: date tre famiglie regolari
con i tre numeri di vertici distinti `d+1`, `2d`, `2ᵈ` (simplesso, ortoplesse,
ipercubo), la cardinalità dei vertici — invariante per similarità — le separa
in tre classi distinte, dunque `3 ≤ platonicCount d`.

Questo teorema è INCONDIZIONATO nella struttura ma prende i tre politopi in
ipotesi: appena le tre costruzioni sono certificate come `IsRegular`, si
applica e chiude il lower bound.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **Il lower bound da tre testimoni con vertici distinti.** -/
theorem tre_le_platonicCount (d : ℕ) (hd : 5 ≤ d)
    (Ps Po Pi : regularPolytopes d)
    (hs : (Ps : ConvexPolytope d).vertices.card = d + 1)
    (ho : (Po : ConvexPolytope d).vertices.card = 2 * d)
    (hi : (Pi : ConvexPolytope d).vertices.card = 2 ^ d) :
    (3 : ℕ∞) ≤ platonicCount d := by
  classical
  -- l'invariante: il numero di vertici
  let inv : regularPolytopes d → ℕ := fun P => (P : ConvexPolytope d).vertices.card
  -- è invariante per similarità
  have hinv : ∀ P Q : regularPolytopes d, regularSimilar d P Q → inv P = inv Q := by
    intro P Q hPQ
    exact (vertices_card_of_similar hPQ).symm
  -- la famiglia dei tre testimoni
  let F : Fin 3 → regularPolytopes d := ![Ps, Po, Pi]
  -- l'invariante li separa: card distinte d+1, 2d, 2^d
  have hsep : Function.Injective (fun i => inv (F i)) := by
    have hval : ∀ i : Fin 3, inv (F i) = ![d + 1, 2 * d, 2 ^ d] i := by
      intro i
      fin_cases i
      · exact hs
      · exact ho
      · exact hi
    have hcard := card_tre_iniettiva d hd
    intro i j hij
    apply hcard
    simp only at hij ⊢
    rw [← hval i, ← hval j]
    exact hij
  -- il motore del minorante
  have h := le_platonicCount_di_invariante d 3 F inv hinv hsep
  simpa using h

end LeanEval.Geometry.PlatonicClassification
