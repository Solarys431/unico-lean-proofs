import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.LowerBound
import UnicoProofs.Platonici.Simplesso
import UnicoProofs.Platonici.Ortoplesse
import UnicoProofs.Platonici.OrtoplesseFacce
import UnicoProofs.Platonici.Ipercubo

/-!
IL LOWER BOUND INCONDIZIONATO `3 ≤ platonicCount d` (19 lug 2026).

Con le tre costruzioni certificate — simplesso (d+1 vertici), ortoplesse
(2d), ipercubo (2ᵈ), tutte `IsRegular` in ogni dimensione — il framework
`tre_le_platonicCount` si applica e chiude il lato basso del benchmark per
`d ≥ 5`, SENZA ipotesi ausiliarie.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **IL LOWER BOUND, INCONDIZIONATO.** Per `d ≥ 5` esistono almeno tre
politopi regolari a meno di similarità. -/
theorem three_le_platonicCount (d : ℕ) (hd : 5 ≤ d) :
    (3 : ℕ∞) ≤ platonicCount d := by
  have hd1 : 1 ≤ d := by omega
  exact tre_le_platonicCount d hd
    ⟨simplesso d hd1, simplesso_mem_regularPolytopes d hd1⟩
    ⟨ortoplesse d hd1, ortoplesse_mem_regularPolytopes d hd1⟩
    ⟨ipercubo d hd1, ipercubo_mem_regularPolytopes d hd1⟩
    (card_simplesso d hd1) (card_ortoplesse d hd1) (card_ipercubo d hd1)

end LeanEval.Geometry.PlatonicClassification
