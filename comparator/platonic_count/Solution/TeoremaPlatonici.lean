import Mathlib
import Challenge
import Solution.Chiusura2
import Solution.ConteggioRegolare

/-!
# I SOLIDI PLATONICI SONO CINQUE

Il teorema del benchmark, in dimensione 3:

    platonicCount 3 = 5

cioè: i politopi regolari di ℝ³, a meno di similarità, sono esattamente
cinque.

La dimostrazione, tutta kernel-certificata, si articola in due metà:

**MINORANTE** (≥ 5): i cinque solidi platonici, costruiti esplicitamente
con le loro coordinate, sono regolari e a due a due non simili.

**MAGGIORANTE** (≤ 5): ogni politopo regolare ha un tipo ciclico (p,q)
che soddisfa la disuguaglianza di Schläfli, dunque è una delle cinque
coppie; e due politopi regolari dello stesso tipo sono simili (RIGIDITÀ).

La rigidità, che è la parte difficile, procede per soli invarianti
canonici:

    fattore di scala dai diametri degli spigoli
      → omotetia (che non altera i raggi)
      → registrazione dalla matrice di Gram del ventaglio
      → isometria (che applica la sola parte lineare)
      → ventagli allineati al vertice registrato
      → propagazione dell'allineamento lungo il grafo dei vertici
      → uguaglianza degli insiemi di vertici
      → uguaglianza degli inviluppi convessi
      → similarità.

Non usa l'identificazione delle faccette, né il teorema di Cauchy, né il
generatore orbitale come lato, né punti scelti sugli spigoli.
-/

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **I SOLIDI PLATONICI SONO CINQUE.** -/
theorem platonicCount_three : platonicCount 3 = 5 :=
  platonicCount3_da_rigidita_regolare
    (fun P Q p q hregP hregQ hP hQ => by
      haveI : NeZero q := ⟨by
        have hq : 3 ≤ q := hP.2.2.1
        omega⟩
      exact rigidita_stesso_tipo P Q hP hQ hregP hregQ)

end LeanEval.Geometry.PlatonicClassification
