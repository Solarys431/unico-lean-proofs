import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FlagAdiacente
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.MossaInvolutiva
import UnicoProofs.Platonici.Equivarianza
import UnicoProofs.Platonici.Trasportatore
import UnicoProofs.Platonici.Commutazione

/-!
MOTORE COXETER, PASSO 11 — LA RELAZIONE LONTANA SULLE BANDIERE
(19 lug 2026).

Per ranghi non adiacenti (`i + 2 ≤ j`) il prodotto `rᵢ rⱼ` applicato due
volte fissa la bandiera base: il calcolo insegue le quattro applicazioni
attraverso l'equivarianza, riduce con la commutazione delle mosse e
chiude con l'involutività. Ogni ingrediente è già certificato; quando la
libertà dell'azione sarà in cassaforte, questo enunciato si promuoverà
alla relazione di Coxeter `(rᵢ rⱼ)² = 1` nel gruppo di simmetria.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- **La relazione lontana sulle bandiere**: per `i + 2 ≤ j`,
`rᵢ rⱼ rᵢ rⱼ` riporta la bandiera base in sé. -/
theorem simpleReflection_far_comm_fixes (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) {i j : Fin n}
    (hij : (i : ℕ) + 2 ≤ (j : ℕ)) :
    mapFlag P (simpleReflection_isSymmetry P hreg F i)
      (mapFlag P (simpleReflection_isSymmetry P hreg F j)
        (mapFlag P (simpleReflection_isSymmetry P hreg F i)
          (mapFlag P (simpleReflection_isSymmetry P hreg F j) F))) = F := by
  rw [simpleReflection_mapFlag P hreg F j,
    mapFlag_adjacentFlag P hreg.1
      (simpleReflection_isSymmetry P hreg F i) F j,
    simpleReflection_mapFlag P hreg F i,
    mapFlag_adjacentFlag P hreg.1
      (simpleReflection_isSymmetry P hreg F j)
      (adjacentFlag P hreg.1 F i) j,
    mapFlag_adjacentFlag P hreg.1
      (simpleReflection_isSymmetry P hreg F j) F i,
    simpleReflection_mapFlag P hreg F j,
    adjacentFlag_comm P hreg.1 F hij,
    adjacentFlag_involutive P hreg.1 (adjacentFlag P hreg.1 F i) j]
  exact simpleReflection_swaps P hreg F i

end LeanEval.Geometry.PlatonicClassification
