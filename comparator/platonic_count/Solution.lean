/-
The two Platonic conjuncts proved against the lean-eval contract, in 122
modules under `Solution/`.

`platonicCount_three` is the exact count in dimension three: the lower bound
comes from the five explicit witnesses, the upper bound from rigidity (two
regular 3-polytopes of the same cyclic type are similar).

`platonicCount_two` is the plane: infinitely many regular polygons, separated
by their vertex count.
-/
import Solution.TeoremaPlatonici
import Solution.TeoremaDim2

namespace PlatoniciMain

open LeanEval.Geometry.PlatonicClassification

/-- The exact count of Platonic solids in dimension three. -/
theorem platonicCount_three : platonicCount 3 = 5 :=
  LeanEval.Geometry.PlatonicClassification.platonicCount_three

/-- In the plane there are infinitely many regular polytopes. -/
theorem platonicCount_two : platonicCount 2 = ⊤ :=
  LeanEval.Geometry.PlatonicClassification.platonicCount_two

end PlatoniciMain
