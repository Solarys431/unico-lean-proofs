/-
Copyright (c) 2026 Daniele Cappello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Cappello
-/
import Mathlib

/-!
# Feuerbach's theorem (Wiedijk #29) — the challenge statement

In any triangle, the nine-point circle is internally tangent to the incircle
(`feuerbach_insphere`) and externally tangent to each of the three excircles
(`feuerbach_exsphere`), for every triangle of a two-dimensional real Euclidean plane.

Every symbol here is mathlib's own — `Triangle`, `insphere`, `exsphere`, `ninePointCircle`,
`Sphere.IsIntTangent`, `Sphere.IsExtTangent` — so a reviewer trusts the statement by reading
these few lines. Run Comparator to check that `Solution.lean` proves these exact statements,
using only the standard axioms.
-/

open EuclideanGeometry Affine Module

namespace FeuerbachMain

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

theorem feuerbach_insphere (t : Triangle ℝ P) :
    t.insphere.IsIntTangent t.ninePointCircle := by
  sorry

theorem feuerbach_exsphere (t : Triangle ℝ P) (i : Fin 3) :
    (t.exsphere {i}).IsExtTangent t.ninePointCircle := by
  sorry

end FeuerbachMain
