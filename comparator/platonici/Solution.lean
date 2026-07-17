/-
Copyright (c) 2026 Daniele Cappello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Cappello

The full kernel-checked proof of the Platonic classification, in 25 modules
under `Solution/`. `cyclicallyRegular_schlafli` is proved in
`Solution.Classificazione`; the existence witness is the regular tetrahedron
from `Solution.TetraedroStadio2`.
-/
import Solution.Classificazione
import Solution.TetraedroStadio2

namespace PlatoniciMain

/-- Non-vacuity, witnessed by the regular tetrahedron. -/
theorem exists_cyclicallyRegular :
    ∃ P : FiniteConvexPolytope (EuclideanSpace ℝ (Fin 3)),
      P.IsCyclicallyRegularOfType 3 3 :=
  ⟨tetraedro, tetraedro_cyclicallyRegular⟩

end PlatoniciMain
