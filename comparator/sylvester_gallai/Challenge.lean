/-
Copyright (c) 2026 Daniele Cappello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Cappello
-/
import ChallengeDeps

/-!
# Sylvester–Gallai — the challenge statement

A finite set of points, not all collinear, admits an ordinary line: a line through
exactly two of them. Stated in an arbitrary real inner product space with its affine
torsor, with no dimension hypothesis; the classical plane is `EuclideanSpace ℝ (Fin 2)`.

The proof is replaced by `sorry` here on purpose. Run Comparator to check that
`Solution.lean` proves this exact statement, using only the standard axioms.
-/

open RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace SylvesterGallai

theorem sylvester_gallai (S : Set P) (hfin : S.Finite) (hncol : ¬ Collinear ℝ S) :
    ∃ a ∈ S, ∃ b ∈ S, IsOrdinaryLine (V := V) S a b := by
  sorry

end SylvesterGallai
