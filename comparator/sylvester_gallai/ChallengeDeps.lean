/-
Copyright (c) 2026 Daniele Cappello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Cappello
-/
import Mathlib

/-!
# Sylvester–Gallai — trusted definitions

The two definitions the statement rests on. A reviewer needs to read only this file
(and `Challenge.lean`) to trust the claim: `lineThrough a b` is the affine line through
two points, and `IsOrdinaryLine S a b` says the line through `a` and `b` meets `S` in
exactly those two points. The proof in `Solution.lean` consumes these definitions
unchanged, so it cannot quietly weaken them.
-/

open RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace SylvesterGallai

/-- The line through two points. -/
noncomputable def lineThrough (a b : P) : AffineSubspace ℝ P := affineSpan ℝ {a, b}

/-- A line is **ordinary** with respect to `S` if it contains exactly two points of `S`. -/
def IsOrdinaryLine (S : Set P) (a b : P) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ ∀ c ∈ S, c ∈ lineThrough (V := V) a b → c = a ∨ c = b

end SylvesterGallai
