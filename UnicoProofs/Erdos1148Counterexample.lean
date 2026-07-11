/-
Copyright 2026 Solarys431.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib

/-!
# Erdős Problem 1148: the counterexample `6563`

*Statement source:* [google-deepmind/formal-conjectures, `ErdosProblems/1148.lean`]
(https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1148.lean).
Erdős 1148 asks whether every large integer `n` can be written as `n = x² + y² − z²`
with `max(x², y², z²) ≤ n`. The largest integer known **not** to be so representable
is `6563`; this file certifies that fact.

## Trust level: compiler, not pure kernel

The proof is closed by `native_decide`, which compiles the `Decidable` instance to
native code and trusts the compiler and the `Lean.ofReduceBool` axiom, in addition to
the kernel. It is therefore **not** a pure-kernel proof: it depends on
`Lean.ofReduceBool`. We state this explicitly rather than hide it. A pure-kernel
`decide` does not reduce here (the nested `Finset` decidability instance gets stuck on
`List.decidableBEx`); a kernel-only proof would need a reflection-friendly instance or a
structured argument, and is left as future work.

## Provenance (AI disclosure)

Produced within the NOUS/UNICO pipeline (orchestrated by Claude, Anthropic) on
July 11, 2026, and verified locally (Lean `v4.32.0-rc1`, mathlib `v4.32.0-rc1`).
Label: LLM-generated. The `Decidable` instance is copied verbatim from the
formal-conjectures source file.

To re-verify: `lake exe cache get && lake build`.
-/

namespace Erdos1148

/-- `n` is representable as `x² + y² − z²` with `max(x², y², z²) ≤ n`
(natural-number truncated subtraction, exactly as in the source file). -/
def Erdos1148Prop (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧ x ^ 2 ≤ n ∧ y ^ 2 ≤ n ∧ z ^ 2 ≤ n

instance (n : ℕ) : Decidable (Erdos1148Prop n) :=
  decidable_of_iff
    (∃ x ∈ Finset.range (Nat.sqrt n + 1), ∃ y ∈ Finset.range (Nat.sqrt n + 1),
      ∃ z ∈ Finset.range (Nat.sqrt n + 1),
      n = x ^ 2 + y ^ 2 - z ^ 2 ∧ x ^ 2 ≤ n ∧ y ^ 2 ≤ n ∧ z ^ 2 ≤ n)
    (by
      constructor
      · rintro ⟨x, -, y, -, z, -, h⟩; exact ⟨x, y, z, h⟩
      · rintro ⟨x, y, z, h1, h2, h3, h4⟩
        refine ⟨x, Finset.mem_range.mpr ?_, y, Finset.mem_range.mpr ?_,
                z, Finset.mem_range.mpr ?_, h1, h2, h3, h4⟩
        all_goals (simp only [Nat.lt_succ_iff]; exact Nat.le_sqrt'.mpr ‹_›))

/-- `6563` cannot be written as `x² + y² − z²` with `max(x², y², z²) ≤ 6563`. -/
theorem erdos_1148_counterexample_6563 : ¬ Erdos1148Prop 6563 := by
  native_decide

end Erdos1148
