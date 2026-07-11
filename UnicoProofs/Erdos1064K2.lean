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
# Erdős Problem 1064, variant k2: infinitely many `n` with `φ(n) < φ(n − φ(n))`

*Statement source:* [google-deepmind/formal-conjectures, `ErdosProblems/1064.lean`,
theorem `erdos_1064.variants.k2`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1064.lean)
— tagged `research solved`, with no `formal_proof` recorded at the time of writing
(July 11, 2026).

*Reference (informal solution):* A. Grytczuk, F. Luca, M. Wójtowicz,
*A conjecture of Erdős concerning inequalities for the Euler totient function*,
Publ. Math. Debrecen (2001). See also [erdosproblems.com/1064](https://www.erdosproblems.com/1064).

## Proof idea

The family `n = 30 * 2^k` works for every `k`:
`φ(30 * 2^k) = 8 * 2^k`, hence `n − φ(n) = 22 * 2^k = 2^(k+1) * 11`,
whose totient is `10 * 2^k`. Since `8 * 2^k < 10 * 2^k`, the set is infinite.

## Provenance (AI disclosure)

The proof below was produced on July 11, 2026 by **Aristotle** (Harmonic AI),
prompted with the statement and the literature reference, within a pipeline
orchestrated by **Claude** (Anthropic) as part of the NOUS/UNICO project of Solarys431. It was verified locally with the Lean 4 kernel
(toolchain `v4.32.0-rc1`, mathlib `v4.32.0-rc1`): no `sorry`, no additional
axioms, no `native_decide`. Label: LLM-generated.

**Prior art** (found in a search conducted July 11, 2026, before any upstream
submission): an equivalent constructive proof of this statement, via the same
witness family `15 * 2^(k+1)`, was committed on **July 8, 2026** to
[rjwalters/lean-genius](https://github.com/rjwalters/lean-genius)
(`proofs/Proofs/Erdos1064Problem.lean`, theorem `glw_infinitely_many`), inside
a file that also states an unrelated axiom for the density half of the problem
(the infinitude theorem itself does not depend on it). The proof in this file
was produced independently; priority belongs to lean-genius.

To re-verify: `lake exe cache get && lake build`.
-/

/-- For the family `n = 30 * 2^k = 2^(k+1) * 15`, `φ(n) = 8 * 2^k`. -/
lemma phi_family (k : ℕ) : Nat.totient (30 * 2 ^ k) = 8 * 2 ^ k := by
  have h1 : 30 * 2 ^ k = 2 ^ (k + 1) * 15 := by ring
  rw [h1, Nat.totient_mul (by norm_num), Nat.totient_prime_pow Nat.prime_two (by omega),
    show Nat.totient 15 = 8 from rfl, Nat.add_sub_cancel]
  ring

/-- For the family `n = 30 * 2^k`, `n − φ(n) = 22 * 2^k = 2^(k+1) * 11`. -/
lemma sub_family (k : ℕ) : 30 * 2 ^ k - Nat.totient (30 * 2 ^ k) = 22 * 2 ^ k := by
  rw [phi_family]; omega

/-- `φ(22 * 2^k) = 10 * 2^k`. -/
lemma phi_sub_family (k : ℕ) : Nat.totient (22 * 2 ^ k) = 10 * 2 ^ k := by
  rw [show 22 * 2 ^ k = 2 ^ (k + 1) * 11 by ring, Nat.totient_mul (by norm_num),
    Nat.totient_prime_pow (by norm_num) (by omega), show Nat.totient 11 = 10 from rfl,
    Nat.add_sub_cancel]
  ring

/-- **Erdős 1064, variant k2.** There exist infinitely many `n` such that
`φ(n) < φ(n − φ(n))`. Matches `erdos_1064.variants.k2` in
google-deepmind/formal-conjectures (there stated with `open Nat` notation `φ`,
which is notation for `Nat.totient`). -/
theorem erdos_1064_k2 :
    {n : ℕ | Nat.totient n < Nat.totient (n - Nat.totient n)}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 30 * 2 ^ k)
  · intro a b hab
    simp only at hab
    have : (2 : ℕ) ^ a = 2 ^ b := by omega
    exact Nat.pow_right_injective (le_refl 2) this
  · intro k
    simp only [Set.mem_setOf_eq]
    rw [sub_family, phi_family, phi_sub_family]
    have : (0 : ℕ) < 2 ^ k := pow_pos (by norm_num) k
    omega
