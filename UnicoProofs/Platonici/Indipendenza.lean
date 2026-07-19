import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.Trasportatore
import UnicoProofs.Platonici.RelazioniCoxeter
import UnicoProofs.Platonici.Iperpiano
import UnicoProofs.Platonici.Normali
import UnicoProofs.Platonici.FormulaRiflessione

/-!
MOTORE COXETER, PASSO 25 — I NORMALI SONO INDIPENDENTI, LA GRAM È
DEFINITA POSITIVA (19 lug 2026).

Il fatto strutturale che rende la matrice di Gram un oggetto rigido:
gli `n` normali `αᵢ` sono linearmente indipendenti.

La dimostrazione non passa dalla geometria fine, ma da una
BIORTOGONALITÀ già disponibile: `rᵢ` fissa tutte le facce della bandiera
tranne quella di rango `i`, quindi il centroide `c_k` sta nell'iperpiano
di `rᵢ` per ogni `k ≠ i`, e non ci sta per `k = i` (altrimenti `rᵢ`
fisserebbe anche la faccia di rango `i`, e non sarebbe la mossa).

In formule, traslando nell'origine il centroide del corpo:

    ⟪αᵢ, c_k − c_top⟫ = 0   per k ≠ i,     ≠ 0   per k = i.

Una famiglia biortogonale a una famiglia di vettori è libera.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- **Biortogonalità ⟹ indipendenza lineare.** Se `⟪α i, v k⟫` si annulla
fuori dalla diagonale e non si annulla sulla diagonale, la famiglia `α`
è linearmente indipendente. -/
theorem linearIndependent_of_biorthogonal {ι : Type*} [Fintype ι]
    [DecidableEq ι] (α v : ι → E n)
    (hdiag : ∀ i, ⟪α i, v i⟫ ≠ (0 : ℝ))
    (hoff : ∀ i k, k ≠ i → ⟪α i, v k⟫ = (0 : ℝ)) :
    LinearIndependent ℝ α := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have happ := congrArg (fun w : E n => (⟪w, v i⟫ : ℝ)) hg
  simp only [inner_zero_left, sum_inner] at happ
  have hterm : ∀ k, (⟪g k • α k, v i⟫ : ℝ) =
      if k = i then g i * ⟪α i, v i⟫ else 0 := by
    intro k
    rw [real_inner_smul_left]
    by_cases hk : k = i
    · subst hk
      simp
    · rw [hoff k i (Ne.symm hk), mul_zero, if_neg hk]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)] at happ
  rw [Finset.sum_ite_eq' Finset.univ i
    (fun _ => g i * ⟪α i, v i⟫)] at happ
  simp only [Finset.mem_univ, if_true] at happ
  exact (mul_eq_zero.mp happ).resolve_right (hdiag i)

/-- La matrice di Gram di una famiglia libera è definita positiva:
la forma quadratica associata si annulla solo sul vettore nullo. -/
theorem gram_definita_positiva {ι : Type*} [Fintype ι] (α : ι → E n)
    (hind : LinearIndependent ℝ α) (g : ι → ℝ)
    (hzero : ∀ j, ∑ i, g i * ⟪α i, α j⟫ = (0 : ℝ)) :
    ∀ i, g i = 0 := by
  have hsum : (∑ i, g i • α i) = 0 := by
    have hnorm : (⟪∑ i, g i • α i, ∑ i, g i • α i⟫ : ℝ) = 0 := by
      rw [sum_inner]
      refine Finset.sum_eq_zero ?_
      intro j _
      rw [real_inner_smul_left, inner_sum]
      have : (∑ i, (⟪α j, g i • α i⟫ : ℝ)) = ∑ i, g i * ⟪α i, α j⟫ := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [real_inner_smul_right, real_inner_comm]
      rw [this, hzero j, mul_zero]
    exact inner_self_eq_zero.mp hnorm
  exact (Fintype.linearIndependent_iff.mp hind) g hsum

end LeanEval.Geometry.PlatonicClassification
