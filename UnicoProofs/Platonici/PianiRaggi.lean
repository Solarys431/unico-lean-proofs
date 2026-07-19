import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FanVertice
import UnicoProofs.Platonici.PianoDaiRaggi
import UnicoProofs.Platonici.PianiComuni

/-!
RIGIDITÀ — IL PIANO DAI RAGGI, NON DAI PUNTI (19 lug 2026).

Correzione di un dettaglio nel modulo precedente: il «punto» che
rappresenta uno spigolo è una scelta classica, dunque due ventagli
possono sceglierne di diversi ANCHE quando gli spigoli coincidono come
insiemi. Quel che davvero coincide sono i RAGGI (gate 2), e per il piano
tanto basta: moltiplicare un generatore per uno scalare non nullo non
cambia lo span. Qui la forma corretta, che dipende solo dai raggi.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- Riscalare i generatori non cambia lo span (forma generica). -/
theorem span_pair_smul_gen {u w : E 3} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Submodule.span ℝ ({a • u, b • w} : Set (E 3)) =
      Submodule.span ℝ ({u, w} : Set (E 3)) := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    rcases hz with hz | hz
    · rw [hz]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl rfl))
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl))
  · rw [Submodule.span_le]
    intro z hz
    rcases hz with hz | hz
    · rw [hz]
      have hmem : a • u ∈ Submodule.span ℝ
          ({a • u, b • w} : Set (E 3)) :=
        Submodule.subset_span (Or.inl rfl)
      have hsmul : a⁻¹ • (a • u) ∈ Submodule.span ℝ
          ({a • u, b • w} : Set (E 3)) := Submodule.smul_mem _ _ hmem
      simpa [smul_smul, inv_mul_cancel₀ ha] using hsmul
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have hmem : b • w ∈ Submodule.span ℝ
          ({a • u, b • w} : Set (E 3)) :=
        Submodule.subset_span (Or.inr rfl)
      have hsmul : b⁻¹ • (b • w) ∈ Submodule.span ℝ
          ({a • u, b • w} : Set (E 3)) := Submodule.smul_mem _ _ hmem
      simpa [smul_smul, inv_mul_cancel₀ hb] using hsmul

/-- Il vettore dal vertice al punto dello spigolo è un multiplo positivo
del raggio. -/
theorem punto_sub_eq_smul_dir {P : ConvexPolytope 3} {v : E 3} {q : ℕ}
    (D : P.asFinite.CyclicVertexData v q) (i : Fin q) :
    punto P.asFinite v D i - v =
      ‖punto P.asFinite v D i - v‖ • dir P.asFinite v D i := by
  classical
  have hne : punto P.asFinite v D i - v ≠ 0 :=
    sub_ne_zero.mpr (punto_spec P.asFinite v D i).1
  have hnorm : ‖punto P.asFinite v D i - v‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  show punto P.asFinite v D i - v =
    ‖punto P.asFinite v D i - v‖ •
      (‖punto P.asFinite v D i - v‖⁻¹ • (punto P.asFinite v D i - v))
  rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]

/-- La norma del vettore al punto dello spigolo è positiva. -/
theorem norma_punto_pos {P : ConvexPolytope 3} {v : E 3} {q : ℕ}
    (D : P.asFinite.CyclicVertexData v q) (i : Fin q) :
    ‖punto P.asFinite v D i - v‖ ≠ 0 :=
  norm_ne_zero_iff.mpr (sub_ne_zero.mpr (punto_spec P.asFinite v D i).1)

/-- **IL PIANO DELLA FACCETTA DIPENDE SOLO DAI DUE RAGGI**: gli span dei
vettori ai punti degli spigoli coincidono con lo span dei raggi. -/
theorem span_punti_eq_span_raggi {P : ConvexPolytope 3} {v : E 3} {q : ℕ}
    (D : P.asFinite.CyclicVertexData v q) (i j : Fin q) :
    Submodule.span ℝ
        ({punto P.asFinite v D i - v, punto P.asFinite v D j - v} :
          Set (E 3)) =
      Submodule.span ℝ
        ({dir P.asFinite v D i, dir P.asFinite v D j} : Set (E 3)) := by
  rw [punto_sub_eq_smul_dir D i, punto_sub_eq_smul_dir D j]
  exact span_pair_smul_gen (norma_punto_pos D i) (norma_punto_pos D j)

/-- **I PIANI OMOLOGHI COINCIDONO, DAI SOLI RAGGI**. -/
theorem piano_faccetta_comune_dai_raggi {P Q : ConvexPolytope 3}
    {v : E 3} {q : ℕ}
    (DP : P.asFinite.CyclicVertexData v q)
    (DQ : Q.asFinite.CyclicVertexData v q)
    (i j : Fin q)
    (hxP : punto P.asFinite v DP i ∈ DP.faccetta i)
    (hyP : punto P.asFinite v DP j ∈ DP.faccetta i)
    (hxQ : punto Q.asFinite v DQ i ∈ DQ.faccetta i)
    (hyQ : punto Q.asFinite v DQ j ∈ DQ.faccetta i)
    (hvP : v ∈ DP.faccetta i) (hvQ : v ∈ DQ.faccetta i)
    (hindP : LinearIndependent ℝ
      ![punto P.asFinite v DP i - v, punto P.asFinite v DP j - v])
    (hindQ : LinearIndependent ℝ
      ![punto Q.asFinite v DQ i - v, punto Q.asFinite v DQ j - v])
    (hrankP : Module.finrank ℝ (vectorSpan ℝ (DP.faccetta i)) = 2)
    (hrankQ : Module.finrank ℝ (vectorSpan ℝ (DQ.faccetta i)) = 2)
    (hdir : dir P.asFinite v DP = dir Q.asFinite v DQ) :
    affineSpan ℝ (DP.faccetta i) = affineSpan ℝ (DQ.faccetta i) := by
  refine affineSpan_eq_of_raggi_eq hvP hxP hyP hvQ hxQ hyQ
    hindP hindQ hrankP hrankQ ?_
  rw [span_punti_eq_span_raggi DP i j, span_punti_eq_span_raggi DQ i j,
    hdir]

end LeanEval.Geometry.PlatonicClassification
