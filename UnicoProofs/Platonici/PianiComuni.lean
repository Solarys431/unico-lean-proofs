import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FanVertice
import UnicoProofs.Platonici.PianoDaiRaggi
import UnicoProofs.Platonici.VerticeAdiacente

/-!
RIGIDITÀ — I PIANI DEL VENTAGLIO SONO COMUNI (19 lug 2026).

Il mattone che permette di proseguire l'induzione oltre il primo vertice.
Ogni faccetta del ventaglio a `v` è delimitata da due spigoli consecutivi,
dunque contiene `v` e due punti su due raggi consecutivi. Se i raggi
coincidono nei due politopi (gate 2) e coincidono anche i passi
(diametro), allora quei punti sono gli stessi, e per
`affineSpan_eq_of_raggi_eq` le due faccette omologhe GIACCIONO NELLO
STESSO PIANO. Non serve identificarle come insiemi: per il seguito basta
il piano, ed è ciò che fissa l'orientazione del ventaglio al vertice
successivo.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- I due estremi non banali degli spigoli che delimitano la faccetta `i`
del ventaglio: il punto sullo spigolo `i` e quello sullo spigolo
precedente stanno entrambi nella faccetta `i`. -/
theorem punti_nella_faccetta {P : ConvexPolytope 3} {v : E 3} {q : ℕ}
    (D : P.asFinite.CyclicVertexData v q) (i : Fin q) :
    punto P.asFinite v D i ∈ D.faccetta i := by
  exact (punto_spec P.asFinite v D i).2.1

/-- Il punto dello spigolo, riscritto sul raggio. -/
theorem punto_su_raggio {P : ConvexPolytope 3} {v : E 3} {q : ℕ}
    (D : P.asFinite.CyclicVertexData v q) (i : Fin q) :
    punto P.asFinite v D i =
      v + ‖punto P.asFinite v D i - v‖ • dir P.asFinite v D i := by
  classical
  have hne : punto P.asFinite v D i - v ≠ 0 := by
    have h := (punto_spec P.asFinite v D i).1
    exact sub_ne_zero.mpr h
  have hnorm : ‖punto P.asFinite v D i - v‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  show punto P.asFinite v D i =
    v + ‖punto P.asFinite v D i - v‖ •
      (‖punto P.asFinite v D i - v‖⁻¹ • (punto P.asFinite v D i - v))
  rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  abel

/-- **I PIANI OMOLOGHI COINCIDONO**: stessi raggi e stessi punti su due
raggi consecutivi ⟹ le due faccette del ventaglio stanno nello stesso
piano affine. -/
theorem piano_faccetta_comune {P Q : ConvexPolytope 3} {v : E 3} {q : ℕ}
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
    (hpunti_i : punto P.asFinite v DP i = punto Q.asFinite v DQ i)
    (hpunti_j : punto P.asFinite v DP j = punto Q.asFinite v DQ j) :
    affineSpan ℝ (DP.faccetta i) = affineSpan ℝ (DQ.faccetta i) := by
  refine affineSpan_eq_of_raggi_eq hvP hxP hyP hvQ hxQ hyQ
    hindP hindQ hrankP hrankQ ?_
  rw [hpunti_i, hpunti_j]

end LeanEval.Geometry.PlatonicClassification
