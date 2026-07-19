import Mathlib
import Challenge
import Solution.FanVertice
import Solution.LatoSemipiano
import Solution.BandieraSpigolo

/-!
RIGIDITÀ — IL VERTICE ADIACENTE È DETERMINATO (19 lug 2026).

Il cuore della strategia dei vertici. Lo spigolo che esce da `v` lungo il
raggio `dir i` è il segmento `[v, v + t • dir i]`, e poiché `dir` è
unitario il suo DIAMETRO è esattamente `t`. Dunque due politopi che
hanno, allo stesso vertice, gli stessi raggi (gate 2) e spigoli dello
stesso diametro (`spigoli_congrui`, dopo la normalizzazione di scala)
hanno anche gli stessi vertici adiacenti. Nessun riferimento a `ell`:
la falla 11 resta fuori dalla porta.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- Il diametro di un segmento è la distanza fra i suoi estremi. -/
theorem diam_segment (x y : E 3) :
    Metric.diam (segment ℝ x y) = dist x y := by
  classical
  have hseg : segment ℝ x y = convexHull ℝ ({x, y} : Set (E 3)) := by
    rw [convexHull_pair]
  rw [hseg, convexHull_diam, Metric.diam_pair]

/-- **IL DIAMETRO DELLO SPIGOLO È IL PASSO**: se lo spigolo uscente da `v`
è `[v, v + t • u]` con `u` unitario e `t > 0`, allora il diametro vale
`t`. -/
theorem diam_spigolo_eq (v u : E 3) (hu : ‖u‖ = 1) {t : ℝ} (ht : 0 < t) :
    Metric.diam (segment ℝ v (v + t • u)) = t := by
  rw [diam_segment]
  rw [dist_eq_norm]
  have h1 : v - (v + t • u) = -(t • u) := by
    abel
  rw [h1, norm_neg, norm_smul, hu, mul_one,
    Real.norm_of_nonneg (le_of_lt ht)]

/-- **IL PASSO È DETERMINATO DAL DIAMETRO**: due rappresentazioni dello
stesso tipo di spigolo con lo stesso diametro hanno lo stesso passo. -/
theorem passo_eq_of_diam_eq {v u : E 3} (hu : ‖u‖ = 1)
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (hdiam : Metric.diam (segment ℝ v (v + t • u)) =
      Metric.diam (segment ℝ v (v + s • u))) :
    t = s := by
  rw [diam_spigolo_eq v u hu ht, diam_spigolo_eq v u hu hs] at hdiam
  exact hdiam

/-- **IL VERTICE ADIACENTE COINCIDE**: stesso vertice, stesso raggio,
spigoli di uguale diametro ⟹ stesso vertice adiacente. -/
theorem vertice_adiacente_eq {v uP uQ wP wQ : E 3} {tP tQ : ℝ}
    (huP : ‖uP‖ = 1) (huQ : ‖uQ‖ = 1)
    (htP : 0 < tP) (htQ : 0 < tQ)
    (hwP : wP = v + tP • uP) (hwQ : wQ = v + tQ • uQ)
    (hraggi : uP = uQ)
    (hdiam : Metric.diam (segment ℝ v wP) = Metric.diam (segment ℝ v wQ)) :
    wP = wQ := by
  subst hraggi
  subst hwP
  subst hwQ
  have ht : tP = tQ := by
    rw [diam_spigolo_eq v uP huP htP, diam_spigolo_eq v uP huP htQ] at hdiam
    exact hdiam
  rw [ht]

/-- **LO SPIGOLO DEL VENTAGLIO È DETERMINATO**: con lo stesso vertice, lo
stesso raggio e spigoli di uguale diametro, i due spigoli coincidono come
insiemi (e dunque hanno gli stessi estremi, cioè lo stesso vertice
adiacente). -/
theorem spigolo_del_fan_eq (P Q : ConvexPolytope 3) {p q : ℕ}
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (hQ : Q.asFinite.IsCyclicallyRegularOfType p q)
    {v : E 3} (hvP : v ∈ P.vertices) (hvQ : v ∈ Q.vertices)
    (DP : P.asFinite.CyclicVertexData v q)
    (DQ : Q.asFinite.CyclicVertexData v q)
    (i : Fin q)
    (hraggi : dir P.asFinite v DP i = dir Q.asFinite v DQ i)
    (hdiam : Metric.diam
        (DP.faccetta i ∩ DP.faccetta (finRotate q i)) =
      Metric.diam (DQ.faccetta i ∩ DQ.faccetta (finRotate q i))) :
    DP.faccetta i ∩ DP.faccetta (finRotate q i) =
      DQ.faccetta i ∩ DQ.faccetta (finRotate q i) := by
  classical
  obtain ⟨tP, htP, hsegP⟩ := spigolo_eq_segmento_sul_raggio P hP hvP DP i
  obtain ⟨tQ, htQ, hsegQ⟩ := spigolo_eq_segmento_sul_raggio Q hQ hvQ DQ i
  rw [hsegP, hsegQ] at hdiam ⊢
  rw [diam_spigolo_eq v _ (dir_unitaria P.asFinite v DP i) htP,
    diam_spigolo_eq v _ (dir_unitaria Q.asFinite v DQ i) htQ] at hdiam
  rw [hdiam, hraggi]

end LeanEval.Geometry.PlatonicClassification
