import Mathlib
import Challenge
import Solution.FanVertice
import Solution.LatoSemipiano
import Solution.VerticeAdiacente

/-!
RIGIDITÀ — IL RAGGIO NON DIPENDE DAL PUNTO SCELTO (19 lug 2026).

Il nodo del trasporto attraverso due trasformazioni, isolato da Daniele
con il principio: «non confrontare due ricostruzioni di un dato quando
puoi trasportare direttamente la proprietà necessaria».

Il `punto` che rappresenta uno spigolo è una scelta classica: il ventaglio
del politopo scalato può sceglierne uno diverso da `a • x`. Ma il RAGGIO
non dipende da quella scelta — tutti i punti dello spigolo diversi dal
vertice danno la stessa direzione unitaria — e i raggi sono l'unico dato
che la registrazione e l'allineamento consumano davvero.

Ne segue (osservazione di Daniele) che per `a > 0` l'omotetia non cambia
affatto i raggi:  a(x−v)/‖a(x−v)‖ = (x−v)/‖x−v‖.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- **IL RAGGIO NON DIPENDE DAL PUNTO SCELTO SULLO SPIGOLO**. -/
theorem dir_da_qualunque_punto (P : ConvexPolytope 3) {p q : ℕ}
    (h : P.asFinite.IsCyclicallyRegularOfType p q) {v : E 3}
    (hv : v ∈ P.vertices) (D : P.asFinite.CyclicVertexData v q)
    (i : Fin q) {x : E 3}
    (hx : x ∈ D.faccetta i ∩ D.faccetta (finRotate q i)) (hxv : x ≠ v) :
    ‖x - v‖⁻¹ • (x - v) = dir P.asFinite v D i := by
  classical
  obtain ⟨t, ht, hseg⟩ := spigolo_eq_segmento_sul_raggio P h hv D i
  rw [hseg] at hx
  -- x sta sul segmento, dunque x = v + s·t·dir con s ∈ [0,1]
  obtain ⟨α, β, hα, hβ, hαβ, hx'⟩ := hx
  have hxv' : x - v = (β * t) • dir P.asFinite v D i := by
    rw [← hx']
    have hone : α = 1 - β := by linarith
    rw [hone]
    rw [smul_add, smul_smul]
    module
  have hβpos : 0 < β := by
    rcases lt_or_eq_of_le hβ with hlt | heq
    · exact hlt
    · exfalso
      apply hxv
      have hβ0 : β = 0 := heq.symm
      have : x - v = 0 := by
        rw [hxv', hβ0, zero_mul, zero_smul]
      exact sub_eq_zero.mp this
  have hcoef : 0 < β * t := mul_pos hβpos ht
  rw [hxv', norm_smul, Real.norm_of_nonneg (le_of_lt hcoef),
    dir_unitaria P.asFinite v D i, mul_one, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hcoef), one_smul]

/-- **L'OMOTETIA NON CAMBIA I RAGGI** (forma vettoriale): per `a > 0`,
la direzione unitaria di `a • w` è quella di `w`. -/
theorem dir_smul_invariante {a : ℝ} (ha : 0 < a) {w : E 3} (hw : w ≠ 0) :
    ‖a • w‖⁻¹ • (a • w) = ‖w‖⁻¹ • w := by
  rw [norm_smul, Real.norm_of_nonneg (le_of_lt ha), smul_smul]
  have hnw : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hane : a ≠ 0 := ne_of_gt ha
  rw [mul_inv, mul_comm (a⁻¹ : ℝ) (‖w‖⁻¹), mul_assoc,
    inv_mul_cancel₀ hane, mul_one]

/-- **L'ISOMETRIA APPLICA LA SUA PARTE LINEARE AI RAGGI**. -/
theorem dir_isom_lineare (g : Isom 3) (v x : E 3) :
    ‖g x - g v‖⁻¹ • (g x - g v) =
      (g.linearIsometryEquiv) (‖x - v‖⁻¹ • (x - v)) := by
  classical
  have h := g.map_vsub x v
  have hlin : g x - g v = g.linearIsometryEquiv (x - v) := by
    rw [map_sub]
    simpa using h.symm
  rw [hlin, map_smul, g.linearIsometryEquiv.norm_map]

end LeanEval.Geometry.PlatonicClassification
