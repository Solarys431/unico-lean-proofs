import Mathlib
import Challenge
import Solution.SemipianoCanonico

/-!
RIGIDITÀ — IL RAGGIO NEL PIANO È UNICO (19 lug 2026).

La chiave per AGGIRARE la falla 11 invece di ripararla. Per proseguire
l'induzione al vertice successivo serve un secondo raggio comune; finora
lo si cercava identificando la faccetta come INSIEME, il che costringe a
usare `faccetta_determinata` e quindi a normalizzare i testimoni
d'orbita (falla 11). Ma non serve l'insieme: basta il PIANO della
faccetta, che è già certificato (`piano_faccetta_comune_dai_raggi`).

Infatti, dentro un piano assegnato, un vettore unitario è determinato da
(a) il coseno dell'angolo con un unitario noto del piano e (b) da quale
parte della retta di quest'ultimo si trova. Coseno e semipiano sono
entrambi dati canonici già in casa: la Gram e `SemipianoCanonico`.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope
open scoped RealInnerProductSpace

/-- Decomposizione di un vettore del piano lungo `u` e la sua normale. -/
theorem decomposizione_ortogonale {u n z : E 3}
    (hu : ‖u‖ = 1) (hn : ‖n‖ = 1) (hortho : ⟪u, n⟫ = 0)
    (hz : z ∈ Submodule.span ℝ ({u, n} : Set (E 3))) :
    z = ⟪u, z⟫ • u + ⟪n, z⟫ • n := by
  classical
  rw [Submodule.mem_span_pair] at hz
  obtain ⟨a, b, hab⟩ := hz
  have hnu : ⟪n, u⟫ = 0 := by
    rw [real_inner_comm]
    exact hortho
  have huu : ⟪u, u⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hnn : ⟪n, n⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have ha : ⟪u, z⟫ = a := by
    rw [← hab]
    simp [inner_add_right, real_inner_smul_right, huu, hortho, hu, hn]
  have hb : ⟪n, z⟫ = b := by
    rw [← hab]
    simp [inner_add_right, real_inner_smul_right, hnn, hnu, hu, hn]
  rw [ha, hb, ← hab]

/-- **UNICITÀ DEL RAGGIO NEL PIANO**: due vettori unitari del piano
generato da `u` e dalla sua normale `n`, che formano lo stesso angolo con
`u` e stanno dalla stessa parte rispetto alla retta di `u`, coincidono. -/
theorem raggio_nel_piano_unico {u n z z' : E 3}
    (hu : ‖u‖ = 1) (hn : ‖n‖ = 1) (hortho : ⟪u, n⟫ = 0)
    (hz : z ∈ Submodule.span ℝ ({u, n} : Set (E 3)))
    (hz' : z' ∈ Submodule.span ℝ ({u, n} : Set (E 3)))
    (hnormz : ‖z‖ = 1) (hnormz' : ‖z'‖ = 1)
    (hang : ⟪u, z⟫ = ⟪u, z'⟫)
    (hlato : 0 < ⟪n, z⟫ ∧ 0 < ⟪n, z'⟫) :
    z = z' := by
  classical
  have hdz := decomposizione_ortogonale hu hn hortho hz
  have hdz' := decomposizione_ortogonale hu hn hortho hz'
  -- le norme fissano il quadrato della componente normale
  have hnorm2 : ⟪u, z⟫ ^ 2 + ⟪n, z⟫ ^ 2 = ⟪u, z'⟫ ^ 2 + ⟪n, z'⟫ ^ 2 := by
    have hzz : ⟪z, z⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hnormz]; norm_num
    have hzz' : ⟪z', z'⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hnormz']; norm_num
    have huu : ⟪u, u⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hu]; norm_num
    have hnn : ⟪n, n⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hn]; norm_num
    have hnu : ⟪n, u⟫ = 0 := by rw [real_inner_comm]; exact hortho
    have e1 : ⟪z, z⟫ = ⟪u, z⟫ ^ 2 + ⟪n, z⟫ ^ 2 := by
      nth_rewrite 2 [hdz]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_comm z u, real_inner_comm z n]
      ring
    have e2 : ⟪z', z'⟫ = ⟪u, z'⟫ ^ 2 + ⟪n, z'⟫ ^ 2 := by
      nth_rewrite 2 [hdz']
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_comm z' u, real_inner_comm z' n]
      ring
    rw [← e1, ← e2, hzz, hzz']
  -- stessa componente lungo u ⟹ stesso quadrato della componente normale
  have hquad : ⟪n, z⟫ ^ 2 = ⟪n, z'⟫ ^ 2 := by
    rw [hang] at hnorm2
    linarith
  -- entrambe positive ⟹ uguali
  have hpos : ⟪n, z⟫ = ⟪n, z'⟫ := by
    have h1 := hlato.1
    have h2 := hlato.2
    nlinarith [hquad, h1, h2]
  rw [hdz, hdz', hang, hpos]

end LeanEval.Geometry.PlatonicClassification
