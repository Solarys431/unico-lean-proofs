import Mathlib
import Challenge
import Solution.ConoVertice
import Solution.FacceConnesse
import Solution.VerticeAdiacente
import Solution.BandieraSpigolo

/-!
RIGIDITÀ — IL DIAMETRO DI UNO SPIGOLO È POSITIVO (19 lug 2026).

Il pezzo che manca per definire il fattore di normalizzazione
`a = diam(spigolo di P) / diam(spigolo di Q)`: il denominatore dev'essere
non nullo. Uno spigolo è una faccia di rango 1, dunque un segmento fra due
vertici DISTINTI, e il suo diametro è la loro distanza — positiva.

Individuato da Daniele come rischio residuo dell'assemblaggio, prima che
si manifestasse.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **IL DIAMETRO DI UNO SPIGOLO È POSITIVO**. -/
theorem diam_spigolo_pos (P : ConvexPolytope 3) {δ : Set (E 3)}
    (hδ : P.IsFace δ) (hdδ : faceDim δ = 1) :
    0 < Metric.diam δ := by
  classical
  -- uno spigolo contiene un vertice del politopo
  obtain ⟨w, hwV, hwδ⟩ := faccetta_ha_vertice P hδ
  -- e ne contiene un secondo, distinto
  obtain ⟨u, huV, huδ, huw, hseg⟩ := spigolo_segmento P hδ hdδ hwV hwδ
  rw [hseg, diam_segment]
  exact dist_pos.mpr (Ne.symm huw)

/-- Il fattore di normalizzazione è positivo. -/
theorem fattore_pos (P Q : ConvexPolytope 3) {δ ε : Set (E 3)}
    (hδ : P.IsFace δ) (hdδ : faceDim δ = 1)
    (hε : Q.IsFace ε) (hdε : faceDim ε = 1) :
    0 < Metric.diam δ / Metric.diam ε :=
  div_pos (diam_spigolo_pos P hδ hdδ) (diam_spigolo_pos Q hε hdε)

/-- In un politopo regolare il diametro degli spigoli è una costante
positiva, indipendente dallo spigolo scelto. -/
theorem diam_spigoli_costante_pos (P : ConvexPolytope 3)
    (hreg : P.IsRegular) {δ δ' : Set (E 3)}
    (hδ : P.IsFace δ) (hdδ : faceDim δ = 1)
    (hδ' : P.IsFace δ') (hdδ' : faceDim δ' = 1) :
    Metric.diam δ = Metric.diam δ' ∧ 0 < Metric.diam δ :=
  ⟨spigoli_congrui P hreg hδ hdδ hδ' hdδ', diam_spigolo_pos P hδ hdδ⟩

end LeanEval.Geometry.PlatonicClassification
