import Mathlib
import Challenge
import Solution.ScalaBandiere
import Solution.TrasportoFaccetta

/-!
RIGIDITÀ — GLI SPIGOLI SONO TUTTI CONGRUENTI (19 lug 2026).

Primo pezzo della strategia che AGGIRA la falla 11: invece di
normalizzare i testimoni d'orbita (che confrontano `segment x (rho x)` e
possono percorrere diagonali), si misura lo spigolo con il suo DIAMETRO,
che è intrinseco e invariante per isometrie. La transitività sulle
bandiere di un politopo regolare porta ogni spigolo su ogni altro,
dunque tutti gli spigoli hanno lo stesso diametro: la lunghezza del lato
è un invariante del politopo, senza mai nominare `ell`.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Un'isometria affine conserva il diametro. -/
theorem diam_image_isom (φ : Isom 3) (s : Set (E 3)) :
    Metric.diam ((⇑φ) '' s) = Metric.diam s := by
  have hiso : Isometry (⇑φ) := φ.isometry
  exact hiso.diam_image s

/-- **GLI SPIGOLI DI UNA STESSA BANDIERA-ORBITA SONO CONGRUENTI**: se una
simmetria porta lo spigolo di una bandiera su quello di un'altra, i due
hanno lo stesso diametro. -/
theorem diam_eq_of_symmetry {φ : Isom 3} {δ δ' : Set (E 3)}
    (himg : (⇑φ) '' δ = δ') : Metric.diam δ = Metric.diam δ' := by
  rw [← himg, diam_image_isom]

/-- **TUTTI GLI SPIGOLI DI UN POLITOPO REGOLARE SONO CONGRUENTI**, nella
forma che serve: due bandiere qualsiasi hanno spigoli dello stesso
diametro. -/
theorem spigoli_bandiere_congrui (P : ConvexPolytope 3)
    (hreg : P.IsRegular) (F G : P.Flag) :
    Metric.diam (F.face 1) = Metric.diam (G.face 1) := by
  obtain ⟨φ, _hsym, himg⟩ := hreg.2 F G
  exact diam_eq_of_symmetry (himg 1)

/-- La lunghezza del lato di un politopo regolare: il diametro dello
spigolo di una qualunque sua bandiera. -/
noncomputable def latoDi (P : ConvexPolytope 3) (F : P.Flag) : ℝ :=
  Metric.diam (F.face 1)

theorem latoDi_indipendente (P : ConvexPolytope 3) (hreg : P.IsRegular)
    (F G : P.Flag) : latoDi P F = latoDi P G :=
  spigoli_bandiere_congrui P hreg F G

/-- Ogni faccia di rango 1 è lo spigolo di qualche bandiera: quindi il
diametro comune vale per TUTTI gli spigoli, non solo per quelli di
bandiera. (Forma condizionale: l'esistenza della bandiera che contiene un
dato spigolo si scarica separatamente.) -/
theorem spigoli_congrui_di_bandiere (P : ConvexPolytope 3)
    (hreg : P.IsRegular) {δ δ' : Set (E 3)}
    (hδ : ∃ F : P.Flag, F.face 1 = δ)
    (hδ' : ∃ G : P.Flag, G.face 1 = δ') :
    Metric.diam δ = Metric.diam δ' := by
  obtain ⟨F, hF⟩ := hδ
  obtain ⟨G, hG⟩ := hδ'
  rw [← hF, ← hG]
  exact spigoli_bandiere_congrui P hreg F G

end LeanEval.Geometry.PlatonicClassification
