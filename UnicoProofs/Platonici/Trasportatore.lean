import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FlagAdiacente
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.MossaInvolutiva
import UnicoProofs.Platonici.Equivarianza

/-!
MOTORE COXETER, PASSO 9 — TRASPORTATORE E RIFLESSIONI SEMPLICI
(19 lug 2026).

La flag-transitività di `IsRegular` fornisce, per ogni coppia di
bandiere, una simmetria che porta l'una nell'altra: il TRASPORTATORE.
La riflessione semplice `rᵢ` (relativa a una bandiera base `F`) è il
trasportatore da `F` alla sua adiacente al rango `i`.

Il teorema di chiusura: `rᵢ` applicata due volte fissa la bandiera —
per l'equivarianza la seconda applicazione insegue la prima attraverso
la mossa, e l'involutività della mossa riporta a casa. Quando la
LIBERTÀ dell'azione (fascicolo 41) sarà certificata, questo si
promuoverà a `rᵢ² = id` nel gruppo.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- L'azione rispetta la composizione delle simmetrie. -/
theorem mapFlag_trans (P : ConvexPolytope n) {φ ψ : Isom n}
    (hφ : P.isSymmetry φ) (hψ : P.isSymmetry ψ) (F : P.Flag) :
    mapFlag P hψ (mapFlag P hφ F) =
      mapFlag P (symmetry_transN hφ hψ) F := by
  apply flag_ext
  funext k
  show (⇑ψ) '' ((⇑φ) '' F.face k) = (⇑(φ.trans ψ)) '' F.face k
  rw [Set.image_image]
  rfl

/-- L'inversa disfa l'azione. -/
theorem mapFlag_symm_mapFlag (P : ConvexPolytope n) {φ : Isom n}
    (hφ : P.isSymmetry φ) (F : P.Flag) :
    mapFlag P (symmetry_symmN hφ) (mapFlag P hφ F) = F := by
  apply flag_ext
  funext k
  show (⇑φ.symm) '' ((⇑φ) '' F.face k) = F.face k
  exact φ.toEquiv.symm_image_image _

/-- Il **trasportatore**: la simmetria che porta `F` in `G`
(scelta classica dalla flag-transitività). -/
noncomputable def transporter (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F G : P.Flag) : Isom n :=
  (hreg.2 F G).choose

theorem transporter_isSymmetry (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F G : P.Flag) : P.isSymmetry (transporter P hreg F G) :=
  (hreg.2 F G).choose_spec.1

/-- Il trasportatore porta davvero `F` in `G`. -/
theorem transporter_mapFlag (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F G : P.Flag) :
    mapFlag P (transporter_isSymmetry P hreg F G) F = G := by
  apply flag_ext
  funext k
  show (⇑(transporter P hreg F G)) '' F.face k = G.face k
  exact (hreg.2 F G).choose_spec.2 k

/-- La **riflessione semplice** al rango `i`, relativa alla bandiera
base `F`: il trasportatore da `F` alla sua adiacente. -/
noncomputable def simpleReflection (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n) : Isom n :=
  transporter P hreg F (adjacentFlag P hreg.1 F i)

theorem simpleReflection_isSymmetry (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n) :
    P.isSymmetry (simpleReflection P hreg F i) :=
  transporter_isSymmetry P hreg F (adjacentFlag P hreg.1 F i)

/-- `rᵢ` manda la bandiera base nella sua adiacente al rango `i`. -/
theorem simpleReflection_mapFlag (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n) :
    mapFlag P (simpleReflection_isSymmetry P hreg F i) F =
      adjacentFlag P hreg.1 F i :=
  transporter_mapFlag P hreg F (adjacentFlag P hreg.1 F i)

/-- `rᵢ` scambia la bandiera base con la sua adiacente. -/
theorem simpleReflection_swaps (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n) :
    mapFlag P (simpleReflection_isSymmetry P hreg F i)
      (adjacentFlag P hreg.1 F i) = F := by
  rw [mapFlag_adjacentFlag P hreg.1
    (simpleReflection_isSymmetry P hreg F i) F i,
    simpleReflection_mapFlag P hreg F i]
  exact adjacentFlag_involutive P hreg.1 F i

/-- **`rᵢ` due volte fissa la bandiera**: il germe di `rᵢ² = 1`. -/
theorem simpleReflection_sq_fixes (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n) :
    mapFlag P (simpleReflection_isSymmetry P hreg F i)
      (mapFlag P (simpleReflection_isSymmetry P hreg F i) F) = F := by
  rw [simpleReflection_mapFlag P hreg F i]
  exact simpleReflection_swaps P hreg F i

end LeanEval.Geometry.PlatonicClassification
