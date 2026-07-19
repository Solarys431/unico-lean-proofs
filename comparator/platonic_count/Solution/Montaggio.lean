import Mathlib
import Challenge
import Solution.Muovi
import Solution.MuoviTipo
import Solution.TrasportoFinale
import Solution.VentagliEspliciti
import Solution.Registro
import Solution.Propagazione

/-!
RIGIDITÀ — IL MONTAGGIO DELL'ALLINEAMENTO (19 lug 2026).

Il cuore del finale: dalla registrazione si ricava che i raggi del
politopo mosso coincidono, indice per indice, con quelli del bersaglio.

Il passaggio chiave è che un'isometria affine sposta il vertice e applica
la parte lineare al resto: `g (v + w) = g v + L_g w`, che segue da
`map_vsub`. Combinata con `dir_muovi_eq` (l'isometria applica la sola
parte lineare) e con la conclusione della registrazione, dà l'uguaglianza
dei raggi senza residui.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- Un'isometria affine trasla il punto base e applica la parte lineare. -/
theorem isom_add (g : Isom 3) (v w : E 3) :
    g (v + w) = g v + g.linearIsometryEquiv w := by
  have h := g.map_vsub (v + w) v
  simp only [vsub_eq_sub] at h
  have hsub : v + w - v = w := by abel
  rw [hsub] at h
  exact sub_eq_iff_eq_add'.mp h.symm

/-- **I RAGGI DEL MOSSO COINCIDONO CON QUELLI DEL BERSAGLIO**: è la
conclusione della registrazione, letta sui raggi. -/
theorem dir_registrato {q : ℕ} {g : Isom 3}
    {v v' : E 3} {dA dB : Fin q → E 3}
    (hgv : g v = v')
    (hreg : ∀ i, g (v + dA i) = v' + dB i) (i : Fin q) :
    g.linearIsometryEquiv (dA i) = dB i := by
  have h := hreg i
  rw [isom_add g v (dA i), hgv] at h
  exact add_left_cancel h

/-- **L'ALLINEAMENTO AL VERTICE REGISTRATO**: dopo aver mosso `A` con
l'isometria della registrazione, i suoi raggi coincidono con quelli di
`B`. -/
theorem allineamento_da_registro (A B : ConvexPolytope 3) {p q : ℕ}
    (hA : A.asFinite.IsCyclicallyRegularOfType p q)
    {v v' : E 3} (hvA : v ∈ A.vertices) (hvB : v' ∈ B.vertices)
    (DA : A.asFinite.CyclicVertexData v q)
    (DB : B.asFinite.CyclicVertexData v' q)
    {g : Isom 3} (hgv : g v = v')
    (hreg : ∀ i, g (v + dir A.asFinite v DA i) =
      v' + dir B.asFinite v' DB i)
    (DA' : (muovi g A).asFinite.CyclicVertexData (g v) q)
    (hfacce : ∀ i, DA'.faccetta i = (fun x : E 3 => g x) '' DA.faccetta i) :
    ∀ i, dir (muovi g A).asFinite (g v) DA' i = dir B.asFinite v' DB i := by
  intro i
  rw [dir_muovi_eq A hA g hvA DA DA' hfacce i]
  exact dir_registrato hgv hreg i

end LeanEval.Geometry.PlatonicClassification
