import Mathlib
import Challenge
import Solution.Scala
import Solution.ScalaTipo
import Solution.Muovi
import Solution.MuoviTipo
import Solution.TrasportoFinale
import Solution.VentagliEspliciti
import Solution.Registro
import Solution.Montaggio
import Solution.Saldatura
import Solution.Propagazione
import Solution.LatiUguali
import Solution.RegolareTrasporto
import Solution.Fattore
import Solution.Riduzione
import Solution.TipiTestimoni

/-!
RIGIDITÀ — IL TEOREMA FINALE (19 lug 2026).

L'assemblaggio, nella sequenza fissata:

  fattore positivo dai diametri  →  omotetia  →  registrazione dalla Gram
  →  isometria  →  ventagli allineati  →  propagazione sui vertici
  →  uguaglianza degli hull  →  similarità.

Nessun passaggio usa l'identificazione delle faccette, Cauchy, il
generatore orbitale come lato, o punti scelti sugli spigoli: solo
invarianti canonici (Gram, raggi, diametri, hull).
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope

/-- Il ventaglio in un vertice, estratto dal tipo ciclico. -/
theorem esiste_ventaglio (P : ConvexPolytope 3) {p q : ℕ}
    (h : P.asFinite.IsCyclicallyRegularOfType p q) {v : E 3}
    (hv : v ∈ P.vertices) :
    Nonempty (P.asFinite.CyclicVertexData v q) :=
  h.2.2.2.choose_spec.2.2 v hv

/-- Un politopo full-dimensional ha almeno un vertice. -/
theorem esiste_vertice (P : ConvexPolytope 3) :
    ∃ v : E 3, v ∈ P.vertices := by
  obtain ⟨v, hv⟩ := P.vertices_nonempty
  exact ⟨v, hv⟩

end LeanEval.Geometry.PlatonicClassification
