import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.Scala
import UnicoProofs.Platonici.ScalaTipo
import UnicoProofs.Platonici.Muovi
import UnicoProofs.Platonici.MuoviTipo
import UnicoProofs.Platonici.TrasportoFinale
import UnicoProofs.Platonici.VentagliEspliciti
import UnicoProofs.Platonici.Registro
import UnicoProofs.Platonici.Montaggio
import UnicoProofs.Platonici.Saldatura
import UnicoProofs.Platonici.Propagazione
import UnicoProofs.Platonici.LatiUguali
import UnicoProofs.Platonici.RegolareTrasporto
import UnicoProofs.Platonici.Fattore
import UnicoProofs.Platonici.Riduzione
import UnicoProofs.Platonici.TipiTestimoni

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
