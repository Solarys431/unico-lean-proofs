import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.SimilarEquiv
import UnicoProofs.Platonici.Scala
import UnicoProofs.Platonici.ScalaTipo
import UnicoProofs.Platonici.Muovi
import UnicoProofs.Platonici.FanAHfan
import UnicoProofs.Platonici.Riduzione
import UnicoProofs.Platonici.TipiTestimoni

/-!
RIGIDITÀ — LO SCHELETRO DELL'ASSEMBLAGGIO (19 lug 2026).

Il montaggio finale, in forma condizionale rispetto all'unico pezzo che
manca (il gate locale «stesso fan marcato ⟹ stessa faccetta», fascicolo
28). La catena è:

  normalizzare la scala  →  registrare (isometria dal ventaglio)
  →  ventagli uguali  →  corpi uguali  →  Similar.

Le trasformazioni si compongono con `similar_scala`, `similar_muovi` e
`similar_trans`, tutte già certificate. Nessun passaggio nomina l'`ell`
orbitale: la scala si sceglierà dal diametro di uno spigolo esposto.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **L'ASSEMBLAGGIO**: se due politopi, dopo essere stati portati in
registro, hanno lo stesso corpo, allora sono simili. È la composizione
delle tre trasformazioni canoniche. -/
theorem similar_di_registro (P Q : ConvexPolytope 3) {a : ℝ} (ha : 0 < a)
    (g : Isom 3)
    (hcorpo : P.toSet = (muovi g (scala a (ne_of_gt ha) Q)).toSet) :
    Similar P Q := by
  have h1 : Similar Q (scala a (ne_of_gt ha) Q) := similar_scala a ha Q
  have h2 : Similar (scala a (ne_of_gt ha) Q)
      (muovi g (scala a (ne_of_gt ha) Q)) :=
    similar_muovi g (scala a (ne_of_gt ha) Q)
  have h3 : Similar Q (muovi g (scala a (ne_of_gt ha) Q)) :=
    similar_trans h1 h2
  -- P ha lo stesso corpo del trasformato, quindi gli è simile
  have h4 : Similar P (muovi g (scala a (ne_of_gt ha) Q)) := by
    refine ⟨1, one_pos, AffineIsometryEquiv.refl ℝ (E 3), ?_⟩
    rw [← hcorpo]
    simp
  exact similar_trans h4 (similar_symm h3)

/-- **LA RIGIDITÀ, IN FORMA CONDIZIONALE**: se ogni coppia di politopi
dello stesso tipo ammette una normalizzazione (scala + isometria) che ne
identifica i corpi, allora vale `hrigid`, e quindi il conteggio. -/
theorem rigidita_da_registro
    (hreg : ∀ (P Q : ConvexPolytope 3) (p q : ℕ),
      P.asFinite.IsCyclicallyRegularOfType p q →
      Q.asFinite.IsCyclicallyRegularOfType p q →
      ∃ (a : ℝ) (ha : 0 < a) (g : Isom 3),
        P.toSet = (muovi g (scala a (ne_of_gt ha) Q)).toSet) :
    ∀ (P Q : ConvexPolytope 3) (p q : ℕ),
      P.asFinite.IsCyclicallyRegularOfType p q →
      Q.asFinite.IsCyclicallyRegularOfType p q → Similar P Q := by
  intro P Q p q hP hQ
  obtain ⟨a, ha, g, hcorpo⟩ := hreg P Q p q hP hQ
  exact similar_di_registro P Q ha g hcorpo

/-- **IL CONTEGGIO DAL REGISTRO**: chiudendo il registro si chiude la
campagna 3D. -/
theorem platonicCount3_da_registro
    (hreg : ∀ (P Q : ConvexPolytope 3) (p q : ℕ),
      P.asFinite.IsCyclicallyRegularOfType p q →
      Q.asFinite.IsCyclicallyRegularOfType p q →
      ∃ (a : ℝ) (ha : 0 < a) (g : Isom 3),
        P.toSet = (muovi g (scala a (ne_of_gt ha) Q)).toSet) :
    platonicCount 3 = 5 :=
  platonicCount3_da_rigidita (rigidita_da_registro hreg)

end LeanEval.Geometry.PlatonicClassification
