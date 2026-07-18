import UnicoProofs.Platonici.Classificazione
import UnicoProofs.Platonici.TetraedroStadio2
import UnicoProofs.Platonici.CuboTestimone
import UnicoProofs.Platonici.OttaedroTestimone
import UnicoProofs.Platonici.DodecaedroTestimone
import UnicoProofs.Platonici.IcosaedroTestimone

/-!
FASE 1B, N6 — LA CARATTERIZZAZIONE COMPLETA (18 lug 2026).

Il teorema di Schläfli locale (`cyclicallyRegular_schlafli`) dice che ogni
politopo ciclicamente regolare ha tipo in {(3,3),(4,3),(3,4),(5,3),(3,5)};
i cinque testimoni dicono che OGNI tipo ammesso si realizza. Insieme:
la caratterizzazione esatta. Nessuna direzione è vacua.
-/

open FiniteConvexPolytope

/-- I CINQUE SOLIDI ESISTONO: un testimone kernel-puro per ciascun tipo. -/
theorem cinque_testimoni :
    (∃ P : FiniteConvexPolytope E3, P.IsCyclicallyRegularOfType 3 3) ∧
    (∃ P : FiniteConvexPolytope E3, P.IsCyclicallyRegularOfType 4 3) ∧
    (∃ P : FiniteConvexPolytope E3, P.IsCyclicallyRegularOfType 3 4) ∧
    (∃ P : FiniteConvexPolytope E3, P.IsCyclicallyRegularOfType 5 3) ∧
    (∃ P : FiniteConvexPolytope E3, P.IsCyclicallyRegularOfType 3 5) :=
  ⟨⟨tetraedro, tetraedro_cyclicallyRegular⟩,
   ⟨cubo, cubo_cyclicallyRegular⟩,
   ⟨ottaedro, ottaedro_cyclicallyRegular⟩,
   ⟨dodecaedro, dodecaedro_cyclicallyRegular⟩,
   ⟨icosaedro, icosaedro_cyclicallyRegular⟩⟩

/-- LA CARATTERIZZAZIONE: un tipo (p,q) è realizzabile da un politopo
ciclicamente regolare se e solo se è uno dei cinque tipi platonici. -/
theorem realizzabile_iff (p q : ℕ) :
    (∃ P : FiniteConvexPolytope E3, P.IsCyclicallyRegularOfType p q)
    ↔ ((p = 3 ∧ q = 3) ∨ (p = 4 ∧ q = 3) ∨ (p = 3 ∧ q = 4)
        ∨ (p = 5 ∧ q = 3) ∨ (p = 3 ∧ q = 5)) := by
  constructor
  · rintro ⟨P, hP⟩
    exact (cyclicallyRegular_schlafli P hP).2
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨tetraedro, tetraedro_cyclicallyRegular⟩
    · exact ⟨cubo, cubo_cyclicallyRegular⟩
    · exact ⟨ottaedro, ottaedro_cyclicallyRegular⟩
    · exact ⟨dodecaedro, dodecaedro_cyclicallyRegular⟩
    · exact ⟨icosaedro, icosaedro_cyclicallyRegular⟩
