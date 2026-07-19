import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.IstanzeBenchmark
import UnicoProofs.Platonici.Ponte
import UnicoProofs.Platonici.Maggiorante

/-!
RIGIDITÀ — LA RIDUZIONE FINALE (19 lug 2026).

L'ipotesi hrig del Maggiorante (ogni regolare è simile a un testimone) si
riduce qui a DUE ingredienti:
1. la RIGIDITÀ per tipo: due politopi del contratto i cui asFinite hanno
   lo stesso tipo ciclico (p,q) sono simili (i gate 2-7 in scarico);
2. i TIPI dei testimoni: gli asFinite dei cinque solidi BM hanno i cinque
   tipi di Schläfli (i moduli Testimone li certificano già nel mondo
   finito; resta il collegamento asFinite, coordinate alla mano).
Con questi due, `regolare_schlafli` smista ogni politopo regolare sul suo
testimone e `platonicCount 3 = 5` segue dal Maggiorante.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **LA RIDUZIONE**: rigidità per tipo + tipi dei testimoni ⟹ l'ipotesi
del Maggiorante. -/
theorem hrig_da_rigidita_e_tipi
    (hrigid : ∀ (P Q : ConvexPolytope 3) (p q : ℕ),
      P.asFinite.IsCyclicallyRegularOfType p q →
      Q.asFinite.IsCyclicallyRegularOfType p q → Similar P Q)
    (hT : tetraedroBM.asFinite.IsCyclicallyRegularOfType 3 3)
    (hC : cuboBM.asFinite.IsCyclicallyRegularOfType 4 3)
    (hO : ottaedroBM.asFinite.IsCyclicallyRegularOfType 3 4)
    (hD : dodecaedroBM.asFinite.IsCyclicallyRegularOfType 5 3)
    (hI : icosaedroBM.asFinite.IsCyclicallyRegularOfType 3 5) :
    ∀ P : regularPolytopes 3,
      ∃ i : Fin 5, regularSimilar 3 P (testimone i) := by
  intro P
  obtain ⟨p, q, htipo, hcasi⟩ :=
    regolare_schlafli (P : ConvexPolytope 3) P.property
  rcases hcasi with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
  · subst hp; subst hq
    exact ⟨0, hrigid _ _ 3 3 htipo hT⟩
  · subst hp; subst hq
    exact ⟨1, hrigid _ _ 4 3 htipo hC⟩
  · subst hp; subst hq
    exact ⟨2, hrigid _ _ 3 4 htipo hO⟩
  · subst hp; subst hq
    exact ⟨3, hrigid _ _ 5 3 htipo hD⟩
  · subst hp; subst hq
    exact ⟨4, hrigid _ _ 3 5 htipo hI⟩

/-- **L'EQUAZIONE FINALE, RIDOTTA AI DUE INGREDIENTI**. -/
theorem platonicCount3_da_rigidita_e_tipi
    (hrigid : ∀ (P Q : ConvexPolytope 3) (p q : ℕ),
      P.asFinite.IsCyclicallyRegularOfType p q →
      Q.asFinite.IsCyclicallyRegularOfType p q → Similar P Q)
    (hT : tetraedroBM.asFinite.IsCyclicallyRegularOfType 3 3)
    (hC : cuboBM.asFinite.IsCyclicallyRegularOfType 4 3)
    (hO : ottaedroBM.asFinite.IsCyclicallyRegularOfType 3 4)
    (hD : dodecaedroBM.asFinite.IsCyclicallyRegularOfType 5 3)
    (hI : icosaedroBM.asFinite.IsCyclicallyRegularOfType 3 5) :
    platonicCount 3 = 5 :=
  platonicCount3_eq_cinque_di
    (hrig_da_rigidita_e_tipi hrigid hT hC hO hD hI)

end LeanEval.Geometry.PlatonicClassification
