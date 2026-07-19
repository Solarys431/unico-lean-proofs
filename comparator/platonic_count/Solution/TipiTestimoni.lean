import Mathlib
import Challenge
import Solution.IstanzeBenchmark
import Solution.Riduzione

/-!
RIGIDITÀ — I TIPI DEI TESTIMONI (19 lug 2026).

I cinque BM del contratto sono costruiti con gli stessi campi dei solidi
del mondo finito, quindi i loro `asFinite` SONO quei solidi per
riducibilità definizionale, e i tipi ciclici certificati dai moduli
Testimone si trasportano senza lavoro. Con questo, l'equazione finale
`platonicCount 3 = 5` pende da UNA SOLA ipotesi: la rigidità per tipo.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

theorem tetraedroBM_tipo :
    tetraedroBM.asFinite.IsCyclicallyRegularOfType 3 3 := by
  show tetraedro.IsCyclicallyRegularOfType 3 3
  exact tetraedro_cyclicallyRegular

theorem cuboBM_tipo :
    cuboBM.asFinite.IsCyclicallyRegularOfType 4 3 := by
  show cubo.IsCyclicallyRegularOfType 4 3
  exact cubo_cyclicallyRegular

theorem ottaedroBM_tipo :
    ottaedroBM.asFinite.IsCyclicallyRegularOfType 3 4 := by
  show ottaedro.IsCyclicallyRegularOfType 3 4
  exact ottaedro_cyclicallyRegular

theorem dodecaedroBM_tipo :
    dodecaedroBM.asFinite.IsCyclicallyRegularOfType 5 3 := by
  show dodecaedro.IsCyclicallyRegularOfType 5 3
  exact dodecaedro_cyclicallyRegular

theorem icosaedroBM_tipo :
    icosaedroBM.asFinite.IsCyclicallyRegularOfType 3 5 := by
  show icosaedro.IsCyclicallyRegularOfType 3 5
  exact icosaedro_cyclicallyRegular

/-- **L'IMBUTO FINALE**: l'equazione del benchmark pende dalla SOLA
rigidità per tipo. -/
theorem platonicCount3_da_rigidita
    (hrigid : ∀ (P Q : ConvexPolytope 3) (p q : ℕ),
      P.asFinite.IsCyclicallyRegularOfType p q →
      Q.asFinite.IsCyclicallyRegularOfType p q → Similar P Q) :
    platonicCount 3 = 5 :=
  platonicCount3_da_rigidita_e_tipi hrigid tetraedroBM_tipo cuboBM_tipo
    ottaedroBM_tipo dodecaedroBM_tipo icosaedroBM_tipo

end LeanEval.Geometry.PlatonicClassification
