import Mathlib
import Challenge
import Solution.IstanzeBenchmark
import Solution.Ponte
import Solution.Maggiorante
import Solution.Riduzione
import Solution.TipiTestimoni
import Solution.RegolariBenchmark

/-!
RIGIDITÀ — IL CONTEGGIO DALLA RIGIDITÀ FRA REGOLARI (19 lug 2026).

`platonicCount3_da_rigidita` chiede l'implicazione «stesso tipo ⟹ simili»
per politopi QUALSIASI, mentre il nostro teorema di rigidità usa la
regolarità (le serve per la congruenza degli spigoli). Non è un problema:
`platonicCount` conta le classi di similarità di `regularPolytopes 3`,
dunque tutti i politopi in gioco SONO regolari, e i cinque testimoni lo
sono per teoremi già certificati. Qui la variante con l'ipotesi
indebolita.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **IL CONTEGGIO DALLA RIGIDITÀ FRA REGOLARI**. -/
theorem platonicCount3_da_rigidita_regolare
    (hrigid : ∀ (P Q : ConvexPolytope 3) (p q : ℕ),
      P.IsRegular → Q.IsRegular →
      P.asFinite.IsCyclicallyRegularOfType p q →
      Q.asFinite.IsCyclicallyRegularOfType p q → Similar P Q) :
    platonicCount 3 = 5 := by
  refine platonicCount3_eq_cinque_di ?_
  intro P
  obtain ⟨p, q, htipo, hcasi⟩ :=
    regolare_schlafli (P : ConvexPolytope 3) P.property
  have hPreg : (P : ConvexPolytope 3).IsRegular := P.property
  rcases hcasi with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
  · subst hp; subst hq
    exact ⟨0, hrigid _ _ 3 3 hPreg tetraedroBM_isRegular htipo
      tetraedroBM_tipo⟩
  · subst hp; subst hq
    exact ⟨1, hrigid _ _ 4 3 hPreg cuboBM_isRegular htipo cuboBM_tipo⟩
  · subst hp; subst hq
    exact ⟨2, hrigid _ _ 3 4 hPreg ottaedroBM_isRegular htipo
      ottaedroBM_tipo⟩
  · subst hp; subst hq
    exact ⟨3, hrigid _ _ 5 3 hPreg dodecaedroBM_isRegular htipo
      dodecaedroBM_tipo⟩
  · subst hp; subst hq
    exact ⟨4, hrigid _ _ 3 5 hPreg icosaedroBM_isRegular htipo
      icosaedroBM_tipo⟩

end LeanEval.Geometry.PlatonicClassification
