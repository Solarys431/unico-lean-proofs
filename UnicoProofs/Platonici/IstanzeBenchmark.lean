import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.InvarianteSimilarita
import UnicoProofs.Platonici.TetraedroStadio2
import UnicoProofs.Platonici.CuboTestimone
import UnicoProofs.Platonici.OttaedroTestimone
import UnicoProofs.Platonici.DodecaedroTestimone
import UnicoProofs.Platonici.IcosaedroTestimone

/-!
FASE 2 — LE CINQUE ISTANZE SUL CONTRATTO DEL BENCHMARK (18 lug 2026).

`ConvexPolytope 3` del benchmark ha esattamente i campi del nostro
`FiniteConvexPolytope E3`: le cinque istanze si costruiscono riusando le
dimostrazioni della fase 1b. Le cardinalità (4, 8, 6) si ottengono con
decodificatori di segno (inversa sinistra ⟹ iniettività della famiglia).
-/

open Set Metric FiniteConvexPolytope

namespace LeanEval.Geometry.PlatonicClassification

noncomputable section

/-- Il tetraedro sul contratto del benchmark. -/
def tetraedroBM : ConvexPolytope 3 :=
  ⟨verticiTetra, tetraedro.nonempty, tetraedro.vertices_eq_extremePoints⟩

/-- Il cubo sul contratto del benchmark. -/
def cuboBM : ConvexPolytope 3 :=
  ⟨verticiCubo, cubo.nonempty, cubo.vertices_eq_extremePoints⟩

/-- L'ottaedro sul contratto del benchmark. -/
def ottaedroBM : ConvexPolytope 3 :=
  ⟨verticiOtta, ottaedro.nonempty, ottaedro.vertices_eq_extremePoints⟩

/-- Il dodecaedro sul contratto del benchmark. -/
def dodecaedroBM : ConvexPolytope 3 :=
  ⟨dodecaedro.vertices, dodecaedro.nonempty, dodecaedro.vertices_eq_extremePoints⟩

/-- L'icosaedro sul contratto del benchmark. -/
def icosaedroBM : ConvexPolytope 3 :=
  ⟨icosaedro.vertices, icosaedro.nonempty, icosaedro.vertices_eq_extremePoints⟩

/-! ## Le cardinalità via decodificatore di segno -/

/-- La famiglia dei vertici del cubo. -/
def famCubo : Fin 8 → E3 := ![c0, c1, c2, c3, c4, c5, c6, c7]

open Classical in
/-- Il decodificatore: legge i segni delle tre coordinate (if annidati,
nessuna aritmetica: ogni ramo è un letterale). -/
noncomputable def decCubo (x : E3) : Fin 8 :=
  if 0 < (WithLp.ofLp x) 0 then
    (if 0 < (WithLp.ofLp x) 1 then
      (if 0 < (WithLp.ofLp x) 2 then 0 else 1)
     else
      (if 0 < (WithLp.ofLp x) 2 then 2 else 3))
  else
    (if 0 < (WithLp.ofLp x) 1 then
      (if 0 < (WithLp.ofLp x) 2 then 4 else 5)
     else
      (if 0 < (WithLp.ofLp x) 2 then 6 else 7))

theorem decCubo_famCubo : ∀ i, decCubo (famCubo i) = i := by
  intro i
  fin_cases i
  all_goals simp [decCubo, famCubo, c0, c1, c2, c3, c4, c5, c6, c7]
  all_goals try decide
  all_goals try norm_num

theorem famCubo_iniettiva : Function.Injective famCubo :=
  Function.LeftInverse.injective decCubo_famCubo

theorem card_cubo : cuboBM.vertices.card = 8 := by
  show verticiCubo.card = 8
  have h : verticiCubo = Finset.univ.image famCubo := by
    ext z
    rw [mem_verticiCubo_iff]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h | h | h | h | h | h | h) <;> subst h
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨6, rfl⟩
      · exact ⟨7, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [famCubo]
  rw [h, Finset.card_image_of_injective _ famCubo_iniettiva]
  simp

/-- La famiglia dei vertici dell'ottaedro. -/
def famOtta : Fin 6 → E3 := ![o0, o1, o2, o3, o4, o5]

open Classical in
/-- Decodificatore: quale coordinata è non nulla, e il suo segno. -/
noncomputable def decOtta (x : E3) : Fin 6 :=
  if (WithLp.ofLp x) 0 > 0 then 0
  else if (WithLp.ofLp x) 1 > 0 then 1
  else if (WithLp.ofLp x) 2 > 0 then 2
  else if (WithLp.ofLp x) 0 < 0 then 3
  else if (WithLp.ofLp x) 1 < 0 then 4
  else 5

theorem decOtta_famOtta : ∀ i, decOtta (famOtta i) = i := by
  intro i
  fin_cases i
  all_goals simp [decOtta, famOtta, o0, o1, o2, o3, o4, o5]
  all_goals try decide
  all_goals try norm_num

theorem famOtta_iniettiva : Function.Injective famOtta :=
  Function.LeftInverse.injective decOtta_famOtta

theorem card_otta : ottaedroBM.vertices.card = 6 := by
  show verticiOtta.card = 6
  have h : verticiOtta = Finset.univ.image famOtta := by
    ext z
    rw [mem_verticiOtta_iff]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h | h | h | h | h) <;> subst h
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [famOtta]
  rw [h, Finset.card_image_of_injective _ famOtta_iniettiva]
  simp

theorem card_tetra : tetraedroBM.vertices.card = 4 := by
  show verticiTetra.card = 4
  rw [verticiTetra_eq_map, Finset.card_map]
  simp


/-! ## Le cardinalità del dodecaedro e dell'icosaedro -/

/-- La famiglia dei vertici. -/
def famDodeca : Fin 20 → E3 := ![a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3]

open Classical in
/-- Decodificatore del dodecaedro: famiglia per coordinata nulla, poi segni. -/
noncomputable def decDodeca (x : E3) : Fin 20 :=
  if (WithLp.ofLp x) 0 = 0 then
    (if 0 < (WithLp.ofLp x) 1 then (if 0 < (WithLp.ofLp x) 2 then 11 else 10)
     else (if 0 < (WithLp.ofLp x) 2 then 9 else 8))
  else if (WithLp.ofLp x) 1 = 0 then
    (if 0 < (WithLp.ofLp x) 0 then (if 0 < (WithLp.ofLp x) 2 then 15 else 14)
     else (if 0 < (WithLp.ofLp x) 2 then 13 else 12))
  else if (WithLp.ofLp x) 2 = 0 then
    (if 0 < (WithLp.ofLp x) 0 then (if 0 < (WithLp.ofLp x) 1 then 19 else 18)
     else (if 0 < (WithLp.ofLp x) 1 then 17 else 16))
  else
    (if 0 < (WithLp.ofLp x) 0 then
      (if 0 < (WithLp.ofLp x) 1 then (if 0 < (WithLp.ofLp x) 2 then 7 else 6)
       else (if 0 < (WithLp.ofLp x) 2 then 5 else 4))
     else
      (if 0 < (WithLp.ofLp x) 1 then (if 0 < (WithLp.ofLp x) 2 then 3 else 2)
       else (if 0 < (WithLp.ofLp x) 2 then 1 else 0)))

theorem decDodeca_famDodeca : ∀ i, decDodeca (famDodeca i) = i := by
  have hphi : (0:ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have hphii : (0:ℝ) < Real.goldenRatio⁻¹ := inv_pos.mpr hphi
  intro i
  fin_cases i
  all_goals try simp [decDodeca, famDodeca, a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3]
  all_goals try norm_num [hphi, hphii]
  all_goals (have hsum : (0:ℝ) < 1 + Real.sqrt 5 := (by positivity); have hdiv : (0:ℝ) < 2 / (1 + Real.sqrt 5) := (by positivity); first | rfl | linarith [Real.goldenRatio_pos, hsum, hdiv] | (intro hng; linarith [Real.goldenRatio_pos, hsum, hdiv]) | (split_ifs <;> first | rfl | (exfalso; linarith [Real.goldenRatio_pos, hsum, hdiv])))

theorem famDodeca_iniettiva : Function.Injective famDodeca :=
  Function.LeftInverse.injective decDodeca_famDodeca

theorem card_dodeca : verticiDodeca.card = 20 := by
  have h : verticiDodeca = Finset.univ.image famDodeca := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hz
      have hc : z = a0 ∨ z = a1 ∨ z = a2 ∨ z = a3 ∨ z = a4 ∨ z = a5 ∨ z = a6 ∨ z = a7 ∨ z = b0 ∨ z = b1 ∨ z = b2 ∨ z = b3 ∨ z = c0D ∨ z = c1D ∨ z = c2D ∨ z = c3D ∨ z = d0 ∨ z = d1D ∨ z = d2D ∨ z = d3 := by
        simpa [verticiDodeca] using hz
      rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · subst h
        exact ⟨0, rfl⟩
      · subst h
        exact ⟨1, rfl⟩
      · subst h
        exact ⟨2, rfl⟩
      · subst h
        exact ⟨3, rfl⟩
      · subst h
        exact ⟨4, rfl⟩
      · subst h
        exact ⟨5, rfl⟩
      · subst h
        exact ⟨6, rfl⟩
      · subst h
        exact ⟨7, rfl⟩
      · subst h
        exact ⟨8, rfl⟩
      · subst h
        exact ⟨9, rfl⟩
      · subst h
        exact ⟨10, rfl⟩
      · subst h
        exact ⟨11, rfl⟩
      · subst h
        exact ⟨12, rfl⟩
      · subst h
        exact ⟨13, rfl⟩
      · subst h
        exact ⟨14, rfl⟩
      · subst h
        exact ⟨15, rfl⟩
      · subst h
        exact ⟨16, rfl⟩
      · subst h
        exact ⟨17, rfl⟩
      · subst h
        exact ⟨18, rfl⟩
      · subst h
        exact ⟨19, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [famDodeca, verticiDodeca]
  rw [h, Finset.card_image_of_injective _ famDodeca_iniettiva]
  simp

/-- La famiglia dei vertici. -/
def famIcosa : Fin 12 → E3 := ![a0I, a1I, a2I, a3I, b0I, b1I, b2I, b3I, c0I, c1I, c2I, c3I]

open Classical in
/-- Decodificatore dell'icosaedro: famiglia per coordinata nulla, poi segni. -/
noncomputable def decIcosa (x : E3) : Fin 12 :=
  if (WithLp.ofLp x) 0 = 0 then
    (if 0 < (WithLp.ofLp x) 1 then (if 0 < (WithLp.ofLp x) 2 then 11 else 10)
     else (if 0 < (WithLp.ofLp x) 2 then 9 else 8))
  else if (WithLp.ofLp x) 1 = 0 then
    (if 0 < (WithLp.ofLp x) 0 then (if 0 < (WithLp.ofLp x) 2 then 3 else 2)
     else (if 0 < (WithLp.ofLp x) 2 then 1 else 0))
  else
    (if 0 < (WithLp.ofLp x) 0 then (if 0 < (WithLp.ofLp x) 1 then 7 else 6)
     else (if 0 < (WithLp.ofLp x) 1 then 5 else 4))

theorem decIcosa_famIcosa : ∀ i, decIcosa (famIcosa i) = i := by
  have hphi : (0:ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have hphii : (0:ℝ) < Real.goldenRatio⁻¹ := inv_pos.mpr hphi
  intro i
  fin_cases i
  all_goals try simp [decIcosa, famIcosa, a0I, a1I, a2I, a3I, b0I, b1I, b2I, b3I, c0I, c1I, c2I, c3I]
  all_goals try norm_num [hphi, hphii]
  all_goals (have hsum : (0:ℝ) < 1 + Real.sqrt 5 := (by positivity); have hdiv : (0:ℝ) < 2 / (1 + Real.sqrt 5) := (by positivity); first | rfl | linarith [Real.goldenRatio_pos, hsum, hdiv] | (intro hng; linarith [Real.goldenRatio_pos, hsum, hdiv]) | (split_ifs <;> first | rfl | (exfalso; linarith [Real.goldenRatio_pos, hsum, hdiv])))


theorem famIcosa_iniettiva : Function.Injective famIcosa :=
  Function.LeftInverse.injective decIcosa_famIcosa

theorem card_icosa : verticiIcosa.card = 12 := by
  have h : verticiIcosa = Finset.univ.image famIcosa := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hz
      have hc : z = a0I ∨ z = a1I ∨ z = a2I ∨ z = a3I ∨ z = b0I ∨ z = b1I ∨ z = b2I ∨ z = b3I ∨ z = c0I ∨ z = c1I ∨ z = c2I ∨ z = c3I := by
        simpa [verticiIcosa] using hz
      rcases hc with h | h | h | h | h | h | h | h | h | h | h | h
      · subst h
        exact ⟨0, rfl⟩
      · subst h
        exact ⟨1, rfl⟩
      · subst h
        exact ⟨2, rfl⟩
      · subst h
        exact ⟨3, rfl⟩
      · subst h
        exact ⟨4, rfl⟩
      · subst h
        exact ⟨5, rfl⟩
      · subst h
        exact ⟨6, rfl⟩
      · subst h
        exact ⟨7, rfl⟩
      · subst h
        exact ⟨8, rfl⟩
      · subst h
        exact ⟨9, rfl⟩
      · subst h
        exact ⟨10, rfl⟩
      · subst h
        exact ⟨11, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [famIcosa, verticiIcosa]
  rw [h, Finset.card_image_of_injective _ famIcosa_iniettiva]
  simp

theorem card_dodecaedroBM : dodecaedroBM.vertices.card = 20 := card_dodeca
theorem card_icosaedroBM : icosaedroBM.vertices.card = 12 := card_icosa


/-! ## Le dieci non-similarità -/

theorem non_simili_tetraedro_cubo : ¬ ConvexPolytope.Similar tetraedroBM cuboBM := by
  intro h
  have hc := vertices_card_of_similar h
  rw [show (cuboBM).vertices.card = _ from card_cubo,
    show (tetraedroBM).vertices.card = _ from card_tetra] at hc
  norm_num at hc

theorem non_simili_tetraedro_ottaedro : ¬ ConvexPolytope.Similar tetraedroBM ottaedroBM := by
  intro h
  have hc := vertices_card_of_similar h
  rw [show (ottaedroBM).vertices.card = _ from card_otta,
    show (tetraedroBM).vertices.card = _ from card_tetra] at hc
  norm_num at hc

theorem non_simili_tetraedro_dodecaedro : ¬ ConvexPolytope.Similar tetraedroBM dodecaedroBM := by
  intro h
  have hc := vertices_card_of_similar h
  rw [show (dodecaedroBM).vertices.card = _ from card_dodeca,
    show (tetraedroBM).vertices.card = _ from card_tetra] at hc
  norm_num at hc

theorem non_simili_tetraedro_icosaedro : ¬ ConvexPolytope.Similar tetraedroBM icosaedroBM := by
  intro h
  have hc := vertices_card_of_similar h
  rw [show (icosaedroBM).vertices.card = _ from card_icosa,
    show (tetraedroBM).vertices.card = _ from card_tetra] at hc
  norm_num at hc

theorem non_simili_cubo_ottaedro : ¬ ConvexPolytope.Similar cuboBM ottaedroBM := by
  intro h
  have hc := vertices_card_of_similar h
  rw [show (ottaedroBM).vertices.card = _ from card_otta,
    show (cuboBM).vertices.card = _ from card_cubo] at hc
  norm_num at hc

theorem non_simili_cubo_dodecaedro : ¬ ConvexPolytope.Similar cuboBM dodecaedroBM := by
  intro h
  have hc := vertices_card_of_similar h
  rw [show (dodecaedroBM).vertices.card = _ from card_dodeca,
    show (cuboBM).vertices.card = _ from card_cubo] at hc
  norm_num at hc

theorem non_simili_cubo_icosaedro : ¬ ConvexPolytope.Similar cuboBM icosaedroBM := by
  intro h
  have hc := vertices_card_of_similar h
  rw [show (icosaedroBM).vertices.card = _ from card_icosa,
    show (cuboBM).vertices.card = _ from card_cubo] at hc
  norm_num at hc

theorem non_simili_ottaedro_dodecaedro : ¬ ConvexPolytope.Similar ottaedroBM dodecaedroBM := by
  intro h
  have hc := vertices_card_of_similar h
  rw [show (dodecaedroBM).vertices.card = _ from card_dodeca,
    show (ottaedroBM).vertices.card = _ from card_otta] at hc
  norm_num at hc

theorem non_simili_ottaedro_icosaedro : ¬ ConvexPolytope.Similar ottaedroBM icosaedroBM := by
  intro h
  have hc := vertices_card_of_similar h
  rw [show (icosaedroBM).vertices.card = _ from card_icosa,
    show (ottaedroBM).vertices.card = _ from card_otta] at hc
  norm_num at hc

theorem non_simili_dodecaedro_icosaedro : ¬ ConvexPolytope.Similar dodecaedroBM icosaedroBM := by
  intro h
  have hc := vertices_card_of_similar h
  rw [show (icosaedroBM).vertices.card = _ from card_icosa,
    show (dodecaedroBM).vertices.card = _ from card_dodeca] at hc
  norm_num at hc

end

end LeanEval.Geometry.PlatonicClassification
