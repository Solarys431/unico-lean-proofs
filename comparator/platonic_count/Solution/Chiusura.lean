import Mathlib
import Challenge
import Solution.FacceConnesse
import Solution.Coincidenza
import Solution.Connessa
import Solution.VerticiFaccette

/-!
RIGIDITÀ, GATE 4 — LA CHIUSURA PER ADIACENZA DAL FAN (19 lug 2026).

Il passo che mancava all'induzione per coincidenza: se i due politopi
hanno gli stessi fan a ogni vertice comune, allora l'insieme delle
faccette comuni è chiuso per adiacenza, e quindi (con Balinski e la
connettività globale, già in casa) i due politopi COINCIDONO.

Il perno è che i vertici di una faccia non dipendono dal politopo
ambiente (`vertici_faccia_estremi`): perciò da una faccetta comune si
eredita un vertice comune, e lì il fan fa il resto.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Un vertice di P dentro una faccia comune è vertice anche di Q. -/
theorem vertice_comune_di_faccia_comune (P Q : ConvexPolytope 3)
    {A : Set (E 3)} (hAP : P.IsFace A) (hAQ : Q.IsFace A)
    {v : E 3} (hvP : v ∈ P.vertices) (hvA : v ∈ A) :
    v ∈ Q.vertices := by
  classical
  have h1 : v ∈ P.vertices.filter (· ∈ A) :=
    Finset.mem_filter.mpr ⟨hvP, hvA⟩
  have h2 : v ∈ (((facePolytope P hAP).vertices : Finset (E 3)) :
      Set (E 3)) := Finset.mem_coe.mpr h1
  rw [vertici_faccia_estremi P hAP] at h2
  have h3 : v ∈ (((facePolytope Q hAQ).vertices : Finset (E 3)) :
      Set (E 3)) := by
    rw [vertici_faccia_estremi Q hAQ]
    exact h2
  exact vertice_di_faccetta Q hAQ (Finset.mem_coe.mp h3)

/-- Ogni faccia non vuota contiene un vertice del politopo. -/
theorem faccia_ha_vertice (P : ConvexPolytope 3) {A : Set (E 3)}
    (hA : P.IsFace A) : ∃ u, u ∈ P.vertices ∧ u ∈ A :=
  faccetta_ha_vertice P hA

/-- **IL GATE 4**: fan uguali a ogni vertice comune ⟹ le faccette comuni
sono chiuse per adiacenza. -/
theorem chiusura_da_fan (P Q : ConvexPolytope 3)
    (hfan : ∀ v : E 3, v ∈ P.vertices → v ∈ Q.vertices →
      ∀ F : Set (E 3),
        (P.IsFace F ∧ faceDim F = 2 ∧ v ∈ F) →
        (Q.IsFace F ∧ faceDim F = 2 ∧ v ∈ F)) :
    ∀ A, FaccettaComune P Q A →
      ∀ B, FaccetteAdiacenti P A B → FaccettaComune P Q B := by
  classical
  rintro A ⟨⟨hAP, hdAP⟩, ⟨hAQ, hdAQ⟩⟩ B ⟨⟨hBP, hdBP⟩, δ, hδ, hdδ, hδA, hδB⟩
  -- un vertice sullo spigolo comune
  obtain ⟨v, hvP, hvδ⟩ := faccia_ha_vertice P hδ
  have hvA : v ∈ A := hδA hvδ
  have hvB : v ∈ B := hδB hvδ
  have hvQ : v ∈ Q.vertices :=
    vertice_comune_di_faccia_comune P Q hAP hAQ hvP hvA
  exact ⟨⟨hBP, hdBP⟩, ⟨(hfan v hvP hvQ B ⟨hBP, hdBP, hvB⟩).1,
    (hfan v hvP hvQ B ⟨hBP, hdBP, hvB⟩).2.1⟩⟩

/-- **LA COINCIDENZA DAL FAN**: fan uguali nei due versi a ogni vertice
comune, più una faccetta comune di partenza, danno lo stesso corpo. -/
theorem coincidenza_da_fan (P Q : ConvexPolytope 3)
    (hfullP : P.IsFullDim) (hfullQ : Q.IsFullDim)
    (hfanP : ∀ v : E 3, v ∈ P.vertices → v ∈ Q.vertices →
      ∀ F : Set (E 3),
        (P.IsFace F ∧ faceDim F = 2 ∧ v ∈ F) →
        (Q.IsFace F ∧ faceDim F = 2 ∧ v ∈ F))
    (hfanQ : ∀ v : E 3, v ∈ Q.vertices → v ∈ P.vertices →
      ∀ F : Set (E 3),
        (Q.IsFace F ∧ faceDim F = 2 ∧ v ∈ F) →
        (P.IsFace F ∧ faceDim F = 2 ∧ v ∈ F))
    (A₀ : Set (E 3)) (hA₀ : FaccettaComune P Q A₀) :
    P.toSet = Q.toSet := by
  refine coincidenza_da_chiusura P Q hfullP hfullQ
    (chiusura_da_fan P Q hfanP) ?_ A₀ hA₀
  -- il verso opposto: la chiusura nel grafo di Q
  rintro A ⟨⟨hAP, hdAP⟩, ⟨hAQ, hdAQ⟩⟩ B ⟨⟨hBQ, hdBQ⟩, δ, hδ, hdδ, hδA, hδB⟩
  obtain ⟨v, hvQ, hvδ⟩ := faccia_ha_vertice Q hδ
  have hvA : v ∈ A := hδA hvδ
  have hvB : v ∈ B := hδB hvδ
  have hvP : v ∈ P.vertices :=
    vertice_comune_di_faccia_comune Q P hAQ hAP hvQ hvA
  exact ⟨⟨(hfanQ v hvQ hvP B ⟨hBQ, hdBQ, hvB⟩).1,
    (hfanQ v hvQ hvP B ⟨hBQ, hdBQ, hvB⟩).2.1⟩, ⟨hBQ, hdBQ⟩⟩

end LeanEval.Geometry.PlatonicClassification
