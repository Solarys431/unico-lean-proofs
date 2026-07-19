import Mathlib
import Challenge
import Solution.VerticiEsposti
import Solution.SottoPolitopo
import Solution.DimStretta
import Solution.Interpolazione
import Solution.ScalaBandiere
import Solution.BandieraCompagna
import Solution.Diamante
import Solution.Diamante2D
import Solution.SecondoSpigolo
import Solution.ConoVertice
import Solution.Camminata

/-!
FASE 3A, F9a — LA CONNETTIVITÀ DEL POLIGONO (18 lug 2026).

In un poligono (politopo di rango 2) il grafo dei vertici con gli spigoli
come lati è connesso: la camminata del simplesso con il potenziale dato
dall'espositore del vertice bersaglio. Il principio locale-globale è il
cono al vertice (ConoVertice); i vicini di un vertice sono gli altri
estremi dei suoi (esattamente due) spigoli; il massimo del potenziale è
unico per la caratterizzazione argmax del vertice esposto.

Prima un attrezzo: un vertice del politopo dentro uno spigolo-segmento ne
è un estremo (parametrizzazione + estremalità).
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Un vertice del politopo dentro un segmento ne è un estremo. -/
theorem vertice_estremo_del_segmento (P : ConvexPolytope n)
    {e : Set (E n)} (he : P.IsFace e)
    {a b : E n} (hseg : e = segment ℝ a b) (hab : a ≠ b)
    {x : E n} (hxV : x ∈ P.vertices) (hxe : x ∈ e) :
    x = a ∨ x = b := by
  classical
  by_contra hcon
  push_neg at hcon
  have hex : x ∈ e.extremePoints ℝ := vertice_estremo_in_faccia P he hxV hxe
  have hxseg : x ∈ segment ℝ a b := by
    rw [← hseg]
    exact hxe
  obtain ⟨s, t, hs, ht, hst, hx⟩ := hxseg
  have hae : a ∈ e := by
    rw [hseg]
    exact left_mem_segment ℝ a b
  have hbe : b ∈ e := by
    rw [hseg]
    exact right_mem_segment ℝ a b
  -- s e t sono entrambi positivi, altrimenti x sarebbe un estremo
  have hspos : 0 < s := by
    rcases lt_or_eq_of_le hs with h | h
    · exact h
    · exfalso
      apply hcon.2
      have ht1 : t = 1 := by
        rw [← h] at hst
        simpa using hst
      rw [← hx, ← h, ht1]
      simp
  have htpos : 0 < t := by
    rcases lt_or_eq_of_le ht with h | h
    · exact h
    · exfalso
      apply hcon.1
      have hs1 : s = 1 := by
        rw [← h] at hst
        simpa using hst
      rw [← hx, ← h, hs1]
      simp
  have hopen : x ∈ openSegment ℝ a b := ⟨s, t, hspos, htpos, hst, hx⟩
  have h2 := hex.2 hae hbe hopen
  exact hcon.1 h2.symm

/-- **LA CONNETTIVITÀ DEL POLIGONO**: due vertici qualsiasi di un poligono
sono collegati da un cammino di spigoli (la relazione: essere entrambi
vertici del politopo dentro uno spigolo comune, con estremi distinti). -/
theorem poligono_connesso (Q : ConvexPolytope n)
    (hdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = 2)
    {x₀ xs : E n} (hx₀ : x₀ ∈ Q.vertices) (hxs : xs ∈ Q.vertices) :
    Relation.ReflTransGen
      (fun p q => q ∈ Q.vertices ∧ p ≠ q ∧
        ∃ e : Set (E n), Q.IsFace e ∧ faceDim e = 1 ∧ p ∈ e ∧ q ∈ e)
      x₀ xs := by
  classical
  -- il potenziale: l'espositore del vertice bersaglio
  obtain ⟨l, hl⟩ := (vertex_isFace Q hxs).1 (Set.singleton_nonempty xs)
  have hxsT : xs ∈ Q.toSet := by
    have h1 : xs ∈ ({xs} : Set (E n)) := rfl
    rw [hl] at h1
    exact h1.1
  have hlmax : ∀ y ∈ Q.toSet, l y ≤ l xs := by
    have h1 : xs ∈ ({xs} : Set (E n)) := rfl
    rw [hl] at h1
    exact h1.2
  have hlchar : ∀ q ∈ Q.toSet, l q = l xs → q = xs := by
    intro q hq hlq
    have h1 : q ∈ ({xs} : Set (E n)) := by
      rw [hl]
      exact ⟨hq, fun y hy => le_trans (hlmax y hy) (le_of_eq hlq.symm)⟩
    exact h1
  -- la camminata astratta con X = vertici, adiacenza via spigoli
  have hcam := camminata_del_simplesso (α := E n) Q.vertices
    (fun p q => p ≠ q ∧
      ∃ e : Set (E n), Q.IsFace e ∧ faceDim e = 1 ∧ p ∈ e ∧ q ∈ e)
    (fun y => l y) ?_ hxs ?_ hx₀
  · -- adattamento della relazione
    refine Relation.ReflTransGen.mono ?_ hcam
    rintro p q ⟨hqX, hpq, e, he⟩
    exact ⟨hqX, hpq, e, he⟩
  · -- il principio locale-globale
    intro w hwV hloc z hzV
    -- i due spigoli di w nel poligono
    have hwT : w ∈ Q.toSet := subset_convexHull ℝ _ hwV
    have hvface : Q.IsFace ({w} : Set (E n)) := vertex_isFace Q hwV
    have hgap : faceDim ({w} : Set (E n)) + 2 ≤
        Module.finrank ℝ (vectorSpan ℝ Q.toSet) := by
      rw [faceDim_singleton, hdim]
    obtain ⟨e₁, he₁, hwe₁, he₁ne⟩ := interpolazione Q hvface hgap
    have hde₁ : faceDim e₁ = 1 := by
      have h1 := faceDim_lt_of_ssubset Q hvface he₁ hwe₁
      rw [faceDim_singleton] at h1
      have hss : e₁ ⊂ Q.toSet :=
        ⟨face_subset_toSet Q he₁, fun hsup => he₁ne
          (Set.Subset.antisymm (face_subset_toSet Q he₁) hsup)⟩
      have h2 := faceDim_lt_of_ssubset Q he₁ (toSet_isFace Q) hss
      have h3 : faceDim Q.toSet = 2 := hdim
      omega
    have hwmem₁ : w ∈ e₁ := hwe₁.subset rfl
    obtain ⟨e₂, he₂, hde₂, hwmem₂, he₂ne⟩ := secondo_spigolo Q hdim hwV
      he₁ hde₁ hwmem₁
    -- gli estremi dei due spigoli
    obtain ⟨a, haV, hae, haw, hsega⟩ := spigolo_segmento Q he₁ hde₁ hwV hwmem₁
    obtain ⟨b, hbV, hbe, hbw, hsegb⟩ := spigolo_segmento Q he₂ hde₂ hwV hwmem₂
    -- gli estremi sono vicini nel grafo: il potenziale non cresce
    have hha : l a ≤ l w := by
      apply hloc a haV
      exact ⟨fun h => haw h.symm, e₁, he₁, hde₁, hwmem₁, hae⟩
    have hhb : l b ≤ l w := by
      apply hloc b hbV
      exact ⟨fun h => hbw h.symm, e₂, he₂, hde₂, hwmem₂, hbe⟩
    -- il locale-globale del cono
    have := locale_globale Q hdim hwV he₁ hde₁ he₂ hde₂
      (fun h => he₂ne h.symm) hae haw hsega hbe hbw hsegb hwmem₁ hwmem₂
      l hha hhb
    exact this z (subset_convexHull ℝ _ hzV)
  · -- il massimo è unico
    intro z hzV hzne
    have hzT : z ∈ Q.toSet := subset_convexHull ℝ _ hzV
    rcases lt_or_eq_of_le (hlmax z hzT) with h | h
    · exact h
    · exact absurd (hlchar z hzT h) hzne

end LeanEval.Geometry.PlatonicClassification
