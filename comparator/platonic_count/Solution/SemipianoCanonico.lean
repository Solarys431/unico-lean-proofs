import Mathlib
import Challenge
import Solution.PianoDaiRaggi

/-!
RIGIDITÀ — IL SEMIPIANO COME DATO CANONICO (19 lug 2026).

Il lemma centrale isolato da Daniele: il semipiano della faccetta non si
sceglie, si RICOSTRUISCE da dati invarianti del fan marcato (il raggio
dello spigolo e il raggio precedente). Traslando tutto nel vertice, il
funzionale espositore si annulla sul raggio dello spigolo ed è
strettamente negativo sul raggio precedente; questi due fatti bastano a
determinare il semipiano, e due funzionali che li condividono
individuano LO STESSO semipiano.

La dimostrazione non ha bisogno di proporzionalità fra i funzionali:
decomponendo `x = a • u + b • r`, ogni funzionale che si annulla su `u`
vale `b * (valore su r)`, e con entrambi i valori negativi il segno
dipende solo da `b`. La forma affine (quella d'uso) segue traslando.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Nel piano generato da `u` e `r`, un funzionale che si annulla su `u`
vale il coefficiente di `r` per il suo valore su `r`. -/
theorem valore_nel_piano {u r : E 3} {φ : E 3 →L[ℝ] ℝ} (hu : φ u = 0)
    {x : E 3} (hx : x ∈ Submodule.span ℝ ({u, r} : Set (E 3))) :
    ∃ b : ℝ, x - b • r ∈ Submodule.span ℝ ({u} : Set (E 3)) ∧
      φ x = b * φ r := by
  classical
  rw [Submodule.mem_span_pair] at hx
  obtain ⟨a, b, hab⟩ := hx
  refine ⟨b, ?_, ?_⟩
  · have h1 : x - b • r = a • u := by
      rw [← hab]
      abel
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · rw [← hab]
    simp [hu]

/-- **IL SEMIPIANO È DETERMINATO** (forma lineare): due funzionali che si
annullano sul raggio dello spigolo e sono entrambi strettamente negativi
sul raggio precedente individuano lo stesso semipiano. -/
theorem semipiano_eq_di_segni {u r : E 3} {φ ψ : E 3 →L[ℝ] ℝ}
    (hφu : φ u = 0) (hψu : ψ u = 0)
    (hφr : φ r < 0) (hψr : ψ r < 0)
    {x : E 3} (hx : x ∈ Submodule.span ℝ ({u, r} : Set (E 3))) :
    φ x ≤ 0 ↔ ψ x ≤ 0 := by
  classical
  -- UNA sola decomposizione, usata per entrambi i funzionali: così il
  -- coefficiente è lo stesso e non serve l'unicità della scrittura
  rw [Submodule.mem_span_pair] at hx
  obtain ⟨a, b, hab⟩ := hx
  have hφx : φ x = b * φ r := by
    rw [← hab]
    simp [hφu]
  have hψx : ψ x = b * ψ r := by
    rw [← hab]
    simp [hψu]
  rw [hφx, hψx]
  constructor
  · intro h
    have hb : 0 ≤ b := by nlinarith
    nlinarith
  · intro h
    have hb : 0 ≤ b := by nlinarith
    nlinarith

/-- **LA FORMA AFFINE**, quella d'uso: traslando nel vertice, il semipiano
della faccetta delimitato dalla retta dello spigolo è lo stesso per due
funzionali che concordano sui due segni canonici. -/
theorem semipiano_affine_eq {v u r : E 3} {φ ψ : E 3 →L[ℝ] ℝ}
    (hφu : φ u = 0) (hψu : ψ u = 0)
    (hφr : φ r < 0) (hψr : ψ r < 0) :
    {z : E 3 | z - v ∈ Submodule.span ℝ ({u, r} : Set (E 3)) ∧
        φ (z - v) ≤ 0} =
      {z : E 3 | z - v ∈ Submodule.span ℝ ({u, r} : Set (E 3)) ∧
        ψ (z - v) ≤ 0} := by
  ext z
  constructor
  · rintro ⟨hspan, hle⟩
    exact ⟨hspan, (semipiano_eq_di_segni hφu hψu hφr hψr hspan).mp hle⟩
  · rintro ⟨hspan, hle⟩
    exact ⟨hspan, (semipiano_eq_di_segni hφu hψu hφr hψr hspan).mpr hle⟩

/-- Il controllo di non nullità: se il funzionale si annulla anche sul
raggio precedente, il piano intero è nel suo nucleo — cioè la faccetta
coinciderebbe con la retta dello spigolo. La stretta negatività è dunque
la forma corretta dell'ipotesi. -/
theorem non_degenere_di_stretto {r : E 3} {φ : E 3 →L[ℝ] ℝ}
    (hφr : φ r < 0) : φ r ≠ 0 := ne_of_lt hφr

end LeanEval.Geometry.PlatonicClassification
