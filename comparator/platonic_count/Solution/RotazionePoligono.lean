import Mathlib
import Solution.Fondamenta
import Solution.CatenaAE
import Solution.Ordine
import Solution.OrbitaTraslata
import Solution.R2Base

/-!
L1 — LA ROTAZIONE DEL POLIGONO (campagna #50, G1-mio).

Nel modello 2D, l'isometria affine χ del poligono orbitale, letta attorno al
suo centro fisso cc, è una ROTAZIONE di ordine additivo esattamente p sui
raggi dₖ = zₖ − cc: i raggi sono non nulli (cocircolarità + iniettività),
il passo è la parte lineare, la riflessione è esclusa dal
due-passi-non-torna (CatenaAE), l'ordine viene da A4. Esporta l'orbita dei
raggi in forma rotazionale: χ^[k] 0 − cc = rot(θ)^[k] (0 − cc).
-/

open Real
open scoped RealInnerProductSpace
open CatenaAE PlatoniciA4

namespace PlatoniciL1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- LA ROTAZIONE DEL POLIGONO: l'isometria del ciclo, letta attorno al
centro fisso, è una rotazione di ordine additivo p sui raggi. -/
theorem rotazione_del_poligono (o : Orientation ℝ E (Fin 2))
    (χ : E ≃ᵃⁱ[ℝ] E) (cc : E) (hcc : χ cc = cc)
    {p : ℕ} (hp : 3 ≤ p) (hclosed : (⇑χ)^[p] (0 : E) = 0)
    (hinj : Function.Injective (fun i : Fin p => (⇑χ)^[(i : ℕ)] (0 : E))) :
    ∃ θ : Real.Angle, addOrderOf θ = p ∧
      ∀ k : ℕ, (⇑χ)^[k] (0 : E) - cc
        = (⇑(o.rotation θ))^[k] ((0 : E) - cc) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
  set L : E ≃ₗᵢ[ℝ] E := χ.linearIsometryEquiv with hLdef
  -- il passo dei raggi è la parte lineare
  have hstep : ∀ z : E, χ z - cc = L (z - cc) := by
    intro z
    have h := χ.map_vsub z cc
    rw [hcc] at h
    simpa using h.symm
  have horb : ∀ k : ℕ, (⇑χ)^[k] (0 : E) - cc = (⇑L)^[k] ((0 : E) - cc) := by
    intro k
    induction k with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          hstep, ih]
  -- la famiglia dei raggi
  set d : Fin (m + 2) → E := fun i => (⇑χ)^[(i : ℕ)] (0 : E) - cc with hddef
  have hdinj : Function.Injective d := by
    intro i j hij
    apply hinj
    have := congrArg (fun z => z + cc) hij
    simpa [hddef] using this
  -- passo con avvolgimento
  have hdstep : ∀ i : Fin (m + 2), L (d i) = d (finRotate (m + 2) i) := by
    intro i
    have hL1 : L (d i) = (⇑χ)^[(i : ℕ) + 1] (0 : E) - cc := by
      show L ((⇑χ)^[(i : ℕ)] 0 - cc) = _
      rw [← hstep, Function.iterate_succ_apply']
    by_cases hi : (i : ℕ) + 1 < m + 2
    · have hval : ((finRotate (m + 2) i : Fin (m + 2)) : ℕ) = (i : ℕ) + 1 := by
        rw [finRotate_apply]
        exact Fin.val_add_one_of_lt' (by simpa using hi)
      rw [hL1]
      show _ = (⇑χ)^[((finRotate (m + 2) i : Fin (m + 2)) : ℕ)] 0 - cc
      rw [hval]
    · have hlast : (i : ℕ) + 1 = m + 2 := by
        have := i.isLt
        omega
      have hilast : i = Fin.last (m + 1) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      rw [hL1, hlast, hclosed, hilast, finRotate_last]
      show (0 : E) - cc = (⇑χ)^[((0 : Fin (m + 2)) : ℕ)] 0 - cc
      rfl
  -- i raggi non sono nulli (cocircolarità)
  have hcoc := orbita_cocircolare χ 0 cc hcc
  have hdne : ∀ i, d i ≠ 0 := by
    intro i h0
    have hzi : (⇑χ)^[(i : ℕ)] (0 : E) = cc := by
      have := congrArg (fun z => z + cc) h0
      simpa [hddef] using this
    have hd0 : dist ((0 : E)) cc = 0 := by
      have h1 := hcoc (i : ℕ)
      rw [hzi] at h1
      simpa using h1.symm
    have hcc0 : cc = 0 := by
      have := dist_eq_zero.mp hd0
      exact this.symm
    have hz1 : (⇑χ)^[((1 : Fin (m + 2)) : ℕ)] (0 : E) = 0 := by
      have h1 := hcoc ((1 : Fin (m + 2)) : ℕ)
      rw [hcc0] at h1
      have h2 : dist ((⇑χ)^[((1 : Fin (m + 2)) : ℕ)] (0 : E)) 0 = 0 := by
        rw [h1]
        simp
      exact dist_eq_zero.mp h2
    have h10 : (1 : Fin (m + 2)) = 0 := by
      apply hinj
      show (⇑χ)^[((1 : Fin (m + 2)) : ℕ)] (0 : E)
        = (⇑χ)^[((0 : Fin (m + 2)) : ℕ)] 0
      rw [hz1]
      rfl
    have hval := congrArg Fin.val h10
    simp [Fin.val_one] at hval
  -- la rotazione e il suo ordine
  obtain ⟨θ, hθ⟩ : ∃ θ : Real.Angle, L = o.rotation θ := by
    apply exists_rotation_of_two_step_ne o L (hdstep 0)
    rw [hdstep (finRotate (m + 2) 0)]
    intro hcontra
    exact finRotate_due_ne hp 0 (hdinj hcontra)
  have hord : addOrderOf θ = m + 2 := by
    apply ordine_del_passo o θ (m + 2) hp d hdne
    · intro i
      rw [← hθ]
      exact (hdstep i).symm
    · exact hdinj
  refine ⟨θ, hord, ?_⟩
  intro k
  have hLrot : (⇑L) = ⇑(o.rotation θ) := by rw [hθ]
  rw [horb, hLrot]

end PlatoniciL1
