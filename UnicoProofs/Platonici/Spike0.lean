import Mathlib

open InnerProductGeometry Real
open scoped RealInnerProductSpace

/-!
SPIKE-0 della campagna #50 (kill-gate): il cuore del lemma del difetto angolare.

Legge sferica dei coseni per il fan ciclico attorno a un vertice: se due spigoli
unitari u, u' giacciono sullo stesso cono attorno all'asse w (stessa colatitudine
0 < β < π/2, la strettezza viene dalla puntatezza del cono) e le loro proiezioni
nel piano ortogonale all'asse formano angolo θ ∈ (0, π], allora

    angle u u' < θ    (STRETTO).

Con θ = 2π/q e la simmetria ciclica del vertice questo dà q·α < 2π: il difetto
angolare di Euclide XIII.18, senza formula di Eulero né geometria sferica integrale.
-/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem spike_difetto_angolare
    (w e e' : V) (hw : ‖w‖ = 1) (he : ‖e‖ = 1) (he' : ‖e'‖ = 1)
    (hwe : ⟪w, e⟫ = 0) (hwe' : ⟪w, e'⟫ = 0)
    (β θ : ℝ) (hβ0 : 0 < β) (hβ1 : β < π / 2) (hθ0 : 0 < θ) (hθπ : θ ≤ π)
    (hee' : ⟪e, e'⟫ = Real.cos θ) :
    angle (Real.cos β • w + Real.sin β • e) (Real.cos β • w + Real.sin β • e') < θ := by
  set u  := Real.cos β • w + Real.sin β • e  with hu_def
  set u' := Real.cos β • w + Real.sin β • e' with hu'_def
  have hww : ⟪w, w⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hee : ⟪e, e⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, he]; norm_num
  have he'e' : ⟪e', e'⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, he']; norm_num
  have hew : ⟪e, w⟫ = 0 := by rw [real_inner_comm]; exact hwe
  have he'w : ⟪e', w⟫ = 0 := by rw [real_inner_comm]; exact hwe'
  -- il prodotto interno dei due spigoli: la legge sferica dei coseni
  have h1 : ⟪u, u'⟫ = Real.cos β ^ 2 + Real.sin β ^ 2 * Real.cos θ := by
    simp only [hu_def, hu'_def, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right,
      hww, hwe, hwe', hew, hee']
    ring
  -- entrambi gli spigoli sono unitari
  have hnorm : ∀ (x : V), ‖x‖ = 1 → ⟪w, x⟫ = 0 →
      ‖Real.cos β • w + Real.sin β • x‖ = 1 := by
    intro x hx hwx
    have hxw : ⟪x, w⟫ = 0 := by rw [real_inner_comm]; exact hwx
    have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
    have hsq : ‖Real.cos β • w + Real.sin β • x‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, hww, hwx, hxw, hxx]
      nlinarith [Real.sin_sq_add_cos_sq β]
    have hnn := norm_nonneg (Real.cos β • w + Real.sin β • x)
    nlinarith [hsq, hnn]
  have hu1 : ‖u‖ = 1 := hnorm e he hwe
  have hu'1 : ‖u'‖ = 1 := hnorm e' he' hwe'
  -- le disuguaglianze della stretta
  have hcosβ : 0 < Real.cos β :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ1⟩
  have hcosθ1 : Real.cos θ < 1 := by
    refine lt_of_le_of_ne (Real.cos_le_one θ) fun h => ?_
    have harc := Real.arccos_cos hθ0.le hθπ
    rw [h, Real.arccos_one] at harc
    linarith
  have hgt : Real.cos θ < Real.cos β ^ 2 + Real.sin β ^ 2 * Real.cos θ := by
    have key : 0 < Real.cos β ^ 2 * (1 - Real.cos θ) := by
      have := mul_pos hcosβ hcosβ
      nlinarith
    nlinarith [Real.sin_sq_add_cos_sq β]
  have hle1 : Real.cos β ^ 2 + Real.sin β ^ 2 * Real.cos θ ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq β, Real.neg_one_le_cos θ, sq_nonneg (Real.sin β)]
  -- la conclusione: angle = arccos e l'arccos è strettamente antitono
  have hangle : angle u u' = Real.arccos (Real.cos β ^ 2 + Real.sin β ^ 2 * Real.cos θ) := by
    rw [angle, h1, hu1, hu'1]
    norm_num
  have hlt := Real.arccos_lt_arccos (Real.neg_one_le_cos θ) hgt hle1
  rw [Real.arccos_cos hθ0.le hθπ] at hlt
  rw [hangle]
  exact hlt

-- Il corollario che il kill-gate esige: q angoli uguali attorno al vertice
-- (fan ciclico a passo θ = 2π/q) sommano STRETTAMENTE sotto 2π.
theorem spike_somma_sotto_due_pi
    (w e e' : V) (hw : ‖w‖ = 1) (he : ‖e‖ = 1) (he' : ‖e'‖ = 1)
    (hwe : ⟪w, e⟫ = 0) (hwe' : ⟪w, e'⟫ = 0)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < π / 2)
    (q : ℕ) (hq : 3 ≤ q)
    (hee' : ⟪e, e'⟫ = Real.cos (2 * π / q)) :
    (q : ℝ) * angle (Real.cos β • w + Real.sin β • e) (Real.cos β • w + Real.sin β • e')
      < 2 * π := by
  have hqpos : (0 : ℝ) < q := by positivity
  have hθ0 : 0 < 2 * π / q := by positivity
  have hθπ : 2 * π / q ≤ π := by
    rw [div_le_iff₀ hqpos]
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith [Real.pi_pos]
  have h := spike_difetto_angolare w e e' hw he he' hwe hwe' β (2 * π / q)
    hβ0 hβ1 hθ0 hθπ hee'
  calc (q : ℝ) * angle _ _ < (q : ℝ) * (2 * π / q) := by
        exact mul_lt_mul_of_pos_left h hqpos
    _ = 2 * π := by field_simp
