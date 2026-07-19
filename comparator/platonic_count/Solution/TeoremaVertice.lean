import Mathlib
import Solution.Fondamenta
import Solution.Asse
import Solution.CatenaAE
import Solution.Killer
import Solution.Ordine
import Solution.PonteSpike
import Solution.Colatitudine
import Solution.Carta
import Solution.Spike0
import Solution.Espositore

/-!
A11 — IL TEOREMA DEL VERTICE (campagna #50, assemblaggio, metà pesante).

Da un vertice q-ciclico di un politopo 3-dimensionale, SENZA toccare la
struttura interna delle faccette: q · ∠(u₀, u₁) < 2π, dove u₀, u₁ sono le
direzioni dei due spigoli della faccetta base del fan. La catena completa:

fan (A9) → espositore → asse e puntatezza (Asse) → colatitudine c ∈ (0,1)
(A6) → scomposizione assiale u = c·ŵ + s·ê (A5) → discesa a V₃ (A7) →
piano ortogonale e restrizione (CatenaAE) → rotazione (CatenaAE) → ordine q
del passo (A4) → funzionale della faccetta (A3) → vettore di Riesz (A7) →
massimo del coseno in {0,1} ⟹ passo ±2π/q (killer) → ⟪ê₀,ê₁⟫ = cos(2π/q)
(A5) → spike del difetto angolare (Spike-0) ⟹ q·α < 2π.

L'altra metà (α = (p−2)π/p dalla faccetta regolare, via carta A8 + orbita
traslata A10 + facce esposte G1) chiude il teorema di classificazione.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace
open FiniteConvexPolytope CatenaAE PlatoniciA4 PlatoniciA5 PlatoniciA6 PlatoniciA7

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- IL TEOREMA DEL VERTICE: in un politopo con vectorSpan 3-dimensionale,
un vertice q-ciclico apre tra i due spigoli consecutivi del fan un angolo α
con q·α < 2π. -/
theorem vertice_q_angolo (P : FiniteConvexPolytope A) {v : A}
    (hv : v ∈ P.vertices) {n : ℕ} (hq : 3 ≤ n + 1)
    (D : P.CyclicVertexData v (n + 1))
    (h3 : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3) :
    ((n + 1 : ℕ) : ℝ) * angle (dir P v D 0) (dir P v D (finRotate (n + 1) 0))
      < 2 * π := by
  -- ══ 0. il vertice è estremo ══
  have hvex : v ∈ P.toSet.extremePoints ℝ := by
    rw [FiniteConvexPolytope.toSet, ← P.vertices_eq_extremePoints]
    exact hv
  -- ══ 1. il fan: direzioni unitarie, passo, iniettività ══
  set L : A ≃ₗᵢ[ℝ] A := D.σ.linearIsometryEquiv with hLdef
  set u : Fin (n + 1) → A := dir P v D with hudef
  have hu1 : ∀ i, ‖u i‖ = 1 := fun i => dir_unitaria P v D i
  have hL : ∀ i, L (u i) = u (finRotate (n + 1) i) := fun i =>
    dir_passo P v hq D hvex i
  have hinj : Function.Injective u := dir_iniettiva P v hq D
  -- ══ 2. l'espositore del vertice e la positività sulle direzioni ══
  obtain ⟨f, hf⟩ := P.vertice_espositore v hv
  have hfu : ∀ i, 0 < f (u i) := by
    intro i
    have hs := punto_spec P v D i
    have hmem : punto P v D i ∈ P.toSet :=
      (D.isFacet i).1.1.subset hs.2.1
    have hlt := hf (punto P v D i) hmem hs.1
    have hnp : (0 : ℝ) < ‖punto P v D i - v‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hs.1)
    have : f (u i) = ‖punto P v D i - v‖⁻¹ * (f (punto P v D i) - f v) := by
      rw [hudef]
      show f (‖punto P v D i - v‖⁻¹ • (punto P v D i - v)) = _
      rw [map_smul, map_sub]
      rfl
    rw [this]
    exact mul_pos (inv_pos.mpr hnp) (by linarith)
  -- ══ 3. l'asse e la colatitudine ══
  set w : A := ∑ i, u i with hwdef
  have hw0 : w ≠ 0 := asse_non_nullo u f hfu (by omega)
  have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw0
  set ŵ : A := ‖w‖⁻¹ • w with hŵdef
  have hŵ1 : ‖ŵ‖ = 1 := by
    rw [hŵdef, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (ne_of_gt hwpos)]
  set c : ℝ := ⟪ŵ, u 0⟫ with hcdef
  have hccol : ∀ j, ⟪ŵ, u j⟫ = c := by
    intro j
    rw [hcdef, hŵdef, real_inner_smul_left, real_inner_smul_left]
    congr 1
    rw [real_inner_comm (u j) w, real_inner_comm (u 0) w]
    exact colatitudine_comune L u hL j 0
  have hc0 : (0 : ℝ) < c := by
    have hp := puntatezza L u hL f hfu 0
    rw [hcdef, hŵdef, real_inner_smul_left, real_inner_comm (u 0) w]
    exact mul_pos (inv_pos.mpr hwpos) hp
  have hc1 : c < 1 := by
    have h := PlatoniciA6.colatitudine_sotto_uno (by omega : 1 ≤ n)
      L u hu1 hL hinj 0
    rw [hcdef, real_inner_comm (u 0) ŵ, hŵdef, hwdef]
    exact h
  -- ══ 4. β = arccos c ══
  obtain ⟨β, hβ0, hβπ2, hcos, hsin⟩ := beta_di_colatitudine hc0 hc1
  set s : ℝ := Real.sqrt (1 - c ^ 2) with hsdef
  have hs0 : (0 : ℝ) < s := by
    rw [hsdef]
    apply Real.sqrt_pos.mpr
    nlinarith
  -- ══ 5. la scomposizione assiale come famiglia ══
  choose e he1 he2 he3 using fun j =>
    scomposizione_assiale ŵ (u j) hŵ1 (hu1 j) (hccol j) hc0 hc1
  have hLŵ : L ŵ = ŵ := by
    rw [hŵdef, hwdef]
    exact PlatoniciA6.asse_normalizzato_fisso L u hL
  have hLw : L w = w := by
    rw [hwdef]
    exact asse_invariante L u hL
  have hestep : ∀ j, L (e j) = e (finRotate (n + 1) j) := by
    intro j
    have h1 := congrArg L (he3 j)
    rw [map_add, map_smul, map_smul, map_smul, hLw, hL] at h1
    have h2 := he3 (finRotate (n + 1) j)
    rw [h1] at h2
    have h3 := add_left_cancel h2
    exact smul_right_injective A (ne_of_gt hs0) h3
  have heinj : Function.Injective e := by
    intro i j hij
    apply hinj
    rw [he3 i, he3 j, hij]
  have hene : ∀ j, e j ≠ 0 := by
    intro j h0
    have := he1 j
    rw [h0, norm_zero] at this
    norm_num at this
  -- ══ 6. la discesa a V₃ ══
  set W₃ : Submodule ℝ A := vectorSpan ℝ P.toSet with hW₃def
  haveI hfin3 : FiniteDimensional ℝ W₃ := by
    have h31 : Module.finrank ℝ W₃ = 2 + 1 := by omega
    exact Module.finite_of_finrank_eq_succ h31
  haveI hfact3 : Fact (Module.finrank ℝ W₃ = 3) := ⟨h3⟩
  have humem : ∀ i, u i ∈ W₃ := by
    intro i
    have hs := punto_spec P v D i
    have hx : punto P v D i ∈ P.toSet := (D.isFacet i).1.1.subset hs.2.1
    have hvmem : v ∈ P.toSet := by
      have := hvex.1
      exact this
    have hd : punto P v D i - v ∈ W₃ := by
      simpa using vsub_mem_vectorSpan ℝ hx hvmem
    rw [hudef]
    show ‖punto P v D i - v‖⁻¹ • (punto P v D i - v) ∈ W₃
    exact W₃.smul_mem _ hd
  have hwmem : w ∈ W₃ := by
    rw [hwdef]
    exact Submodule.sum_mem _ fun i _ => humem i
  have hŵmem : ŵ ∈ W₃ := by
    rw [hŵdef]
    exact W₃.smul_mem _ hwmem
  have hemem : ∀ j, e j ∈ W₃ := by
    intro j
    have h1 : e j = s⁻¹ • (u j - c • ŵ) := by
      have := he3 j
      rw [this]
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (ne_of_gt hs0),
        one_smul]
    rw [h1]
    exact W₃.smul_mem _ (Submodule.sub_mem _ (humem j) (W₃.smul_mem _ hŵmem))
  set L₃ := discesa D.σ P.toSet D.preserva with hL₃def
  have hL₃coe : ∀ z : ↥W₃, (L₃ z : A) = L (z : A) := fun z => rfl
  set ŵ₃ : ↥W₃ := ⟨ŵ, hŵmem⟩ with hŵ₃def
  have hŵ₃ne : ŵ₃ ≠ 0 := by
    intro h0
    have h1 : ŵ = 0 := congrArg Subtype.val h0
    rw [h1, norm_zero] at hŵ1
    norm_num at hŵ1
  have hL₃ŵ : L₃ ŵ₃ = ŵ₃ := by
    apply Subtype.ext
    rw [hL₃coe]
    exact hLŵ
  -- ══ 7. il piano ortogonale, l'orientazione, la restrizione ══
  set E₂ : Submodule ℝ ↥W₃ := (ℝ ∙ ŵ₃)ᗮ with hE₂def
  have h2 : Module.finrank ℝ E₂ = 2 :=
    finrank_orthogonal_span_eq_two hŵ₃ne
  haveI hfact2 : Fact (Module.finrank ℝ E₂ = 2) := ⟨h2⟩
  set o : Orientation ℝ E₂ (Fin 2) := orientazione2 E₂ h2 with hodef
  set f₂ := restrizione L₃ ŵ₃ hL₃ŵ with hf₂def
  have hemem₂ : ∀ j, (⟨e j, hemem j⟩ : ↥W₃) ∈ E₂ := by
    intro j
    rw [hE₂def, Submodule.mem_orthogonal_singleton_iff_inner_right]
    show ⟪ŵ, e j⟫ = 0
    exact he2 j
  set ě : Fin (n + 1) → ↥E₂ := fun j => ⟨⟨e j, hemem j⟩, hemem₂ j⟩ with hědef
  have hěcoe : ∀ j, ((ě j : ↥W₃) : A) = e j := fun j => rfl
  have hěne : ∀ j, ě j ≠ 0 := by
    intro j h0
    apply hene j
    have := congrArg (fun z : ↥E₂ => ((z : ↥W₃) : A)) h0
    simpa [hěcoe] using this
  have hěinj : Function.Injective ě := by
    intro i j hij
    apply heinj
    have := congrArg (fun z : ↥E₂ => ((z : ↥W₃) : A)) hij
    simpa [hěcoe] using this
  have hf₂coe : ∀ z : ↥E₂, ((f₂ z : ↥W₃) : A) = L ((z : ↥W₃) : A) :=
    fun z => rfl
  have hstep₂ : ∀ j, f₂ (ě j) = ě (finRotate (n + 1) j) := by
    intro j
    apply Subtype.ext
    apply Subtype.ext
    show ((f₂ (ě j) : ↥W₃) : A) = e (finRotate (n + 1) j)
    rw [hf₂coe, hěcoe]
    exact hestep j
  -- ══ 8. la rotazione e l'ordine del passo ══
  obtain ⟨θ, hθ⟩ : ∃ θ : Real.Angle, f₂ = o.rotation θ := by
    apply exists_rotation_of_two_step_ne o f₂ (hstep₂ 0)
    rw [hstep₂ (finRotate (n + 1) 0)]
    intro hcontra
    exact finRotate_due_ne hq 0 (hěinj hcontra)
  have hstepr : ∀ j, ě (finRotate (n + 1) j) = o.rotation θ (ě j) := by
    intro j
    rw [← hθ]
    exact (hstep₂ j).symm
  have hord : addOrderOf θ = n + 1 :=
    ordine_del_passo o θ (n + 1) hq ě hěne hstepr hěinj
  -- ══ 9. il funzionale della faccetta base e il vettore di Riesz ══
  obtain ⟨l, hleq, hllt⟩ := funzionale_faccetta P D (finRotate (n + 1) 0)
  set l₃ : ↥W₃ →L[ℝ] ℝ := l.comp W₃.subtypeL with hl₃def
  set nn : ↥E₂ := riesz_sotto E₂ l₃ with hnndef
  have hnn_spec : ∀ z : ↥E₂, ⟪nn, z⟫ = l ((z : ↥W₃) : A) := by
    intro z
    rw [hnndef]
    rw [riesz_sotto_spec]
    rfl
  -- l sulle direzioni: zero sugli spigoli propri, negativo sugli altri
  have hlu : ∀ j, l (u j) = ‖punto P v D j - v‖⁻¹ * (l (punto P v D j) - l v) := by
    intro j
    rw [hudef]
    show l (‖punto P v D j - v‖⁻¹ • (punto P v D j - v)) = _
    rw [map_smul, map_sub]
    rfl
  have hlu0 : l (u 0) = 0 := by
    have hs := punto_spec P v D 0
    have hmem : punto P v D 0 ∈ D.faccetta (finRotate (n + 1) 0) := hs.2.2
    have := hleq (punto P v D 0) hmem
    rw [hlu 0, this]
    ring
  have hlu1 : l (u (finRotate (n + 1) 0)) = 0 := by
    have hs := punto_spec P v D (finRotate (n + 1) 0)
    have hmem : punto P v D (finRotate (n + 1) 0)
        ∈ D.faccetta (finRotate (n + 1) 0) := hs.2.1
    have := hleq _ hmem
    rw [hlu _, this]
    ring
  have hluneg : ∀ j : Fin (n + 1), j ≠ 0 → j ≠ finRotate (n + 1) 0 →
      l (u j) < 0 := by
    intro j hj0 hj1
    have hs := punto_spec P v D j
    have hstrict := hllt j hj1
      (fun h => hj0 ((finRotate (n + 1)).injective h))
      (punto P v D j) hs.2 hs.1
    have hnp : (0 : ℝ) < ‖punto P v D j - v‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hs.1)
    rw [hlu j]
    apply mul_neg_of_pos_of_neg (inv_pos.mpr hnp)
    linarith
  -- decomposizione di l lungo asse e piano
  have hldec : ∀ j, l (u j) = c * l ŵ + s * ⟪nn, ě j⟫ := by
    intro j
    have h1 : l (u j) = l (c • ŵ + Real.sqrt (1 - c ^ 2) • e j) := by
      rw [← he3 j]
    have h2 : l (c • ŵ) = c * l ŵ := by
      rw [map_smul]
      rfl
    have h4 : l (Real.sqrt (1 - c ^ 2) • e j) = s * l (e j) := by
      rw [map_smul]
      rfl
    rw [h1, map_add, h2, h4, hnn_spec (ě j), hěcoe]
  have hkeq : ⟪nn, ě (finRotate (n + 1) 0)⟫ = ⟪nn, ě 0⟫ := by
    have h0 := hldec 0
    have h1 := hldec (finRotate (n + 1) 0)
    rw [hlu0] at h0
    rw [hlu1] at h1
    have h2 : s * ⟪nn, ě (finRotate (n + 1) 0)⟫ = s * ⟪nn, ě 0⟫ := by
      linarith
    exact mul_left_cancel₀ (ne_of_gt hs0) h2
  have hklt : ∀ j : Fin (n + 1), j ≠ 0 → j ≠ finRotate (n + 1) 0 →
      ⟪nn, ě j⟫ < ⟪nn, ě 0⟫ := by
    intro j hj0 hj1
    have hj := hluneg j hj0 hj1
    have h0 := hldec 0
    have hjd := hldec j
    rw [hlu0] at h0
    nlinarith [hs0]
  -- ══ 10. il killer: passo = ±2π/q ══
  have horb : ∀ k : ℕ, (⇑(o.rotation θ))^[k] (ě 0)
      = ě ((⇑(finRotate (n + 1)))^[k] 0) := by
    intro k
    induction k with
    | zero => rfl
    | succ m ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
          ← hstepr]
  have hval1 : ((finRotate (n + 1) 0 : Fin (n + 1)) : ℕ) = 1 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [finRotate_apply, zero_add, Fin.val_one]
  have hnn0 : nn ≠ 0 := by
    intro h0
    have hj2ne0 : (finRotate (n + 1)) (finRotate (n + 1) 0) ≠ 0 :=
      finRotate_due_ne hq 0
    have hj2ne1 : (finRotate (n + 1)) (finRotate (n + 1) 0)
        ≠ finRotate (n + 1) 0 := finRotate_ne_self (by omega) _
    have := hklt _ hj2ne0 hj2ne1
    rw [h0] at this
    simp at this
  have hě0u : ‖ě 0‖ = 1 := by
    show ‖e 0‖ = 1
    exact he1 0
  have hkiller := passo_del_fan o θ (n + 1) hq hord nn (ě 0) hnn0 hě0u
    (by
      rw [Function.iterate_one, ← hstepr 0]
      exact hkeq)
    (by
      intro j hj0 hj1
      rw [horb (j : ℕ), finRotate_iterate_zero n (j : ℕ) j.isLt]
      have hjj : (⟨(j : ℕ), j.isLt⟩ : Fin (n + 1)) = j := by
        apply Fin.ext
        rfl
      rw [hjj]
      apply hklt j
      · intro h
        apply hj0
        rw [h]
        rfl
      · intro h
        apply hj1
        rw [h, hval1])
  -- ══ 11. il coseno del passo ══
  have hee' : ⟪e 0, e (finRotate (n + 1) 0)⟫
      = Real.cos (2 * π / ((n + 1 : ℕ) : ℝ)) := by
    have h1 : ⟪ě 0, ě (finRotate (n + 1) 0)⟫
        = Real.cos (2 * π / ((n + 1 : ℕ) : ℝ)) := by
      rw [hstepr 0]
      exact inner_rotation_pm o θ (n + 1) hkiller (ě 0) hě0u
    have h2 : ⟪ě 0, ě (finRotate (n + 1) 0)⟫
        = ⟪e 0, e (finRotate (n + 1) 0)⟫ := rfl
    rw [← h2, h1]
  -- ══ 12. lo spike ══
  have hspike := spike_somma_sotto_due_pi ŵ (e 0) (e (finRotate (n + 1) 0))
    hŵ1 (he1 0) (he1 _) (he2 0) (he2 _) β hβ0 hβπ2 (n + 1) hq
    (by rw [hee'])
  have hu0form : Real.cos β • ŵ + Real.sin β • e 0 = u 0 := by
    rw [hcos, hsin]
    exact (he3 0).symm
  have hu1form : Real.cos β • ŵ + Real.sin β • e (finRotate (n + 1) 0)
      = u (finRotate (n + 1) 0) := by
    rw [hcos, hsin]
    exact (he3 _).symm
  rw [hu0form, hu1form] at hspike
  exact hspike
