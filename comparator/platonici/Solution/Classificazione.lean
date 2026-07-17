import Mathlib
import Solution.Fondamenta
import Solution.TeoremaVertice
import Solution.PonteEsposizione
import Solution.AngoloFaccetta
import Solution.Aritmetica

/-!
LA CLASSIFICAZIONE LOCALE DEI TIPI DI SCHLÄFLI (campagna #50 — il teorema).

Un politopo convesso 3-dimensionale con faccette p-gonali regolari (per
orbita) e ogni vertice q-ciclico soddisfa q(p−2) < 2p, dunque (p,q) è uno
dei cinque tipi platonici: (3,3), (4,3), (3,4), (5,3), (3,5).

Le due metà: il TEOREMA DEL VERTICE (q·α < 2π, dove α è l'angolo tra i due
spigoli consecutivi del fan) e l'ANGOLO DELLA FACCETTA (α = (p−2)π/p),
saldate dall'aritmetica delle cinque coppie. Il teorema che chiude gli
Elementi di Euclide, su spazio astratto, kernel-puro.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace
open FiniteConvexPolytope PlatoniciA13

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

namespace PlatoniciMain

/-- LA CLASSIFICAZIONE LOCALE DEI TIPI DI SCHLÄFLI. -/
theorem cyclicallyRegular_schlafli (P : FiniteConvexPolytope A) {p q : ℕ}
    (h : P.IsCyclicallyRegularOfType p q) :
    q * (p - 2) < 2 * p ∧
    ((p = 3 ∧ q = 3) ∨ (p = 4 ∧ q = 3) ∨ (p = 3 ∧ q = 4) ∨
     (p = 5 ∧ q = 3) ∨ (p = 3 ∧ q = 5)) := by
  classical
  obtain ⟨h3, hp3, hq3, ℓ, hℓ0, hreg, hcyc⟩ := h
  suffices hineq : q * (p - 2) < 2 * p by
    exact ⟨hineq, nat_pairs_of_schlafli p q hp3 hq3 hineq⟩
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hp0R : (0 : ℝ) < p := by positivity
  -- ══ il vertice e il suo fan ══
  obtain ⟨v, hv⟩ := P.nonempty
  obtain ⟨D⟩ := hcyc v hv
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  have hvex : v ∈ P.toSet.extremePoints ℝ := by
    rw [FiniteConvexPolytope.toSet, ← P.vertices_eq_extremePoints]
    exact hv
  have h3' : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := by
    have hbridge : vectorSpan ℝ P.toSet
        = vectorSpan ℝ (P.vertices : Set A) := by
      rw [FiniteConvexPolytope.toSet, ← direction_affineSpan,
        affineSpan_convexHull, direction_affineSpan]
    rw [hbridge]
    exact h3
  -- ══ LA METÀ DEL VERTICE: q · α < 2π ══
  have hV := vertice_q_angolo P hv hq3 D h3'
  -- ══ gli indici del fan ══
  set i₀ : Fin (n + 1) := finRotate (n + 1) 0 with hi₀
  have hi₀0 : i₀ ≠ 0 := by
    rw [hi₀]
    exact finRotate_ne_self (by omega) 0
  have hii : finRotate (n + 1) i₀ ≠ 0 := by
    rw [hi₀]
    exact finRotate_due_ne hq3 0
  have hii₀ : finRotate (n + 1) i₀ ≠ i₀ := finRotate_ne_self (by omega) i₀
  -- ══ la faccetta base e i suoi due spigoli ══
  have hFreg := hreg (D.faccetta i₀) (D.isFacet i₀)
  set x₁ : A := punto P v D 0 with hx₁def
  set x₂ : A := punto P v D i₀ with hx₂def
  have hs₁ := punto_spec P v D 0
  have hs₂ := punto_spec P v D i₀
  rw [← hi₀] at hs₁
  have hn₁ : (0 : ℝ) < ‖x₁ - v‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hs₁.1)
  have hn₂ : (0 : ℝ) < ‖x₂ - v‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hs₂.1)
  -- gli spigoli come esposti nella faccetta (A13)
  have hB₁exp : IsExposed ℝ (D.faccetta i₀)
      (D.faccetta i₀ ∩ D.faccetta 0) :=
    spigolo_esposto_nella_faccetta (D.isFacet i₀).1.1 (D.isFacet 0).1.1
  have hB₂exp : IsExposed ℝ (D.faccetta i₀)
      (D.faccetta i₀ ∩ D.faccetta (finRotate (n + 1) i₀)) :=
    spigolo_esposto_nella_faccetta (D.isFacet i₀).1.1 (D.isFacet _).1.1
  have hvB₁ : v ∈ D.faccetta i₀ ∩ D.faccetta 0 := ⟨D.mem_v i₀, D.mem_v 0⟩
  have hvB₂ : v ∈ D.faccetta i₀ ∩ D.faccetta (finRotate (n + 1) i₀) :=
    ⟨D.mem_v i₀, D.mem_v _⟩
  have hx₁B : x₁ ∈ D.faccetta i₀ ∩ D.faccetta 0 := ⟨hs₁.2.2, hs₁.2.1⟩
  have hx₂B : x₂ ∈ D.faccetta i₀ ∩ D.faccetta (finRotate (n + 1) i₀) :=
    ⟨hs₂.2.1, hs₂.2.2⟩
  -- ══ le esclusioni via spigolo_due ══
  have hx₂B₁ : x₂ ∉ D.faccetta i₀ ∩ D.faccetta 0 := by
    rintro ⟨-, hx₂f0⟩
    rcases D.spigolo_due i₀ 0 x₂ hs₂.2 hs₂.1 hx₂f0 with hcon | hcon
    · exact hi₀0 hcon.symm
    · exact hii hcon.symm
  have hx₁B₂ : x₁ ∉ D.faccetta i₀
      ∩ D.faccetta (finRotate (n + 1) i₀) := by
    rintro ⟨-, hx₁f⟩
    have hs₁' : x₁ ∈ D.faccetta 0 ∩ D.faccetta (finRotate (n + 1) 0) := by
      rw [← hi₀]
      exact ⟨hs₁.2.1, hs₁.2.2⟩
    rcases D.spigolo_due 0 (finRotate (n + 1) i₀) x₁ hs₁' hs₁.1 hx₁f
      with hcon | hcon
    · exact hii hcon
    · rw [← hi₀] at hcon
      exact hii₀ hcon
  -- ══ le direzioni non sono positivamente parallele ══
  have hdir : ∀ c : ℝ, 0 < c → x₂ - v ≠ c • (x₁ - v) := by
    intro c hc heq
    have hd : dir P v D i₀ = dir P v D 0 := by
      show ‖punto P v D i₀ - v‖⁻¹ • (punto P v D i₀ - v)
        = ‖punto P v D 0 - v‖⁻¹ • (punto P v D 0 - v)
      rw [← hx₂def, ← hx₁def, heq, norm_smul, Real.norm_eq_abs,
        abs_of_pos hc, smul_smul, mul_inv]
      congr 1
      field_simp
    exact hi₀0 (dir_iniettiva P v hq3 D hd)
  -- ══ LA METÀ DELLA FACCETTA: α = (p−2)π/p ══
  have hA := angolo_della_faccetta P hFreg (D.mem_v i₀) hvex hB₁exp hB₂exp
    hvB₁ hvB₂ hx₁B hx₂B hs₁.1 hs₂.1 hx₂B₁ hx₁B₂ hdir
  -- ══ il collegamento: l'angolo del fan È l'angolo della faccetta ══
  have hlink : angle (dir P v D 0) (dir P v D i₀)
      = EuclideanGeometry.angle x₁ v x₂ := by
    show angle (‖punto P v D 0 - v‖⁻¹ • (punto P v D 0 - v))
        (‖punto P v D i₀ - v‖⁻¹ • (punto P v D i₀ - v))
      = angle (x₁ - v) (x₂ - v)
    rw [← hx₁def, ← hx₂def,
      angle_smul_left_of_pos _ _ (inv_pos.mpr hn₁),
      angle_smul_right_of_pos _ _ (inv_pos.mpr hn₂)]
  -- ══ la saldatura ══
  rw [hlink, hA] at hV
  -- hV : (n+1) * ((p−2)π/p) < 2π
  have hreal : ((n + 1 : ℕ) : ℝ) * ((p : ℝ) - 2) < 2 * p := by
    have h2 : ((n + 1 : ℕ) : ℝ) * ((p : ℝ) - 2) * π < 2 * π * p := by
      calc ((n + 1 : ℕ) : ℝ) * ((p : ℝ) - 2) * π
          = (((n + 1 : ℕ) : ℝ) * (((p : ℝ) - 2) * π / p)) * p := by
            field_simp
        _ < (2 * π) * p := by
            exact mul_lt_mul_of_pos_right hV hp0R
        _ = 2 * π * p := rfl
    have h3'' : ((n + 1 : ℕ) : ℝ) * ((p : ℝ) - 2) * π < 2 * p * π := by
      linarith [h2]
    exact lt_of_mul_lt_mul_right h3'' hπ.le
  have hcast : (((n + 1) * (p - 2) : ℕ) : ℝ) < ((2 * p : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub (by omega : 2 ≤ p)]
    push_cast at hreal
    linarith [hreal]
  exact_mod_cast hcast

end PlatoniciMain
