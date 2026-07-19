import UnicoProofs.Platonici.DatiDelResiduo
import UnicoProofs.Platonici.Indipendenza
import UnicoProofs.Platonici.Gram
import UnicoProofs.Platonici.Ortogonalita

/-!
FASCICOLO 57 — L'API CANONICA DELLA GRAM.

La scelta del normale e del punto base viene effettuata una volta sola.  I segni
sono poi propagati lungo l'ordine lineare dei ranghi, così che ogni voce
adiacente abbia il segno negativo canonico.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Il normale unitario scelto canonicamente (in senso classico) per il rango
`i`.  Tutti i consumatori vedono la stessa scelta. -/
noncomputable def normale (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) : E n :=
  (simpleReflection_formula P hreg F i).choose

/-- Il punto base scelto insieme a `normale`. -/
noncomputable def puntoBase (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) : E n :=
  (simpleReflection_formula P hreg F i).choose_spec.choose

theorem normale_norm (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) : ‖normale P hreg F i‖ = 1 :=
  (simpleReflection_formula P hreg F i).choose_spec.choose_spec.1

theorem normale_formula (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) :
    ∀ x, simpleReflection P hreg F i x =
      x - (2 * ⟪normale P hreg F i, x - puntoBase P hreg F i⟫ : ℝ) •
        normale P hreg F i :=
  (simpleReflection_formula P hreg F i).choose_spec.choose_spec.2

theorem gram_diag_canonica (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) :
    ⟪normale P hreg F i, normale P hreg F i⟫ = 1 :=
  gram_diagonale (normale_norm P hreg F i)

theorem gram_lontane_canonica (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) {i j : Fin n} (hij : (i : ℕ) + 2 ≤ (j : ℕ)) :
    ⟪normale P hreg F i, normale P hreg F j⟫ = 0 :=
  normali_lontani_ortogonali P hreg F hij
    (normale_norm P hreg F i) (normale_formula P hreg F i)
    (normale_norm P hreg F j) (normale_formula P hreg F j)

theorem gram_adiacente_canonica (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hn : 3 ≤ n) :
    |⟪normale P hreg F i,
        normale P hreg F ⟨(i : ℕ) + 1, hi⟩⟫| =
      Real.cos (Real.pi /
        (coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ : ℝ)) :=
  rotazione_elementare_incondizionata P hreg F i hi hn
    (normale_norm P hreg F i)
    (normale_norm P hreg F ⟨(i : ℕ) + 1, hi⟩)
    (normale_formula P hreg F i)
    (normale_formula P hreg F ⟨(i : ℕ) + 1, hi⟩)

/-- Ricorsione strutturale dei segni lungo la stringa dei ranghi. -/
noncomputable def segnoNat (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) : ∀ k : ℕ, k < n → ℝ
  | 0, _ => 1
  | k + 1, hk =>
      if ⟪segnoNat P hreg F k (Nat.lt_of_succ_lt hk) •
            normale P hreg F ⟨k, Nat.lt_of_succ_lt hk⟩,
          normale P hreg F ⟨k + 1, hk⟩⟫ ≤ 0 then 1 else -1

/-- Il segno del normale di rango `i`; vale sempre `1` oppure `-1`. -/
noncomputable def segno (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) : ℝ :=
  segnoNat P hreg F i i.isLt

noncomputable def normaleOrientato (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n) : E n :=
  segno P hreg F i • normale P hreg F i

theorem segno_eq_one_or_neg_one (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n) :
    segno P hreg F i = 1 ∨ segno P hreg F i = -1 := by
  rcases i with ⟨_ | k, hk⟩
  · exact Or.inl rfl
  · unfold segno
    rw [segnoNat]
    split <;> simp_all

theorem segno_ne_zero (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) : segno P hreg F i ≠ 0 := by
  rcases segno_eq_one_or_neg_one P hreg F i with h | h <;> rw [h] <;>
    norm_num

@[simp] theorem segno_abs (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) : |segno P hreg F i| = 1 := by
  rcases segno_eq_one_or_neg_one P hreg F i with h | h <;> rw [h] <;>
    norm_num

theorem segno_succ (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (k : ℕ) (hk : k + 1 < n) :
    segno P hreg F ⟨k + 1, hk⟩ =
      if ⟪normaleOrientato P hreg F ⟨k, Nat.lt_of_succ_lt hk⟩,
          normale P hreg F ⟨k + 1, hk⟩⟫ ≤ 0 then 1 else -1 := by
  rfl

theorem normaleOrientato_norm (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n) :
    ‖normaleOrientato P hreg F i‖ = 1 := by
  rw [normaleOrientato, norm_smul, normale_norm, mul_one, Real.norm_eq_abs,
    segno_abs]

/-- Cambiare il segno del normale non cambia la formula della riflessione. -/
theorem normaleOrientato_formula (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n) :
    ∀ x, simpleReflection P hreg F i x =
      x - (2 * ⟪normaleOrientato P hreg F i,
        x - puntoBase P hreg F i⟫ : ℝ) • normaleOrientato P hreg F i := by
  intro x
  rcases segno_eq_one_or_neg_one P hreg F i with hs | hs
  · simpa [normaleOrientato, hs] using normale_formula P hreg F i x
  · rw [normale_formula P hreg F i x]
    simp [normaleOrientato, hs, inner_neg_left]

theorem gram_diag_orientata (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) :
    ⟪normaleOrientato P hreg F i, normaleOrientato P hreg F i⟫ = 1 :=
  gram_diagonale (normaleOrientato_norm P hreg F i)

theorem gram_lontane_orientata (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) {i j : Fin n}
    (hij : (i : ℕ) + 2 ≤ (j : ℕ)) :
    ⟪normaleOrientato P hreg F i, normaleOrientato P hreg F j⟫ = 0 := by
  rcases segno_eq_one_or_neg_one P hreg F i with hi | hi <;>
  rcases segno_eq_one_or_neg_one P hreg F j with hj | hj <;>
  simp [normaleOrientato, hi, hj, gram_lontane_canonica P hreg F hij]

theorem gram_adiacente_orientata (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hn : 3 ≤ n) :
    ⟪normaleOrientato P hreg F i,
        normaleOrientato P hreg F ⟨(i : ℕ) + 1, hi⟩⟫ =
      -Real.cos (Real.pi /
        (coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ : ℝ)) := by
  let j : Fin n := ⟨(i : ℕ) + 1, hi⟩
  let a : ℝ := ⟪normaleOrientato P hreg F i, normale P hreg F j⟫
  have habs : |a| = Real.cos (Real.pi /
      (coxeterMatrix P hreg F i j : ℝ)) := by
    rw [show a = segno P hreg F i *
        ⟪normale P hreg F i, normale P hreg F j⟫ by
      simp [a, normaleOrientato, real_inner_smul_left],
      abs_mul, segno_abs, one_mul]
    exact gram_adiacente_canonica P hreg F i hi hn
  have horient :
      ⟪normaleOrientato P hreg F i, normaleOrientato P hreg F j⟫ =
        -|a| := by
    change ⟪normaleOrientato P hreg F i,
      segno P hreg F j • normale P hreg F j⟫ = -|a|
    rw [real_inner_smul_right]
    change segno P hreg F j * a = -|a|
    rw [show segno P hreg F j =
        if a ≤ 0 then 1 else -1 by
      simpa only [j, a] using segno_succ P hreg F (i : ℕ) hi]
    split_ifs with ha
    · simp [abs_of_nonpos ha]
    · have ha' : 0 < a := lt_of_not_ge ha
      simp [abs_of_pos ha']
  rw [horient, habs]

/-- Se un punto è fisso, la sua coordinata normale rispetto al punto base
canonico è nulla. -/
theorem inner_normale_sub_puntoBase_eq_zero_of_fixed
    (P : ConvexPolytope n) (hreg : P.IsRegular) (F : P.Flag)
    (i : Fin n) (x : E n)
    (hx : simpleReflection P hreg F i x = x) :
    ⟪normale P hreg F i, x - puntoBase P hreg F i⟫ = 0 := by
  have hform := normale_formula P hreg F i x
  rw [hx] at hform
  have hsmul :
      (2 * ⟪normale P hreg F i, x - puntoBase P hreg F i⟫ : ℝ) •
        normale P hreg F i = 0 := sub_eq_self.mp hform.symm
  have hnzero : normale P hreg F i ≠ 0 := by
    intro hz
    have hnorm := normale_norm P hreg F i
    rw [hz, norm_zero] at hnorm
    norm_num at hnorm
  have hscalar := (smul_eq_zero.mp hsmul).resolve_right hnzero
  linarith

/-- I normali canonici sono liberi.  La prova usa la base affine comune dei
centroidi della bandiera, non una scelta locale supplementare. -/
theorem normali_canonici_linearIndependent (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (hn : 1 ≤ n) :
    LinearIndependent ℝ (normale P hreg F) := by
  classical
  let q : Fin (n + 1) → E n := centroidiBandieraCorpo P F
  let v : Fin n → E n := fun k => q k.castSucc - q (Fin.last n)
  have hqAI : AffineIndependent ℝ q := by
    simpa only [q] using centroidiBandieraCorpo_affineIndependent P hreg.1 F
  have hvsub : LinearIndependent ℝ
      (fun z : {z : Fin (n + 1) // z ≠ Fin.last n} =>
        q z - q (Fin.last n)) := by
    simpa only [vsub_eq_sub] using
      (affineIndependent_iff_linearIndependent_vsub ℝ q (Fin.last n)).mp hqAI
  let e : Fin n → {z : Fin (n + 1) // z ≠ Fin.last n} :=
    fun k => ⟨k.castSucc, ne_of_lt (Fin.castSucc_lt_last k)⟩
  have he : Function.Injective e := by
    intro a b hab
    exact Fin.castSucc_injective n (congrArg Subtype.val hab)
  have hvLI : LinearIndependent ℝ v := by
    change LinearIndependent ℝ
      ((fun z : {z : Fin (n + 1) // z ≠ Fin.last n} =>
        q z - q (Fin.last n)) ∘ e)
    exact hvsub.comp e he
  have htopfix : ∀ i : Fin n,
      simpleReflection P hreg F i (q (Fin.last n)) = q (Fin.last n) := by
    intro i
    simpa only [q, centroidiBandieraCorpo_last] using
      centroide_di_faccia_fissato P
        (simpleReflection_isSymmetry P hreg F i) (toSet_isFace P)
        (simpleReflection_isSymmetry P hreg F i)
  have hfacefix : ∀ (i k : Fin n), k ≠ i →
      simpleReflection P hreg F i (q k.castSucc) = q k.castSucc := by
    intro i k hki
    simpa only [q, centroidiBandieraCorpo_castSucc] using
      centroide_di_faccia_fissato P
        (simpleReflection_isSymmetry P hreg F i) (F.isFace k)
        (simpleReflection_fissa_facce P hreg F i hki)
  have horth : ∀ (i k : Fin n), k ≠ i →
      ⟪normale P hreg F i, v k⟫ = 0 := by
    intro i k hki
    have hk0 := inner_normale_sub_puntoBase_eq_zero_of_fixed P hreg F i
      (q k.castSucc) (hfacefix i k hki)
    have ht0 := inner_normale_sub_puntoBase_eq_zero_of_fixed P hreg F i
      (q (Fin.last n)) (htopfix i)
    change ⟪normale P hreg F i, q k.castSucc - q (Fin.last n)⟫ = 0
    rw [show q k.castSucc - q (Fin.last n) =
        (q k.castSucc - puntoBase P hreg F i) -
          (q (Fin.last n) - puntoBase P hreg F i) by abel,
      inner_sub_right, hk0, ht0, sub_zero]
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hvspan : Submodule.span ℝ (Set.range v) = ⊤ :=
    hvLI.span_eq_top_of_card_eq_finrank (by simp [E])
  have hdiag : ∀ i : Fin n, ⟪normale P hreg F i, v i⟫ ≠ 0 := by
    intro i hii
    have hall : ∀ k : Fin n, ⟪normale P hreg F i, v k⟫ = 0 := by
      intro k
      by_cases hki : k = i
      · simpa [hki] using hii
      · exact horth i k hki
    have hmem : normale P hreg F i ∈ Submodule.span ℝ (Set.range v) := by
      rw [hvspan]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    have hself :
        ⟪normale P hreg F i, normale P hreg F i⟫ = 0 := by
      calc
        ⟪normale P hreg F i, normale P hreg F i⟫ =
            ⟪normale P hreg F i, ∑ k, c k • v k⟫ := by rw [hc]
        _ = ∑ k, ⟪normale P hreg F i, c k • v k⟫ := by rw [inner_sum]
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro k _
          rw [real_inner_smul_right, hall k, mul_zero]
    have hz : normale P hreg F i = 0 := inner_self_eq_zero.mp hself
    have hnorm := normale_norm P hreg F i
    rw [hz, norm_zero] at hnorm
    norm_num at hnorm
  exact linearIndependent_of_biorthogonal (normale P hreg F) v hdiag horth

theorem normali_orientati_linearIndependent (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (hn : 1 ≤ n) :
    LinearIndependent ℝ (normaleOrientato P hreg F) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hind := Fintype.linearIndependent_iff.mp
    (normali_canonici_linearIndependent P hreg F hn)
  have hsum : ∑ k, (g k * segno P hreg F k) • normale P hreg F k = 0 := by
    simpa only [normaleOrientato, smul_smul] using hg
  have hi := hind (fun k => g k * segno P hreg F k) hsum i
  exact (mul_eq_zero.mp hi).resolve_right (segno_ne_zero P hreg F i)

theorem gram_canonica (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (hn : 3 ≤ n) :
    (∀ i : Fin n,
      ⟪normaleOrientato P hreg F i, normaleOrientato P hreg F i⟫ = 1) ∧
    (∀ i j : Fin n, (i : ℕ) + 2 ≤ (j : ℕ) →
      ⟪normaleOrientato P hreg F i, normaleOrientato P hreg F j⟫ = 0) ∧
    (∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      ⟪normaleOrientato P hreg F i,
        normaleOrientato P hreg F ⟨(i : ℕ) + 1, hi⟩⟫ =
        -Real.cos (Real.pi /
          (coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ : ℝ))) := by
  exact ⟨gram_diag_orientata P hreg F,
    fun _ _ hij => gram_lontane_orientata P hreg F hij,
    fun i hi => gram_adiacente_orientata P hreg F i hi hn⟩

theorem gram_canonica_definita_positiva (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (hn : 3 ≤ n) (g : Fin n → ℝ)
    (hzero : ∀ j, ∑ i, g i *
      ⟪normaleOrientato P hreg F i, normaleOrientato P hreg F j⟫ = 0) :
    ∀ i, g i = 0 :=
  gram_definita_positiva (normaleOrientato P hreg F)
    (normali_orientati_linearIndependent P hreg F (by omega)) g hzero

end LeanEval.Geometry.PlatonicClassification
