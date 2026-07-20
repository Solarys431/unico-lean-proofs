import UnicoProofs.Platonici.Ortoplesse

/-!
Il 24-cell in `E 4`.

I vertici sono le radici del sistema `D₄`: esattamente due coordinate non nulle,
entrambe uguali a `±1`.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

abbrev CoppiaVentiquattro := {p : Fin 4 × Fin 4 // p.1 < p.2}

/-- Codice di un vertice del 24-cell: due coordinate ordinate e due segni. -/
abbrev CodiceVentiquattro := CoppiaVentiquattro × (Bool × Bool)

abbrev indicePrimoVentiquattro (c : CodiceVentiquattro) : Fin 4 := c.1.1.1

abbrev indiceSecondoVentiquattro (c : CodiceVentiquattro) : Fin 4 := c.1.1.2

abbrev segnoPrimoVentiquattro (c : CodiceVentiquattro) : Bool := c.2.1

abbrev segnoSecondoVentiquattro (c : CodiceVentiquattro) : Bool := c.2.2

theorem indicePrimo_lt_indiceSecondo (c : CodiceVentiquattro) :
    indicePrimoVentiquattro c < indiceSecondoVentiquattro c :=
  c.1.2

theorem indicePrimo_ne_indiceSecondo (c : CodiceVentiquattro) :
    indicePrimoVentiquattro c ≠ indiceSecondoVentiquattro c :=
  ne_of_lt (indicePrimo_lt_indiceSecondo c)

def segnoVentiquattro (b : Bool) : ℝ :=
  if b then 1 else -1

@[simp] theorem segnoVentiquattro_ne_zero (b : Bool) :
    segnoVentiquattro b ≠ 0 := by
  cases b <;> norm_num [segnoVentiquattro]

@[simp] theorem norm_segnoVentiquattro (b : Bool) :
    ‖segnoVentiquattro b‖ = 1 := by
  cases b <;> norm_num [segnoVentiquattro]

@[simp] theorem mul_self_segnoVentiquattro (b : Bool) :
    segnoVentiquattro b * segnoVentiquattro b = 1 := by
  cases b <;> norm_num [segnoVentiquattro]

theorem segnoVentiquattro_injective :
    Function.Injective segnoVentiquattro := by
  intro b c h
  cases b <;> cases c
  · rfl
  · norm_num [segnoVentiquattro] at h
  · norm_num [segnoVentiquattro] at h
  · rfl

/-- Costruttore comodo per i codici. -/
def codiceVentiquattro (i j : Fin 4) (hij : i < j)
    (si sj : Bool) : CodiceVentiquattro :=
  (⟨(i, j), hij⟩, (si, sj))

@[simp] theorem indicePrimo_codiceVentiquattro (i j : Fin 4) (hij : i < j)
    (si sj : Bool) :
    indicePrimoVentiquattro (codiceVentiquattro i j hij si sj) = i := rfl

@[simp] theorem indiceSecondo_codiceVentiquattro (i j : Fin 4) (hij : i < j)
    (si sj : Bool) :
    indiceSecondoVentiquattro (codiceVentiquattro i j hij si sj) = j := rfl

@[simp] theorem segnoPrimo_codiceVentiquattro (i j : Fin 4) (hij : i < j)
    (si sj : Bool) :
    segnoPrimoVentiquattro (codiceVentiquattro i j hij si sj) = si := rfl

@[simp] theorem segnoSecondo_codiceVentiquattro (i j : Fin 4) (hij : i < j)
    (si sj : Bool) :
    segnoSecondoVentiquattro (codiceVentiquattro i j hij si sj) = sj := rfl

/-- Un vertice del 24-cell. -/
def vertVentiquattro (c : CodiceVentiquattro) : E 4 :=
  EuclideanSpace.single (indicePrimoVentiquattro c)
      (segnoVentiquattro (segnoPrimoVentiquattro c)) +
    EuclideanSpace.single (indiceSecondoVentiquattro c)
      (segnoVentiquattro (segnoSecondoVentiquattro c))

theorem vertVentiquattro_apply (c : CodiceVentiquattro) (k : Fin 4) :
    vertVentiquattro c k =
      (if k = indicePrimoVentiquattro c then
          segnoVentiquattro (segnoPrimoVentiquattro c) else 0) +
        (if k = indiceSecondoVentiquattro c then
          segnoVentiquattro (segnoSecondoVentiquattro c) else 0) := by
  simp [vertVentiquattro]

@[simp] theorem vertVentiquattro_apply_primo (c : CodiceVentiquattro) :
    vertVentiquattro c (indicePrimoVentiquattro c) =
      segnoVentiquattro (segnoPrimoVentiquattro c) := by
  simp [vertVentiquattro_apply, indicePrimo_ne_indiceSecondo c]

@[simp] theorem vertVentiquattro_apply_secondo (c : CodiceVentiquattro) :
    vertVentiquattro c (indiceSecondoVentiquattro c) =
      segnoVentiquattro (segnoSecondoVentiquattro c) := by
  simp [vertVentiquattro_apply, (indicePrimo_ne_indiceSecondo c).symm]

theorem vertVentiquattro_apply_ne_zero_iff (c : CodiceVentiquattro) (k : Fin 4) :
    vertVentiquattro c k ≠ 0 ↔
      k = indicePrimoVentiquattro c ∨ k = indiceSecondoVentiquattro c := by
  by_cases hk₁ : k = indicePrimoVentiquattro c
  · subst hk₁
    simp [indicePrimo_ne_indiceSecondo c]
  · by_cases hk₂ : k = indiceSecondoVentiquattro c
    · subst hk₂
      simp [hk₁]
    · simp [vertVentiquattro_apply, hk₁, hk₂]

theorem codiceVentiquattro_ext {c d : CodiceVentiquattro}
    (h₁ : indicePrimoVentiquattro c = indicePrimoVentiquattro d)
    (h₂ : indiceSecondoVentiquattro c = indiceSecondoVentiquattro d)
    (hs₁ : segnoPrimoVentiquattro c = segnoPrimoVentiquattro d)
    (hs₂ : segnoSecondoVentiquattro c = segnoSecondoVentiquattro d) :
    c = d := by
  rcases c with ⟨⟨⟨i, j⟩, hij⟩, ⟨si, sj⟩⟩
  rcases d with ⟨⟨⟨i', j'⟩, hij'⟩, ⟨si', sj'⟩⟩
  simp [indicePrimoVentiquattro, indiceSecondoVentiquattro,
    segnoPrimoVentiquattro, segnoSecondoVentiquattro] at h₁ h₂ hs₁ hs₂
  subst i'
  subst j'
  subst si'
  subst sj'
  rfl

theorem vertVentiquattro_pair_eq_of_eq {c d : CodiceVentiquattro}
    (h : vertVentiquattro c = vertVentiquattro d) :
    indicePrimoVentiquattro c = indicePrimoVentiquattro d ∧
      indiceSecondoVentiquattro c = indiceSecondoVentiquattro d := by
  have hci : vertVentiquattro c (indicePrimoVentiquattro c) ≠ 0 := by
    simp
  have hcj : vertVentiquattro c (indiceSecondoVentiquattro c) ≠ 0 := by
    simp
  have hiMem :
      indicePrimoVentiquattro c = indicePrimoVentiquattro d ∨
        indicePrimoVentiquattro c = indiceSecondoVentiquattro d := by
    exact (vertVentiquattro_apply_ne_zero_iff d
      (indicePrimoVentiquattro c)).mp (by simpa [h] using hci)
  have hjMem :
      indiceSecondoVentiquattro c = indicePrimoVentiquattro d ∨
        indiceSecondoVentiquattro c = indiceSecondoVentiquattro d := by
    exact (vertVentiquattro_apply_ne_zero_iff d
      (indiceSecondoVentiquattro c)).mp (by simpa [h] using hcj)
  rcases hiMem with hi | hi
  · rcases hjMem with hj | hj
    · exfalso
      exact indicePrimo_ne_indiceSecondo c (hi.trans hj.symm)
    · exact ⟨hi, hj⟩
  · rcases hjMem with hj | hj
    · exfalso
      have hlt : indiceSecondoVentiquattro c < indicePrimoVentiquattro c := by
        calc
          indiceSecondoVentiquattro c = indicePrimoVentiquattro d := hj
          _ < indiceSecondoVentiquattro d := indicePrimo_lt_indiceSecondo d
          _ = indicePrimoVentiquattro c := hi.symm
      exact (not_lt_of_ge (indicePrimo_lt_indiceSecondo c).le) hlt
    · exfalso
      exact indicePrimo_ne_indiceSecondo c (hi.trans hj.symm)

theorem vertVentiquattro_injective :
    Function.Injective vertVentiquattro := by
  intro c d h
  obtain ⟨h₁, h₂⟩ := vertVentiquattro_pair_eq_of_eq h
  have hs₁ :
      segnoPrimoVentiquattro c = segnoPrimoVentiquattro d := by
    apply segnoVentiquattro_injective
    have hc := congrArg (fun x : E 4 => x (indicePrimoVentiquattro c)) h
    simpa [h₁] using hc
  have hs₂ :
      segnoSecondoVentiquattro c = segnoSecondoVentiquattro d := by
    apply segnoVentiquattro_injective
    have hc := congrArg (fun x : E 4 => x (indiceSecondoVentiquattro c)) h
    simpa [h₂] using hc
  exact codiceVentiquattro_ext h₁ h₂ hs₁ hs₂

/-- I 24 vertici del 24-cell. -/
def verticiVentiquattro : Finset (E 4) :=
  (Finset.univ : Finset CodiceVentiquattro).image vertVentiquattro

theorem mem_verticiVentiquattro {x : E 4} :
    x ∈ verticiVentiquattro ↔ ∃ c : CodiceVentiquattro, vertVentiquattro c = x := by
  simp [verticiVentiquattro]

theorem card_coppiaVentiquattro : Fintype.card CoppiaVentiquattro = 6 := by
  rw [Fintype.card_subtype]
  have h :
      (Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2)) =
        {((0 : Fin 4), (1 : Fin 4)), ((0 : Fin 4), (2 : Fin 4)),
          ((0 : Fin 4), (3 : Fin 4)), ((1 : Fin 4), (2 : Fin 4)),
          ((1 : Fin 4), (3 : Fin 4)), ((2 : Fin 4), (3 : Fin 4))} := by
    ext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp
  rw [h]
  simp

theorem card_codiceVentiquattro : Fintype.card CodiceVentiquattro = 24 := by
  rw [Fintype.card_prod, Fintype.card_prod, card_coppiaVentiquattro]
  norm_num

theorem card_ventiquattro : verticiVentiquattro.card = 24 := by
  rw [verticiVentiquattro,
    Finset.card_image_of_injective _ vertVentiquattro_injective]
  exact card_codiceVentiquattro

theorem verticiVentiquattro_nonempty : verticiVentiquattro.Nonempty := by
  refine ⟨vertVentiquattro
    (codiceVentiquattro (0 : Fin 4) (1 : Fin 4) (by norm_num) true true), ?_⟩
  exact mem_verticiVentiquattro.mpr
    ⟨codiceVentiquattro (0 : Fin 4) (1 : Fin 4) (by norm_num) true true, rfl⟩

theorem norm_sq_vertVentiquattro (c : CodiceVentiquattro) :
    ‖vertVentiquattro c‖ ^ 2 = 2 := by
  let i := indicePrimoVentiquattro c
  let j := indiceSecondoVentiquattro c
  let si := segnoVentiquattro (segnoPrimoVentiquattro c)
  let sj := segnoVentiquattro (segnoSecondoVentiquattro c)
  have horth : inner ℝ (EuclideanSpace.single i si)
      (EuclideanSpace.single j sj) = 0 := by
    rw [EuclideanSpace.inner_single_left]
    simp [i, j, indicePrimo_ne_indiceSecondo c]
  change ‖EuclideanSpace.single i si + EuclideanSpace.single j sj‖ ^ 2 = 2
  rw [pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_real horth]
  simp [si, sj, PiLp.norm_single]
  norm_num

theorem vertVentiquattro_sub_flip_primo (i j : Fin 4) (hij : i < j)
    (sj : Bool) :
    vertVentiquattro (codiceVentiquattro i j hij true sj) -
        vertVentiquattro (codiceVentiquattro i j hij false sj) =
      (2 : ℝ) • EuclideanSpace.single i 1 := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [vertVentiquattro, hij.ne,
      segnoVentiquattro]
    ring_nf
  · simp [vertVentiquattro, hki,
      segnoVentiquattro]
    ring_nf

theorem vertVentiquattro_sub_flip_secondo (i j : Fin 4) (hij : i < j)
    (si : Bool) :
    vertVentiquattro (codiceVentiquattro i j hij si true) -
        vertVentiquattro (codiceVentiquattro i j hij si false) =
      (2 : ℝ) • EuclideanSpace.single j 1 := by
  ext k
  by_cases hkj : k = j
  · subst k
    simp [vertVentiquattro, (ne_of_lt hij).symm,
      segnoVentiquattro]
    ring_nf
  · simp [vertVentiquattro, hkj,
      segnoVentiquattro]
    ring_nf

theorem norm_vertVentiquattro (c : CodiceVentiquattro) :
    ‖vertVentiquattro c‖ = Real.sqrt 2 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),
    norm_sq_vertVentiquattro c, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem verticiVentiquattro_eq_extremePoints :
    ((verticiVentiquattro : Finset (E 4)) : Set (E 4)) =
      Set.extremePoints ℝ
        (convexHull ℝ ((verticiVentiquattro : Finset (E 4)) : Set (E 4))) := by
  let c₀ : CodiceVentiquattro :=
    codiceVentiquattro (0 : Fin 4) (1 : Fin 4) (by norm_num) true true
  have hne : (0 : E 4) ≠ vertVentiquattro c₀ := by
    intro h
    have h0 := congrArg (fun x : E 4 => x (0 : Fin 4)) h
    norm_num [c₀, codiceVentiquattro, vertVentiquattro,
      indicePrimoVentiquattro, indiceSecondoVentiquattro,
      segnoPrimoVentiquattro, segnoSecondoVentiquattro,
      segnoVentiquattro, PiLp.single_apply] at h0
  haveI : Nontrivial (E 4) := ⟨⟨0, vertVentiquattro c₀, hne⟩⟩
  symm
  apply cosferico_extremePoints 0 (Real.sqrt 2)
  intro v hv
  rw [mem_sphere_zero_iff_norm]
  have hv' : v ∈ verticiVentiquattro := by exact_mod_cast hv
  rw [mem_verticiVentiquattro] at hv'
  obtain ⟨c, rfl⟩ := hv'
  exact norm_vertVentiquattro c

/-- Il 24-cell `{3,4,3}` come politopo convesso in `E 4`. -/
def ventiquattro : ConvexPolytope 4 :=
  ⟨verticiVentiquattro, verticiVentiquattro_nonempty,
    verticiVentiquattro_eq_extremePoints⟩

theorem card_politope_ventiquattro :
    ventiquattro.vertices.card = 24 :=
  card_ventiquattro

/-- Il 24-cell genera affineamente tutto `E 4`. -/
theorem ventiquattro_isFullDim : ventiquattro.IsFullDim := by
  let W : Submodule ℝ (E 4) := vectorSpan ℝ ventiquattro.toSet
  have mem_toSet (c : CodiceVentiquattro) :
      vertVentiquattro c ∈ ventiquattro.toSet := by
    exact subset_convexHull ℝ _
      (by exact_mod_cast (mem_verticiVentiquattro.mpr ⟨c, rfl⟩))
  have basis0 : (EuclideanSpace.basisFun (Fin 4) ℝ) (0 : Fin 4) ∈ W := by
    let cp := codiceVentiquattro (0 : Fin 4) (1 : Fin 4) (by norm_num) true true
    let cm := codiceVentiquattro (0 : Fin 4) (1 : Fin 4) (by norm_num) false true
    have hdiff : vertVentiquattro cp - vertVentiquattro cm ∈ W :=
      vsub_mem_vectorSpan ℝ (mem_toSet cp) (mem_toSet cm)
    have hcalc :
        vertVentiquattro cp - vertVentiquattro cm =
          (2 : ℝ) • EuclideanSpace.single (0 : Fin 4) 1 := by
      exact vertVentiquattro_sub_flip_primo _ _ _ true
    rw [EuclideanSpace.basisFun_apply]
    exact (W.smul_mem_iff (by norm_num : (2 : ℝ) ≠ 0)).mp (hcalc ▸ hdiff)
  have basis1 : (EuclideanSpace.basisFun (Fin 4) ℝ) (1 : Fin 4) ∈ W := by
    let cp := codiceVentiquattro (0 : Fin 4) (1 : Fin 4) (by norm_num) true true
    let cm := codiceVentiquattro (0 : Fin 4) (1 : Fin 4) (by norm_num) true false
    have hdiff : vertVentiquattro cp - vertVentiquattro cm ∈ W :=
      vsub_mem_vectorSpan ℝ (mem_toSet cp) (mem_toSet cm)
    have hcalc :
        vertVentiquattro cp - vertVentiquattro cm =
          (2 : ℝ) • EuclideanSpace.single (1 : Fin 4) 1 := by
      exact vertVentiquattro_sub_flip_secondo _ _ _ true
    rw [EuclideanSpace.basisFun_apply]
    exact (W.smul_mem_iff (by norm_num : (2 : ℝ) ≠ 0)).mp (hcalc ▸ hdiff)
  have basis2 : (EuclideanSpace.basisFun (Fin 4) ℝ) (2 : Fin 4) ∈ W := by
    let cp := codiceVentiquattro (2 : Fin 4) (3 : Fin 4) (by omega) true true
    let cm := codiceVentiquattro (2 : Fin 4) (3 : Fin 4) (by omega) false true
    have hdiff : vertVentiquattro cp - vertVentiquattro cm ∈ W :=
      vsub_mem_vectorSpan ℝ (mem_toSet cp) (mem_toSet cm)
    have hcalc :
        vertVentiquattro cp - vertVentiquattro cm =
          (2 : ℝ) • EuclideanSpace.single (2 : Fin 4) 1 := by
      exact vertVentiquattro_sub_flip_primo _ _ _ true
    rw [EuclideanSpace.basisFun_apply]
    exact (W.smul_mem_iff (by norm_num : (2 : ℝ) ≠ 0)).mp (hcalc ▸ hdiff)
  have basis3 : (EuclideanSpace.basisFun (Fin 4) ℝ) (3 : Fin 4) ∈ W := by
    let cp := codiceVentiquattro (2 : Fin 4) (3 : Fin 4) (by omega) true true
    let cm := codiceVentiquattro (2 : Fin 4) (3 : Fin 4) (by omega) true false
    have hdiff : vertVentiquattro cp - vertVentiquattro cm ∈ W :=
      vsub_mem_vectorSpan ℝ (mem_toSet cp) (mem_toSet cm)
    have hcalc :
        vertVentiquattro cp - vertVentiquattro cm =
          (2 : ℝ) • EuclideanSpace.single (3 : Fin 4) 1 := by
      exact vertVentiquattro_sub_flip_secondo _ _ _ true
    rw [EuclideanSpace.basisFun_apply]
    exact (W.smul_mem_iff (by norm_num : (2 : ℝ) ≠ 0)).mp (hcalc ▸ hdiff)
  have hbasis : ∀ i : Fin 4,
      (EuclideanSpace.basisFun (Fin 4) ℝ) i ∈ W := by
    intro i
    fin_cases i
    · exact basis0
    · exact basis1
    · exact basis2
    · exact basis3
  have hW : W = ⊤ := by
    apply (Submodule.eq_top_iff').2
    intro x
    rw [← (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr x]
    exact Submodule.sum_mem W fun i _ => W.smul_mem _ (hbasis i)
  rw [ConvexPolytope.IsFullDim, ConvexPolytope.dim]
  change Module.finrank ℝ W = 4
  rw [hW, finrank_top, finrank_euclideanSpace]
  simp

def segnoBoolDaReale (s : ({-1, 1} : Set ℝ)) (b : Bool) : Bool :=
  if (s : ℝ) = 1 then b else !b

theorem segnoBoolDaReale_spec (s : ({-1, 1} : Set ℝ)) (b : Bool) :
    segnoVentiquattro (segnoBoolDaReale s b) =
      (s : ℝ) * segnoVentiquattro b := by
  unfold segnoBoolDaReale
  split_ifs with h
  · rw [h]
    simp
  · have hs : (s : ℝ) = -1 := by
      have hm := s.property
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with hm | hm
      · exact hm
      · exact (h hm).elim
    rw [hs]
    cases b <;> norm_num [segnoVentiquattro]

theorem segnoPerm_refl_vertVentiquattro
    (ε : Fin 4 → ({-1, 1} : Set ℝ)) (c : CodiceVentiquattro) :
    segnoPerm 4 (Equiv.refl (Fin 4)) ε (vertVentiquattro c) =
      vertVentiquattro
        (codiceVentiquattro (indicePrimoVentiquattro c)
          (indiceSecondoVentiquattro c) (indicePrimo_lt_indiceSecondo c)
          (segnoBoolDaReale (ε (indicePrimoVentiquattro c))
            (segnoPrimoVentiquattro c))
          (segnoBoolDaReale (ε (indiceSecondoVentiquattro c))
            (segnoSecondoVentiquattro c))) := by
  rw [segnoPerm_apply]
  simp only [vertVentiquattro, map_add, segnoLinear_single,
    Equiv.refl_apply, indicePrimo_codiceVentiquattro,
    indiceSecondo_codiceVentiquattro, segnoPrimo_codiceVentiquattro,
    segnoSecondo_codiceVentiquattro, segnoBoolDaReale_spec]

theorem segnoPerm_refl_mem_verticiVentiquattro
    (ε : Fin 4 → ({-1, 1} : Set ℝ)) {v : E 4}
    (hv : v ∈ verticiVentiquattro) :
    segnoPerm 4 (Equiv.refl (Fin 4)) ε v ∈ verticiVentiquattro := by
  rw [mem_verticiVentiquattro] at hv
  obtain ⟨c, rfl⟩ := hv
  refine mem_verticiVentiquattro.mpr ?_
  refine ⟨codiceVentiquattro (indicePrimoVentiquattro c)
      (indiceSecondoVentiquattro c) (indicePrimo_lt_indiceSecondo c)
      (segnoBoolDaReale (ε (indicePrimoVentiquattro c))
        (segnoPrimoVentiquattro c))
      (segnoBoolDaReale (ε (indiceSecondoVentiquattro c))
        (segnoSecondoVentiquattro c)), ?_⟩
  exact (segnoPerm_refl_vertVentiquattro ε c).symm

theorem segnoPerm_refl_image_verticiVentiquattro
    (ε : Fin 4 → ({-1, 1} : Set ℝ)) :
    (segnoPerm 4 (Equiv.refl (Fin 4)) ε : E 4 → E 4) ''
        (verticiVentiquattro : Set (E 4)) =
      (verticiVentiquattro : Set (E 4)) := by
  have hfin :
      Finset.image (segnoPerm 4 (Equiv.refl (Fin 4)) ε : E 4 → E 4)
          verticiVentiquattro =
        verticiVentiquattro := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact segnoPerm_refl_mem_verticiVentiquattro ε hu
    · rw [Finset.card_image_of_injective _
        (segnoPerm 4 (Equiv.refl (Fin 4)) ε).injective]
  rw [← Finset.coe_image, hfin]

/-- Simmetrie parziali: cambi indipendenti di segno delle coordinate. -/
theorem segnoPerm_refl_isSymmetry
    (ε : Fin 4 → ({-1, 1} : Set ℝ)) :
    ventiquattro.isSymmetry (segnoPerm 4 (Equiv.refl (Fin 4)) ε) := by
  rw [ConvexPolytope.isSymmetry, ConvexPolytope.toSet]
  calc
    (segnoPerm 4 (Equiv.refl (Fin 4)) ε : E 4 → E 4) ''
        convexHull ℝ ((ventiquattro.vertices : Finset (E 4)) : Set (E 4)) =
      convexHull ℝ ((segnoPerm 4 (Equiv.refl (Fin 4)) ε : E 4 → E 4) ''
        ((ventiquattro.vertices : Finset (E 4)) : Set (E 4))) := by
          exact (segnoPerm 4 (Equiv.refl (Fin 4)) ε).toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ ((ventiquattro.vertices : Finset (E 4)) : Set (E 4)) := by
      rw [show ((ventiquattro.vertices : Finset (E 4)) : Set (E 4)) =
          (verticiVentiquattro : Set (E 4)) by rfl,
        segnoPerm_refl_image_verticiVentiquattro]

/-!
Resta aperta la dimostrazione completa di `ventiquattro.IsRegular`: qui sono
costruiti il politopo, la cardinalità, la piena dimensionalità e un sottogruppo
esplicito di simmetrie. La transitività su tutte le bandiere richiede una
descrizione kernel-pura della struttura facciale del 24-cell.
-/

end LeanEval.Geometry.PlatonicClassification
