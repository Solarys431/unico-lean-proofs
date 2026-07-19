import Mathlib
import UnicoProofs.Platonici.MassimoConsecutivo
import UnicoProofs.Platonici.ResiduoGeometrico
import UnicoProofs.Platonici.RotazioneElementareDue
import UnicoProofs.Platonici.OrdineTreBordi
import UnicoProofs.Platonici.FormulaRiflessione
import UnicoProofs.Platonici.Iperpiano

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-! ## Centroidi e passo combinatorio -/

/-- Centroide dei vertici del politopo appartenenti a una faccia. -/
noncomputable def centroideFaccia (P : ConvexPolytope n) (f : Set (E n)) : E n := by
  classical
  exact Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ f)) id

/-- Una simmetria manda il centroide di una faccia nel centroide della
faccia immagine.  È la versione non stazionaria di
`centroide_di_faccia_fissato`. -/
theorem centroide_di_faccia_mandato (P : ConvexPolytope n)
    {φ : Isom n} (hφ : P.isSymmetry φ) {f g : Set (E n)}
    (hf : P.IsFace f) (hg : P.IsFace g) (hfg : (⇑φ) '' f = g) :
    φ (centroideFaccia P f) = centroideFaccia P g := by
  classical
  let s : Finset (E n) := P.vertices.filter (fun x => x ∈ f)
  let t : Finset (E n) := P.vertices.filter (fun x => x ∈ g)
  have hs : s.Nonempty := (facePolytope P hf).vertices_nonempty
  have hw : ∑ x ∈ s, s.centroidWeights ℝ x = 1 :=
    s.sum_centroidWeights_eq_one_of_nonempty ℝ hs
  have hmap : φ (s.centroid ℝ id) = s.centroid ℝ (fun x => φ x) := by
    rw [Finset.centroid_def, Finset.centroid_def]
    exact s.map_affineCombination id (s.centroidWeights ℝ) hw
      φ.toAffineEquiv.toAffineMap
  have himage : (⇑φ) '' (s : Set (E n)) = (t : Set (E n)) := by
    have hvertices := simmetria_permuta_vertici P hφ
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [s, t, Finset.coe_filter, Set.mem_setOf_eq] at hx ⊢
      constructor
      · have : φ x ∈ (P.vertices : Set (E n)) := by
          rw [← hvertices]
          exact ⟨x, by exact_mod_cast hx.1, rfl⟩
        exact_mod_cast this
      · rw [← hfg]
        exact ⟨x, hx.2, rfl⟩
    · intro hy
      simp only [s, t, Finset.coe_filter, Set.mem_setOf_eq] at hy
      have hyv : y ∈ (⇑φ) '' (P.vertices : Set (E n)) := by
        rw [hvertices]
        exact_mod_cast hy.1
      obtain ⟨x, hxv, hxy⟩ := hyv
      have hyf : y ∈ (⇑φ) '' f := by
        rw [hfg]
        exact hy.2
      obtain ⟨x', hx'f, hx'y⟩ := hyf
      have hxx' : x = x' := φ.injective (hxy.trans hx'y.symm)
      subst x'
      refine ⟨x, ?_, hxy⟩
      simp only [s, Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨hxv, hx'f⟩
  have hcentroid : s.centroid ℝ (fun x => φ x) = t.centroid ℝ id := by
    apply Finset.centroid_eq_of_inj_on_of_image_eq ℝ s t
    · intro x _ y _ hxy
      exact φ.injective hxy
    · intro x _ y _ hxy
      exact hxy
    · simpa using himage
  simpa only [centroideFaccia, s, t] using hmap.trans hcentroid

/-- Il prodotto `rᵢ rᵢ₊₁` manda il centroide della faccia di rango `i`
nel centroide dell'altra faccia di rango `i` della bandiera adiacente. -/
theorem orbita_passo_combinatorio (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    simpleReflection P hreg F i
        (simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩
          (centroideFaccia P (F.face i))) =
      centroideFaccia P ((adjacentFlag P hreg.1 F i).face i) := by
  let j : Fin n := ⟨(i : ℕ) + 1, hi⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    dsimp only [j] at this
    omega
  have hjfix : (⇑(simpleReflection P hreg F j)) '' F.face i = F.face i :=
    simpleReflection_fissa_facce P hreg F j hij
  have hcfix : simpleReflection P hreg F j (centroideFaccia P (F.face i)) =
      centroideFaccia P (F.face i) := by
    exact centroide_di_faccia_fissato P
      (simpleReflection_isSymmetry P hreg F j) (F.isFace i) hjfix
  have himage : (⇑(simpleReflection P hreg F i)) '' F.face i =
      (adjacentFlag P hreg.1 F i).face i := by
    have h := congrArg (fun G : P.Flag => G.face i)
      (simpleReflection_mapFlag P hreg F i)
    simpa only [mapFlag_face] using h
  rw [show (⟨(i : ℕ) + 1, hi⟩ : Fin n) = j from rfl, hcfix]
  exact centroide_di_faccia_mandato P
    (simpleReflection_isSymmetry P hreg F i) (F.isFace i)
    ((adjacentFlag P hreg.1 F i).isFace i) himage

/-- Il prodotto delle due riflessioni adiacenti, come elemento del gruppo. -/
noncomputable def rhoSimple (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n) : symGroup P :=
  simpleGen P hreg F i * simpleGen P hreg F ⟨(i : ℕ) + 1, hi⟩

/-- Firma effettiva del Bersaglio 1.

Il passo combinatorio è dimostrato; `hmax` e `hstrict` isolano esattamente
la parte ancora mancante del diamante/separazione. -/
theorem orbita_separata (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n) (hn : 3 ≤ n)
    (l : E n →L[ℝ] ℝ)
    (hmax : l (centroideFaccia P (F.face i)) =
      l (centroideFaccia P ((adjacentFlag P hreg.1 F i).face i)))
    (hstrict : ∀ t : ℕ, 2 ≤ t →
      t ≤ coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ - 1 →
      l (((((rhoSimple P hreg F i hi) ^ t : symGroup P) : Isom n)
          (centroideFaccia P (F.face i)))) <
        l (centroideFaccia P (F.face i))) :
    (((rhoSimple P hreg F i hi : symGroup P) : Isom n)
        (centroideFaccia P (F.face i)) =
      centroideFaccia P ((adjacentFlag P hreg.1 F i).face i)) ∧
      l (centroideFaccia P (F.face i)) =
        l (centroideFaccia P ((adjacentFlag P hreg.1 F i).face i)) ∧
      ∀ t : ℕ, 2 ≤ t →
        t ≤ coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ - 1 →
        l (((((rhoSimple P hreg F i hi) ^ t : symGroup P) : Isom n)
            (centroideFaccia P (F.face i)))) <
          l (centroideFaccia P (F.face i)) := by
  have _hm := coxeterMatrix_adiacente_ge_tre_ovunque P hreg F i hi hn
  refine ⟨?_, hmax, hstrict⟩
  dsimp only [rhoSimple, simpleGen]
  change simpleReflection P hreg F i
      (simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩
        (centroideFaccia P (F.face i))) = _
  exact orbita_passo_combinatorio P hreg F i hi

/-! ## Il mezzo passo astratto sul piano del residuo -/

/-- Il centro globale usato come origine affine del residuo. -/
noncomputable def centroGlobale (P : ConvexPolytope n) : E n :=
  Finset.centroid ℝ P.vertices id

/-- Vettore ottenuto proiettando sul piano del residuo. -/
noncomputable def vettoreProiettato (V : Submodule ℝ (E n)) (O c : E n) : V :=
  V.orthogonalProjection (c - O)

/-- Punto affine corrispondente al vettore proiettato. -/
noncomputable def puntoProiettato (V : Submodule ℝ (E n)) (O c : E n) : E n :=
  O + (vettoreProiettato V O c : E n)

/-- Forma direttamente applicabile di `massimo_consecutivo` seguita da
`bisezione_ortogonale`. -/
theorem mezzo_passo (P : ConvexPolytope n) (hreg : P.IsRegular) (F : P.Flag)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (hn : 3 ≤ n)
    (V : Submodule ℝ (E n)) (hV : Module.finrank ℝ V = 2)
    (R : V ≃ₗᵢ[ℝ] V)
    (v w : V) (hv : v ≠ 0) (hw : w ≠ 0)
    (hord : orderOf R = coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩)
    (heq : ⟪(w : E n), ((R v : V) : E n)⟫ =
      ⟪(w : E n), (v : E n)⟫)
    (hlt : ∀ t : ℕ, 2 ≤ t →
      t ≤ coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ - 1 →
      ⟪(w : E n), (((R ^ t) v : V) : E n)⟫ <
        ⟪(w : E n), (v : E n)⟫)
    (hperp : ⟪(w : E n), (v : E n) - ((R v : V) : E n)⟫ = 0) :
    |(⟪(v : E n), (w : E n)⟫ : ℝ)| =
      ‖(v : E n)‖ * ‖(w : E n)‖ *
        Real.cos (Real.pi /
          (coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ : ℝ)) := by
  let m := coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩
  have hm : 3 ≤ m := coxeterMatrix_adiacente_ge_tre_ovunque P hreg F i hi hn
  have hcos := massimo_consecutivo hV R m hm hord v hv w heq hlt
  exact bisezione_ortogonale hV m hm v w (R v) hv hw (R.norm_map v) hperp hcos

/-! ## Pacchetto esplicito del solo innesto ancora mancante -/

/-- Dati geometrici che trasferiscono la separazione dell'orbita alla
restrizione lineare sul piano `V`.  Nessuna condizione è nascosta: in
particolare compaiono sia `orderOf R = m` sia tutte le disuguaglianze
strette richieste da `massimo_consecutivo`. -/
structure DatiMezzoPasso (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    (αi αj : E n) where
  c₁ : E n
  cnext : E n
  V : Submodule ℝ (E n)
  hVspan : V = Submodule.span ℝ ({αi, αj} : Set (E n))
  hc₁_fisso_j : simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ c₁ = c₁
  hc₁_mosso_i : simpleReflection P hreg F i c₁ ≠ c₁
  hcnext_fisso_i : simpleReflection P hreg F i cnext = cnext
  hcnext_mosso_j : simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ cnext ≠ cnext
  R : V ≃ₗᵢ[ℝ] V
  hord : orderOf R = coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩
  heq : ⟪(vettoreProiettato V (centroGlobale P) cnext : E n),
      ((R (vettoreProiettato V (centroGlobale P) c₁) : V) : E n)⟫ =
    ⟪(vettoreProiettato V (centroGlobale P) cnext : E n),
      (vettoreProiettato V (centroGlobale P) c₁ : E n)⟫
  hlt : ∀ t : ℕ, 2 ≤ t →
    t ≤ coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ - 1 →
    ⟪(vettoreProiettato V (centroGlobale P) cnext : E n),
      (((R ^ t) (vettoreProiettato V (centroGlobale P) c₁) : V) : E n)⟫ <
    ⟪(vettoreProiettato V (centroGlobale P) cnext : E n),
      (vettoreProiettato V (centroGlobale P) c₁ : E n)⟫
  hperp : ⟪(vettoreProiettato V (centroGlobale P) cnext : E n),
      (vettoreProiettato V (centroGlobale P) c₁ : E n) -
        ((R (vettoreProiettato V (centroGlobale P) c₁) : V) : E n)⟫ = 0

/-! ## Riparazione simmetrica dell'interfaccia di proiezione -/

/-- Versione generica di `proiettato_fissato`, utilizzabile anche per
la seconda riflessione. -/
theorem proiettato_fissato_da_formula
    {α p O c : E n} {r : E n → E n} (hα : ‖α‖ = 1)
    (hr : ∀ x, r x = x - (2 * ⟪α, x - p⟫ : ℝ) • α)
    {V : Submodule ℝ (E n)} (hαV : α ∈ V)
    (hOfix : r O = O) (hcfix : r c = c) :
    r (puntoProiettato V O c) = puntoProiettato V O c := by
  have hαne : α ≠ 0 := by
    intro h
    rw [h, norm_zero] at hα
    norm_num at hα
  have hfixed : ∀ {x : E n}, r x = x → ⟪α, x - p⟫ = 0 := by
    intro x hx
    rw [hr x] at hx
    have hs : (2 * ⟪α, x - p⟫ : ℝ) • α = 0 := sub_eq_self.mp hx
    have : (2 * ⟪α, x - p⟫ : ℝ) = 0 :=
      (smul_eq_zero.mp hs).resolve_right hαne
    linarith
  have hproj :
      ⟪α, (vettoreProiettato V O c : E n)⟫ = ⟪α, c - O⟫ := by
    have ho := Submodule.inner_right_of_mem_orthogonal hαV
      (V.sub_starProjection_mem_orthogonal (c - O))
    rw [inner_sub_right, sub_eq_zero] at ho
    exact ho.symm
  have hOinner := hfixed hOfix
  have hcinner := hfixed hcfix
  have hcOinner : ⟪α, c - O⟫ = 0 := by
    rw [show c - p = (O - p) + (c - O) by abel, inner_add_right,
      hOinner, zero_add] at hcinner
    exact hcinner
  rw [hr, puntoProiettato]
  rw [show O + (vettoreProiettato V O c : E n) - p =
      (O - p) + (vettoreProiettato V O c : E n) by abel,
    inner_add_right, hOinner, zero_add, hproj, hcOinner, mul_zero,
    zero_smul, sub_zero]

/-- Versione generica di `proiettato_non_fissato`, utilizzabile anche
per la seconda riflessione. -/
theorem proiettato_non_fissato_da_formula
    {α p O c : E n} {r : E n → E n} (hα : ‖α‖ = 1)
    (hr : ∀ x, r x = x - (2 * ⟪α, x - p⟫ : ℝ) • α)
    {V : Submodule ℝ (E n)} (hαV : α ∈ V)
    (hOfix : r O = O) (hcne : r c ≠ c) :
    r (puntoProiettato V O c) ≠ puntoProiettato V O c := by
  have hαne : α ≠ 0 := by
    intro h
    rw [h, norm_zero] at hα
    norm_num at hα
  have hOinner : ⟪α, O - p⟫ = 0 := by
    have h := hOfix
    rw [hr O] at h
    have hs : (2 * ⟪α, O - p⟫ : ℝ) • α = 0 := sub_eq_self.mp h
    have : (2 * ⟪α, O - p⟫ : ℝ) = 0 :=
      (smul_eq_zero.mp hs).resolve_right hαne
    linarith
  have hcinner_ne : ⟪α, c - p⟫ ≠ 0 := by
    intro hc
    apply hcne
    rw [hr c, hc, mul_zero, zero_smul, sub_zero]
  have hproj :
      ⟪α, (vettoreProiettato V O c : E n)⟫ = ⟪α, c - O⟫ := by
    have ho := Submodule.inner_right_of_mem_orthogonal hαV
      (V.sub_starProjection_mem_orthogonal (c - O))
    rw [inner_sub_right, sub_eq_zero] at ho
    exact ho.symm
  intro hfix
  rw [hr] at hfix
  have hs :
      (2 * ⟪α, puntoProiettato V O c - p⟫ : ℝ) • α = 0 :=
    sub_eq_self.mp hfix
  have hscalar : (2 * ⟪α, puntoProiettato V O c - p⟫ : ℝ) = 0 :=
    (smul_eq_zero.mp hs).resolve_right hαne
  apply hcinner_ne
  have hinner : ⟪α, puntoProiettato V O c - p⟫ = ⟪α, c - p⟫ := by
    rw [puntoProiettato]
    rw [show O + (vettoreProiettato V O c : E n) - p =
        (O - p) + (vettoreProiettato V O c : E n) by abel,
      inner_add_right, hOinner, zero_add, hproj]
    rw [show c - p = (O - p) + (c - O) by abel, inner_add_right,
      hOinner, zero_add]
  rw [← hinner]
  linarith

/-! ## Collasso `k = 1` -/

/-- Bersaglio 3.  L'unica ipotesi composta aggiunta alla firma richiesta
è `DatiMezzoPasso`, che espone la separazione e l'ordine della restrizione. -/
theorem rotazione_elementare (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n) (hn : 3 ≤ n)
    {αi pi αj pj : E n} (hαi : ‖αi‖ = 1) (hαj : ‖αj‖ = 1)
    (hri : ∀ x, simpleReflection P hreg F i x =
      x - (2 * ⟪αi, x - pi⟫ : ℝ) • αi)
    (hrj : ∀ x, simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ x =
      x - (2 * ⟪αj, x - pj⟫ : ℝ) • αj)
    (d : DatiMezzoPasso P hreg F i hi αi αj) :
    |(⟪αi, αj⟫ : ℝ)| =
      Real.cos (Real.pi /
        (coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ : ℝ)) := by
  let O := centroGlobale P
  let ci := puntoProiettato d.V O d.c₁
  let cj := puntoProiettato d.V O d.cnext
  have hOi : simpleReflection P hreg F i O = O := by
    exact centro_fisso P hreg (simpleReflection_isSymmetry P hreg F i)
  have hOj : simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ O = O := by
    exact centro_fisso P hreg
      (simpleReflection_isSymmetry P hreg F ⟨(i : ℕ) + 1, hi⟩)
  have hαmem := proiettati_in_V d.V d.hVspan O d.c₁ d.cnext
  rcases hαmem with ⟨hαiV, hαjV, hciV, hcjV⟩
  have hind : ∀ t : ℝ, αj ≠ t • αi :=
    normali_semplici_indipendenti P hreg F (by
      intro h
      have hv := congrArg Fin.val h
      change (i : ℕ) = (i : ℕ) + 1 at hv
      omega) hαi hαj hri hrj
  have hdim : Module.finrank ℝ d.V = 2 := by
    rw [d.hVspan]
    exact finrank_span_normali hαi hind
  have hcifix : simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ ci = ci := by
    exact proiettato_fissato_da_formula hαj hrj hαjV hOj d.hc₁_fisso_j
  have hcjne : simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ cj ≠ cj := by
    exact proiettato_non_fissato_da_formula hαj hrj hαjV hOj d.hcnext_mosso_j
  have hcjfix : simpleReflection P hreg F i cj = cj := by
    dsimp only [cj, O]
    exact proiettato_fissato P hreg F i hi hαi hαj hri hrj d.V d.hVspan
      (centroGlobale P) d.cnext hOi d.hcnext_fisso_i
  have hcine : simpleReflection P hreg F i ci ≠ ci := by
    dsimp only [ci, O]
    exact proiettato_non_fissato P hreg F i hi hαi hαj hri hrj d.V d.hVspan
      (centroGlobale P) d.c₁ hOi d.hc₁_mosso_i
  have hv : vettoreProiettato d.V O d.c₁ ≠ 0 := by
    intro hv0
    apply hcine
    dsimp only [ci, puntoProiettato]
    rw [hv0]
    simp only [Submodule.coe_zero, add_zero]
    exact hOi
  have hw : vettoreProiettato d.V O d.cnext ≠ 0 := by
    intro hw0
    apply hcjne
    dsimp only [cj, puntoProiettato]
    rw [hw0]
    simp only [Submodule.coe_zero, add_zero]
    exact hOj
  have hmezzoV := mezzo_passo P hreg F i hi hn d.V hdim d.R
    (vettoreProiettato d.V O d.c₁) (vettoreProiettato d.V O d.cnext)
    hv hw d.hord d.heq d.hlt d.hperp
  have hmezzo : |(⟪ci - O, cj - O⟫ : ℝ)| =
      ‖ci - O‖ * ‖cj - O‖ *
        Real.cos (Real.pi /
          (coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ : ℝ)) := by
    simpa only [ci, cj, puntoProiettato, add_sub_cancel_left] using hmezzoV
  exact rotazione_elementare_da_centroidi P hreg F i hi hαi hαj hri hrj
    O ci cj hOi hOj hcifix hcjfix hcine hcjne d.V hdim hαiV hαjV
    hciV hcjV hmezzo

/-- Bersaglio 4, condizionale allo stesso pacchetto geometrico del mezzo
passo per le normali prodotte da `simpleReflection_formula`. -/
theorem gram_sottodiagonale (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n) (hn : 3 ≤ n)
    (hdata : ∀ {αi pi αj pj : E n}, ‖αi‖ = 1 → ‖αj‖ = 1 →
      (∀ x, simpleReflection P hreg F i x =
        x - (2 * ⟪αi, x - pi⟫ : ℝ) • αi) →
      (∀ x, simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ x =
        x - (2 * ⟪αj, x - pj⟫ : ℝ) • αj) →
      DatiMezzoPasso P hreg F i hi αi αj) :
    ∃ αi αj : E n, ‖αi‖ = 1 ∧ ‖αj‖ = 1 ∧
      ⟪αi, αj⟫ = -Real.cos (Real.pi /
        (coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ : ℝ)) := by
  obtain ⟨αi, pi, hαi, hri⟩ := simpleReflection_formula P hreg F i
  obtain ⟨αj, pj, hαj, hrj⟩ :=
    simpleReflection_formula P hreg F ⟨(i : ℕ) + 1, hi⟩
  have habs := rotazione_elementare P hreg F i hi hn hαi hαj hri hrj
    (hdata hαi hαj hri hrj)
  obtain ⟨εi, εj, hεi, hεj, hnonpos⟩ :=
    normali_orientabili P hreg F i hi hαi hαj hri hrj
  refine ⟨εi • αi, εj • αj, ?_, ?_, ?_⟩
  · rcases hεi with rfl | rfl <;> simp [hαi]
  · rcases hεj with rfl | rfl <;> simp [hαj]
  · have habs' : |(⟪εi • αi, εj • αj⟫ : ℝ)| =
        Real.cos (Real.pi /
          (coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ : ℝ)) := by
      rcases hεi with rfl | rfl <;> rcases hεj with rfl | rfl <;>
        simpa only [one_smul, neg_smul, inner_neg_left, inner_neg_right,
          neg_neg, abs_neg] using habs
    rw [abs_of_nonpos hnonpos] at habs'
    linarith

end LeanEval.Geometry.PlatonicClassification
