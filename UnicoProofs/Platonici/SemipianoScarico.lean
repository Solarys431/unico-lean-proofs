-- NON RIUSCITO: faccetta_adiacente_eq perche' tutti i suoi dati geometrici
-- (lato comune, piano comune e semipiano canonico) sono derivati qui sotto,
-- ma l'unico teorema finale disponibile, faccetta_determinata, richiede che
-- segment x (rho x) del testimone d'orbita sia quel lato. IsRegularFacet non
-- lo garantisce: per p = 5 rho puo' avanzare lungo le diagonali. Serve un
-- nuovo lemma che riparametrizzi l'orbita lungo i vicini del bordo, oppure
-- una versione di faccetta_determinata formulata con un lato esposto esterno.

import UnicoProofs.Platonici.Normalizzazione
import UnicoProofs.Platonici.PonteEsposizione
import UnicoProofs.Platonici.PianiRaggi
import UnicoProofs.Platonici.IndipendenzaRaggi
import UnicoProofs.Platonici.VerticeAdiacente
import UnicoProofs.Platonici.BandieraSpigolo

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope
open PlatoniciA13

/-- Un funzionale lineare che assume lo stesso valore in due punti e'
costante su tutta la retta affine da essi generata. -/
theorem funzionale_costante_sulla_retta {v w z : E 3}
    (g : E 3 →L[ℝ] ℝ) (hgw : g v = g w)
    (hz : z ∈ affineSpan ℝ ({v, w} : Set (E 3))) :
    g z = g v := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hz
  obtain ⟨t, rfl⟩ := hz
  simp [AffineMap.lineMap_apply, hgw]

/-- Una faccia esposta che e' un segmento obbliga ogni altro funzionale
costante sul segmento ad avere segno uniforme, non appena nel piano si
fissa un punto trasverso. La decomposizione in `hg_piano` e' la forma
algebrica, indipendente dalle coordinate, del fatto che `A` sta nel piano
generato dalle due direzioni indicate. -/
theorem side_di_faccia_esposta
    {A L : Set (E 3)} {v w x : E 3}
    (_hAconv : Convex ℝ A)
    (hL : IsExposed ℝ A L) (hLseg : L = segment ℝ v w)
    (hxA : x ∈ A) (hxL : x ∉ L)
    (g : E 3 →L[ℝ] ℝ)
    (hg_lato : g v = g w)
    (hg_piano : ∀ z ∈ A, ∃ a b : ℝ,
      z - v = a • (w - v) + b • (x - v)) :
    (∀ z ∈ A, g v ≤ g z) ∨ (∀ z ∈ A, g z ≤ g v) := by
  have hvL : v ∈ L := by
    rw [hLseg]
    exact left_mem_segment ℝ v w
  have hwL : w ∈ L := by
    rw [hLseg]
    exact right_mem_segment ℝ v w
  obtain ⟨l, hl⟩ := hL ⟨v, hvL⟩
  have hvmax : v ∈ A ∧ ∀ z ∈ A, l z ≤ l v := by
    have h := hvL
    rw [hl] at h
    exact h
  have hwmax : w ∈ A ∧ ∀ z ∈ A, l z ≤ l w := by
    have h := hwL
    rw [hl] at h
    exact h
  have hlvw : l v = l w := le_antisymm (hwmax.2 v hvmax.1)
    (hvmax.2 w hwmax.1)
  have hlx : l x < l v := by
    have hle : l x ≤ l v := hvmax.2 x hxA
    exact lt_of_le_of_ne hle fun heq => by
      apply hxL
      rw [hl]
      exact ⟨hxA, fun z hz => (hvmax.2 z hz).trans (le_of_eq heq.symm)⟩
  rcases le_total (g v) (g x) with hgpos | hgneg
  · left
    intro z hzA
    obtain ⟨a, b, hab⟩ := hg_piano z hzA
    have hlform : l z - l v = b * (l x - l v) := by
      have happ := congrArg l hab
      simp only [map_sub, map_add, map_smul] at happ
      calc
        l z - l v = a * (l w - l v) + b * (l x - l v) := by
          simpa [smul_eq_mul] using happ
        _ = b * (l x - l v) := by rw [← hlvw]; simp
    have hb : 0 ≤ b := by
      have hzle : l z ≤ l v := hvmax.2 z hzA
      have hneg : l x - l v < 0 := by linarith
      exact nonneg_of_mul_nonpos_right (by linarith [hlform]) hneg
    have hgform : g z - g v = b * (g x - g v) := by
      have happ := congrArg g hab
      simp only [map_sub, map_add, map_smul] at happ
      calc
        g z - g v = a * (g w - g v) + b * (g x - g v) := by
          simpa [smul_eq_mul] using happ
        _ = b * (g x - g v) := by rw [← hg_lato]; simp
    have hdiff : 0 ≤ g x - g v := sub_nonneg.mpr hgpos
    nlinarith [mul_nonneg hb hdiff]
  · right
    intro z hzA
    obtain ⟨a, b, hab⟩ := hg_piano z hzA
    have hlform : l z - l v = b * (l x - l v) := by
      have happ := congrArg l hab
      simp only [map_sub, map_add, map_smul] at happ
      calc
        l z - l v = a * (l w - l v) + b * (l x - l v) := by
          simpa [smul_eq_mul] using happ
        _ = b * (l x - l v) := by rw [← hlvw]; simp
    have hb : 0 ≤ b := by
      have hzle : l z ≤ l v := hvmax.2 z hzA
      have hneg : l x - l v < 0 := by linarith
      exact nonneg_of_mul_nonpos_right (by linarith [hlform]) hneg
    have hgform : g z - g v = b * (g x - g v) := by
      have happ := congrArg g hab
      simp only [map_sub, map_add, map_smul] at happ
      calc
        g z - g v = a * (g w - g v) + b * (g x - g v) := by
          simpa [smul_eq_mul] using happ
        _ = b * (g x - g v) := by rw [← hg_lato]; simp
    have hdiff : g x - g v ≤ 0 := sub_nonpos.mpr hgneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hb hdiff]

/-- Se il nucleo affine del funzionale, dentro `A`, non esce dalla retta
del lato, l'annullamento e' esattamente il lato esposto. -/
theorem annullamento_eq_lato
    {A : Set (E 3)} {v w : E 3} (g : E 3 →L[ℝ] ℝ)
    (_hside : ∀ z ∈ A, g v ≤ g z)
    (hesposta : IsExposed ℝ A (segment ℝ v w))
    (hg : g v = g w)
    (hg_piano : ∀ z ∈ A, g z = g v →
      z ∈ affineSpan ℝ ({v, w} : Set (E 3))) :
    {z ∈ A | g z = g v} = segment ℝ v w := by
  have hseg_nonempty : (segment ℝ v w).Nonempty :=
    ⟨v, left_mem_segment ℝ v w⟩
  obtain ⟨l, hl⟩ := hesposta hseg_nonempty
  have hvseg : v ∈ segment ℝ v w := left_mem_segment ℝ v w
  have hwseg : w ∈ segment ℝ v w := right_mem_segment ℝ v w
  have hvmax : v ∈ A ∧ ∀ z ∈ A, l z ≤ l v := by
    have h := hvseg
    rw [hl] at h
    exact h
  have hwmax : w ∈ A ∧ ∀ z ∈ A, l z ≤ l w := by
    have h := hwseg
    rw [hl] at h
    exact h
  have hlvw : l v = l w := le_antisymm (hwmax.2 v hvmax.1)
    (hvmax.2 w hwmax.1)
  ext z
  constructor
  · rintro ⟨hzA, hzg⟩
    have hzline := hg_piano z hzA hzg
    have hlz : l z = l v := funzionale_costante_sulla_retta l hlvw hzline
    rw [hl]
    exact ⟨hzA, fun y hy => (hvmax.2 y hy).trans (le_of_eq hlz.symm)⟩
  · intro hzseg
    have hzA : z ∈ A := hesposta.subset hzseg
    have hzline : z ∈ affineSpan ℝ ({v, w} : Set (E 3)) :=
      affineSegment_subset_affineSpan ℝ v w (by
        rw [affineSegment_eq_segment]
        exact hzseg)
    exact ⟨hzA, funzionale_costante_sulla_retta g hg hzline⟩

/-- Riscalare separatamente due vettori indipendenti per coefficienti non
nulli conserva l'indipendenza. -/
theorem indipendenti_smul_separati {u r : E 3} {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hind : LinearIndependent ℝ ![u, r]) :
    LinearIndependent ℝ ![a • u, b • r] := by
  rw [LinearIndependent.pair_iff] at hind ⊢
  intro s t hst
  have hst' : (s * a) • u + (t * b) • r = 0 := by
    simpa [smul_smul, mul_assoc] using hst
  obtain ⟨hsa, htb⟩ := hind (s * a) (t * b) hst'
  constructor
  · rcases mul_eq_zero.mp hsa with hs | ha0
    · exact hs
    · exact (ha ha0).elim
  · rcases mul_eq_zero.mp htb with ht | hb0
    · exact ht
    · exact (hb hb0).elim

/-- La giacitura di rango due fornisce la decomposizione usata da
`side_di_faccia_esposta`. -/
theorem decomposizione_nel_piano
    {A : Set (E 3)} {v w x : E 3}
    (hvA : v ∈ A) (hwA : w ∈ A) (hxA : x ∈ A)
    (hind : LinearIndependent ℝ ![w - v, x - v])
    (hrank : Module.finrank ℝ (vectorSpan ℝ A) = 2) :
    ∀ z ∈ A, ∃ a b : ℝ,
      z - v = a • (w - v) + b • (x - v) := by
  have hspan := vectorSpan_eq_span_due hvA hwA hxA hind hrank
  intro z hzA
  have hzmem : z - v ∈ vectorSpan ℝ A := sub_mem_vectorSpan hzA hvA
  rw [hspan, Submodule.mem_span_pair] at hzmem
  obtain ⟨a, b, hab⟩ := hzmem
  exact ⟨a, b, hab.symm⟩

/-- Se un funzionale e' costante sul primo generatore e non sul secondo,
il suo livello per `v`, dentro il piano generato, e' la retta del primo. -/
theorem livello_nel_piano_sottoinsieme_retta
    {A : Set (E 3)} {v w x : E 3} (g : E 3 →L[ℝ] ℝ)
    (hgw : g v = g w) (hgx : g x ≠ g v)
    (hpiano : ∀ z ∈ A, ∃ a b : ℝ,
      z - v = a • (w - v) + b • (x - v)) :
    ∀ z ∈ A, g z = g v →
      z ∈ affineSpan ℝ ({v, w} : Set (E 3)) := by
  intro z hzA hzg
  obtain ⟨a, b, hab⟩ := hpiano z hzA
  have happ := congrArg g hab
  simp only [map_sub, map_add, map_smul] at happ
  have hform : g z - g v = b * (g x - g v) := by
    calc
      g z - g v = a * (g w - g v) + b * (g x - g v) := by
        simpa [smul_eq_mul] using happ
      _ = b * (g x - g v) := by rw [← hgw]; simp
  have hb : b = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right
    · exact sub_ne_zero.mpr hgx
    · rw [hzg, sub_self] at hform
      exact hform.symm
  rw [hb, zero_smul, add_zero] at hab
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  refine ⟨a, ?_⟩
  rw [AffineMap.lineMap_apply]
  change a • (w - v) + v = z
  rw [← hab]
  abel

/-- Il funzionale canonico e' costante sul lato e cresce strettamente sul
secondo raggio. -/
theorem funzionale_secondo_raggio_proprieta {v x w : E 3}
    (hind : LinearIndependent ℝ ![w - v, x - v]) :
    funzionale_secondo_raggio v x w v =
        funzionale_secondo_raggio v x w w ∧
      funzionale_secondo_raggio v x w v <
        funzionale_secondo_raggio v x w x := by
  let u : E 3 := w - v
  let a : E 3 := x - v
  let c : ℝ := ⟪a, u⟫ / ⟪u, u⟫
  let n : E 3 := a - c • u
  have hindua : LinearIndependent ℝ ![u, a] := by
    simpa [u, a] using hind
  have hu_ne : u ≠ 0 := hindua.ne_zero (0 : Fin 2)
  have huu_pos : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu_ne
  have hnu : ⟪n, u⟫ = 0 := by
    dsimp [n, c]
    rw [inner_sub_left, real_inner_smul_left]
    field_simp
    ring
  have hn_ne : n ≠ 0 := by
    intro hn
    have hacu : a = c • u := sub_eq_zero.mp hn
    have hind' := hindua
    rw [linearIndependent_fin2] at hind'
    change a ≠ 0 ∧ ∀ r : ℝ, r • a ≠ u at hind'
    by_cases hc : c = 0
    · apply hind'.1
      exact hacu.trans (by rw [hc, zero_smul])
    · apply hind'.2 c⁻¹
      rw [hacu, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hna_pos : 0 < ⟪n, a⟫ := by
    have ha : a = n + c • u := by
      dsimp [n]
      abel
    rw [ha, inner_add_right, real_inner_smul_right, hnu]
    simp only [mul_zero, add_zero]
    exact real_inner_self_pos.mpr hn_ne
  have hfun : funzionale_secondo_raggio v x w = innerSL ℝ n := by
    rfl
  constructor
  · rw [hfun]
    simp only [innerSL_apply_apply]
    rw [← sub_eq_zero, ← inner_sub_right]
    change ⟪n, v - w⟫ = 0
    rw [show v - w = -u by simp [u], inner_neg_right, hnu, neg_zero]
  · have hdiff : funzionale_secondo_raggio v x w x -
        funzionale_secondo_raggio v x w v = ⟪n, a⟫ := by
      rw [hfun]
      simp only [innerSL_apply_apply, ← inner_sub_right, a]
    linarith

/-- Scarico completo delle due ipotesi di `semipiano_dal_secondo_raggio`
per una faccia planare esposta lungo il lato `v,w`. Il punto `x` fissa il
lato canonico del semipiano. -/
theorem scarico_faccetta_esposta
    {A : Set (E 3)} {v w x : E 3}
    (hAconv : Convex ℝ A) (hvA : v ∈ A) (hwA : w ∈ A) (hxA : x ∈ A)
    (hesposta : IsExposed ℝ A (segment ℝ v w))
    (hxL : x ∉ segment ℝ v w)
    (hind : LinearIndependent ℝ ![w - v, x - v])
    (hrank : Module.finrank ℝ (vectorSpan ℝ A) = 2) :
    (∀ z ∈ A, funzionale_secondo_raggio v x w v ≤
      funzionale_secondo_raggio v x w z) ∧
    {z ∈ A | funzionale_secondo_raggio v x w z =
      funzionale_secondo_raggio v x w v} = segment ℝ v w := by
  let g := funzionale_secondo_raggio v x w
  have hpiano : ∀ z ∈ A, ∃ a b : ℝ,
      z - v = a • (w - v) + b • (x - v) :=
    decomposizione_nel_piano hvA hwA hxA hind hrank
  have hgprop := funzionale_secondo_raggio_proprieta hind
  have hg_lato : g v = g w := by
    simpa [g] using hgprop.1
  have hgvx : g v < g x := by
    simpa [g] using hgprop.2
  have hside := side_di_faccia_esposta hAconv hesposta rfl hxA hxL
    g hg_lato hpiano
  have hlower : ∀ z ∈ A, g v ≤ g z := by
    rcases hside with h | h
    · exact h
    · exact (not_le_of_gt hgvx (h x hxA)).elim
  have hkern : ∀ z ∈ A, g z = g v →
      z ∈ affineSpan ℝ ({v, w} : Set (E 3)) :=
    livello_nel_piano_sottoinsieme_retta g hg_lato (ne_of_gt hgvx) hpiano
  refine ⟨?_, ?_⟩
  · simpa [g] using hlower
  · exact annullamento_eq_lato g hlower hesposta hg_lato hkern

/-- Due facce planari con lo stesso lato esposto e lo stesso secondo raggio
hanno il semipiano comune richiesto dal gate di rigidita'. -/
theorem semipiano_da_lato_esposto_e_secondo_raggio
    {A B : Set (E 3)} {v w x : E 3}
    (hAconv : Convex ℝ A) (hBconv : Convex ℝ B)
    (hvA : v ∈ A) (hvB : v ∈ B)
    (hwA : w ∈ A) (hwB : w ∈ B)
    (hxA : x ∈ A) (hxB : x ∈ B)
    (hpiano : affineSpan ℝ A = affineSpan ℝ B)
    (hespostaA : IsExposed ℝ A (segment ℝ v w))
    (hespostaB : IsExposed ℝ B (segment ℝ v w))
    (hxL : x ∉ segment ℝ v w)
    (hind : LinearIndependent ℝ ![w - v, x - v])
    (hrankA : Module.finrank ℝ (vectorSpan ℝ A) = 2)
    (hrankB : Module.finrank ℝ (vectorSpan ℝ B) = 2) :
    SemipianoComune A B v w := by
  have hA := scarico_faccetta_esposta hAconv hvA hwA hxA hespostaA
    hxL hind hrankA
  have hB := scarico_faccetta_esposta hBconv hvB hwB hxB hespostaB
    hxL hind hrankB
  exact semipiano_dal_secondo_raggio hAconv hBconv hvA hvB hxA hxB hpiano
    (Or.inl hA.1) (Or.inl hB.1) hA.2 hB.2 hind

/-- Montaggio canonico dei tre dati geometrici locali: il lato corrente,
il raggio precedente che ne fissa il semipiano, e il piano della faccetta.
I punti finali sono presi dal solo politopo `P`; l'uguaglianza degli spigoli
come insiemi li rende automaticamente validi anche per `Q`. -/
theorem dati_faccetta_adiacente
    (P Q : ConvexPolytope 3) {p q : ℕ}
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (hQ : Q.asFinite.IsCyclicallyRegularOfType p q)
    {v : E 3} (hvP : v ∈ P.vertices) (hvQ : v ∈ Q.vertices)
    (DP : P.asFinite.CyclicVertexData v q)
    (DQ : Q.asFinite.CyclicVertexData v q)
    (hdir : dir P.asFinite v DP = dir Q.asFinite v DQ)
    (hdiam : ∀ k, Metric.diam
        (DP.faccetta k ∩ DP.faccetta (finRotate q k)) =
      Metric.diam (DQ.faccetta k ∩ DQ.faccetta (finRotate q k)))
    (i : Fin q) :
    ∃ w : E 3,
      DP.faccetta i ∩ DP.faccetta (finRotate q i) = segment ℝ v w ∧
      DQ.faccetta i ∩ DQ.faccetta (finRotate q i) = segment ℝ v w ∧
      affineSpan ℝ (DP.faccetta i) = affineSpan ℝ (DQ.faccetta i) ∧
      SemipianoComune (DP.faccetta i) (DQ.faccetta i) v w := by
  classical
  let j : Fin q := (finRotate q).symm i
  have hji : finRotate q j = i := (finRotate q).apply_symm_apply i
  let eW : SpigoloPer P v := spigolo_adiacente P hP.2.2.1 DP i
  let eX : SpigoloPer P v := spigolo_adiacente P hP.2.2.1 DP j
  let w : E 3 := SpigoloPer.altro P v hvP eW
  let x : E 3 := SpigoloPer.altro P v hvP eX
  have hwSpec := SpigoloPer.altro_spec P v hvP eW
  have hxSpec := SpigoloPer.altro_spec P v hvP eX
  have hedgePW : DP.faccetta i ∩ DP.faccetta (finRotate q i) =
      segment ℝ v w := by
    simpa [eW, w] using hwSpec.2.2.2
  have hedgePX : DP.faccetta j ∩ DP.faccetta i = segment ℝ v x := by
    simpa [eX, x, hji] using hxSpec.2.2.2
  have hedgeCommonW := spigolo_del_fan_eq P Q hP hQ hvP hvQ DP DQ i
    (congrFun hdir i) (hdiam i)
  have hedgeCommonX := spigolo_del_fan_eq P Q hP hQ hvP hvQ DP DQ j
    (congrFun hdir j) (hdiam j)
  have hedgeQW : DQ.faccetta i ∩ DQ.faccetta (finRotate q i) =
      segment ℝ v w := hedgeCommonW.symm.trans hedgePW
  have hedgeQX : DQ.faccetta j ∩ DQ.faccetta i = segment ℝ v x := by
    calc
      DQ.faccetta j ∩ DQ.faccetta i =
          DQ.faccetta j ∩ DQ.faccetta (finRotate q j) := by rw [hji]
      _ = DP.faccetta j ∩ DP.faccetta (finRotate q j) :=
        hedgeCommonX.symm
      _ = DP.faccetta j ∩ DP.faccetta i := by rw [hji]
      _ = segment ℝ v x := hedgePX
  have hwPface : w ∈ DP.faccetta i := by
    have hw : w ∈ DP.faccetta i ∩ DP.faccetta (finRotate q i) := by
      rw [hedgePW]
      exact right_mem_segment ℝ v w
    exact hw.1
  have hxPface : x ∈ DP.faccetta i := by
    have hx : x ∈ DP.faccetta j ∩ DP.faccetta i := by
      rw [hedgePX]
      exact right_mem_segment ℝ v x
    exact hx.2
  have hwQface : w ∈ DQ.faccetta i := by
    have hw : w ∈ DQ.faccetta i ∩ DQ.faccetta (finRotate q i) := by
      rw [hedgeQW]
      exact right_mem_segment ℝ v w
    exact hw.1
  have hxQface : x ∈ DQ.faccetta i := by
    have hx : x ∈ DQ.faccetta j ∩ DQ.faccetta i := by
      rw [hedgeQX]
      exact right_mem_segment ℝ v x
    exact hx.2
  obtain ⟨tW, htW, hwRay⟩ := altro_estremo_sul_raggio P hP hvP DP i
  obtain ⟨tX, htX, hxRay⟩ := altro_estremo_sul_raggio P hP hvP DP j
  have hwRay' : w = v + tW • dir P.asFinite v DP i := by
    simpa [eW, w] using hwRay
  have hxRay' : x = v + tX • dir P.asFinite v DP j := by
    simpa [eX, x] using hxRay
  have hrayJI : LinearIndependent ℝ
      ![dir P.asFinite v DP i, dir P.asFinite v DP j] := by
    have h := raggi_consecutivi_indipendenti P hP hvP DP j
    have hs := LinearIndependent.pair_symm_iff.mp h
    simpa [hji] using hs
  have hindScaled := indipendenti_smul_separati
    (ne_of_gt htW) (ne_of_gt htX) hrayJI
  have hind : LinearIndependent ℝ ![w - v, x - v] := by
    have hwSub : w - v = tW • dir P.asFinite v DP i := by
      rw [hwRay']
      abel
    have hxSub : x - v = tX • dir P.asFinite v DP j := by
      rw [hxRay']
      abel
    simpa [hwSub, hxSub] using hindScaled
  have hxNot : x ∉ segment ℝ v w := by
    intro hxL
    have hxcurr : x ∈ DP.faccetta i ∩ DP.faccetta (finRotate q i) := by
      rw [hedgePW]
      exact hxL
    have hxprev : x ∈ DP.faccetta j ∩ DP.faccetta (finRotate q j) := by
      rw [hji, hedgePX]
      exact right_mem_segment ℝ v x
    have hcases := DP.spigolo_due i j x hxcurr hxSpec.2.2.1 hxprev.1
    rcases hcases with hjeq | hjrot
    · have hh := congrArg (finRotate q) hjeq
      rw [hji] at hh
      have hq2 : 2 ≤ q := by
        have hq3 := hP.2.2.1
        omega
      exact _root_.finRotate_ne_self hq2 i hh.symm
    · apply finRotate_due_ne hP.2.2.1 j
      calc
        finRotate q (finRotate q j) = finRotate q i := by rw [hji]
        _ = j := hjrot.symm
  have hpiano : affineSpan ℝ (DP.faccetta i) =
      affineSpan ℝ (DQ.faccetta i) :=
    affineSpan_eq_of_raggi_eq
      (DP.mem_v i) hwPface hxPface (DQ.mem_v i) hwQface hxQface
      hind hind (DP.isFacet i).2 (DQ.isFacet i).2 rfl
  have hconvP : Convex ℝ (DP.faccetta i) :=
    (DP.isFacet i).1.1.convex (convex_convexHull ℝ _)
  have hconvQ : Convex ℝ (DQ.faccetta i) :=
    (DQ.isFacet i).1.1.convex (convex_convexHull ℝ _)
  have hexpP0 : IsExposed ℝ (DP.faccetta i)
      (DP.faccetta i ∩ DP.faccetta (finRotate q i)) :=
    spigolo_esposto_nella_faccetta (DP.isFacet i).1.1
      (DP.isFacet (finRotate q i)).1.1
  have hexpQ0 : IsExposed ℝ (DQ.faccetta i)
      (DQ.faccetta i ∩ DQ.faccetta (finRotate q i)) :=
    spigolo_esposto_nella_faccetta (DQ.isFacet i).1.1
      (DQ.isFacet (finRotate q i)).1.1
  have hexpP : IsExposed ℝ (DP.faccetta i) (segment ℝ v w) := by
    rw [← hedgePW]
    exact hexpP0
  have hexpQ : IsExposed ℝ (DQ.faccetta i) (segment ℝ v w) := by
    rw [← hedgeQW]
    exact hexpQ0
  have hsemi := semipiano_da_lato_esposto_e_secondo_raggio
    hconvP hconvQ (DP.mem_v i) (DQ.mem_v i) hwPface hwQface
    hxPface hxQface hpiano hexpP hexpQ hxNot hind
    (DP.isFacet i).2 (DQ.isFacet i).2
  exact ⟨w, hedgePW, hedgeQW, hpiano, hsemi⟩

end LeanEval.Geometry.PlatonicClassification
