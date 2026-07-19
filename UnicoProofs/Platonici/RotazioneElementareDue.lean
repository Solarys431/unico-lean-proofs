import Mathlib
import UnicoProofs.Platonici.RotazioneElementare
import UnicoProofs.Platonici.FaccetteConnesse
import UnicoProofs.Platonici.Iperpiano

open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-!  Il primo lemma isola esattamente il contenuto lineare del piano del
residuo.  Formulare l'appartenenza a `V` esplicitamente è essenziale: nello
spazio ambiente la tesi è falsa già in dimensione tre. -/

/-- In un piano euclideo, ruotare entrambe le coppie di rette di novanta
gradi conserva, in valore assoluto, il loro coseno normalizzato. -/
theorem coseno_da_ortogonalita_nel_piano
    {V : Submodule ℝ (E n)} (hdim : Module.finrank ℝ V = 2)
    {α β u v : E n}
    (hαV : α ∈ V) (hβV : β ∈ V) (huV : u ∈ V) (hvV : v ∈ V)
    (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1)
    (hαv : (⟪α, v⟫ : ℝ) = 0) (hβu : (⟪β, u⟫ : ℝ) = 0) :
    |(⟪α, β⟫ : ℝ)| * (‖u‖ * ‖v‖) = |(⟪u, v⟫ : ℝ)| := by
  letI : Fact (Module.finrank ℝ V = 2) := ⟨hdim⟩
  let o : Orientation ℝ V (Fin 2) :=
    (Module.finBasisOfFinrankEq ℝ V hdim).orientation
  let αV : V := ⟨α, hαV⟩
  let βV : V := ⟨β, hβV⟩
  let uV : V := ⟨u, huV⟩
  let vV : V := ⟨v, hvV⟩
  have hαVnorm : ‖αV‖ = 1 := hα
  have hβVnorm : ‖βV‖ = 1 := hβ
  have hαvV : (⟪αV, vV⟫ : ℝ) = 0 := hαv
  have hβuV : (⟪βV, uV⟫ : ℝ) = 0 := hβu
  have hβv : o.areaForm βV vV =
      (⟪αV, βV⟫ : ℝ) * o.areaForm αV vV := by
    have h := o.inner_mul_areaForm_sub αV βV vV
    rw [hαvV, hαVnorm] at h
    norm_num at h
    exact h.symm
  have huv : (⟪uV, vV⟫ : ℝ) =
      o.areaForm βV uV * o.areaForm βV vV := by
    have h := o.inner_mul_inner_add_areaForm_mul_areaForm βV uV vV
    rw [hβuV, hβVnorm] at h
    norm_num at h
    exact h.symm
  have hareaαv : |o.areaForm αV vV| = ‖vV‖ := by
    rw [o.abs_areaForm_of_orthogonal hαvV, hαVnorm, one_mul]
  have hareaβu : |o.areaForm βV uV| = ‖uV‖ := by
    rw [o.abs_areaForm_of_orthogonal hβuV, hβVnorm, one_mul]
  change |(⟪αV, βV⟫ : ℝ)| * (‖uV‖ * ‖vV‖) =
    |(⟪uV, vV⟫ : ℝ)|
  rw [huv, hβv, abs_mul, abs_mul, hareaβu, hareaαv]
  ring

/-- Un punto fisso della riflessione descritta dalla formula affine dà un
vettore, rispetto a un altro punto fisso, ortogonale alla normale. -/
theorem inner_sub_eq_zero_of_fixed_reflection
    {α p O x : E n} {r : E n → E n} (hα : ‖α‖ = 1)
    (hr : ∀ z, r z = z - (2 * ⟪α, z - p⟫ : ℝ) • α)
    (hO : r O = O) (hx : r x = x) :
    (⟪α, x - O⟫ : ℝ) = 0 := by
  have hαne : α ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hα
    norm_num at hα
  have hfixed : ∀ {z : E n}, r z = z → (⟪α, z - p⟫ : ℝ) = 0 := by
    intro z hz
    rw [hr z] at hz
    have hs : (2 * ⟪α, z - p⟫ : ℝ) • α = 0 := sub_eq_self.mp hz
    have hc : (2 * ⟪α, z - p⟫ : ℝ) = 0 :=
      (smul_eq_zero.mp hs).resolve_right hαne
    linarith
  have hx0 := hfixed hx
  have hO0 := hfixed hO
  rw [show x - O = (x - p) - (O - p) by abel, inner_sub_right, hx0, hO0,
    sub_self]

/-- Firma effettiva del Bersaglio 1.  `V` è il piano lineare del residuo;
le quattro ipotesi di appartenenza sono il ponte geometrico che non è
conseguenza delle sole equazioni di punto fisso nello spazio ambiente. -/
theorem coseno_da_centroidi (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    {αi pi αj pj : E n} (hαi : ‖αi‖ = 1) (hαj : ‖αj‖ = 1)
    (hri : ∀ x : E n, simpleReflection P hreg F i x =
      x - (2 * ⟪αi, x - pi⟫ : ℝ) • αi)
    (hrj : ∀ x : E n,
      simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ x =
        x - (2 * ⟪αj, x - pj⟫ : ℝ) • αj)
    (O ci cj : E n)
    (hOi : simpleReflection P hreg F i O = O)
    (hOj : simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ O = O)
    (hci : simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ ci = ci)
    (hcj : simpleReflection P hreg F i cj = cj)
    (_hcine : simpleReflection P hreg F i ci ≠ ci)
    (_hcjne : simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ cj ≠ cj)
    (V : Submodule ℝ (E n)) (hdim : Module.finrank ℝ V = 2)
    (hαiV : αi ∈ V) (hαjV : αj ∈ V)
    (hciV : ci - O ∈ V) (hcjV : cj - O ∈ V) :
    |(⟪αi, αj⟫ : ℝ)| * (‖ci - O‖ * ‖cj - O‖) =
      |(⟪ci - O, cj - O⟫ : ℝ)| := by
  apply coseno_da_ortogonalita_nel_piano hdim hαiV hαjV hciV hcjV hαi hαj
  · exact inner_sub_eq_zero_of_fixed_reflection hαi hri hOi hcj
  · exact inner_sub_eq_zero_of_fixed_reflection hαj hrj hOj hci

/-- Una volta certificato il mezzo passo, la conclusione cercata segue per
cancellazione delle due norme, che sono non nulle grazie alle ipotesi di
non fissità.  Questo lemma registra che non resta alcun ulteriore ostacolo
algebrico dopo il Bersaglio 2. -/
theorem rotazione_elementare_da_centroidi
    (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    {αi pi αj pj : E n} (hαi : ‖αi‖ = 1) (hαj : ‖αj‖ = 1)
    (hri : ∀ x : E n, simpleReflection P hreg F i x =
      x - (2 * ⟪αi, x - pi⟫ : ℝ) • αi)
    (hrj : ∀ x : E n,
      simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ x =
        x - (2 * ⟪αj, x - pj⟫ : ℝ) • αj)
    (O ci cj : E n)
    (hOi : simpleReflection P hreg F i O = O)
    (hOj : simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ O = O)
    (hci : simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ ci = ci)
    (hcj : simpleReflection P hreg F i cj = cj)
    (hcine : simpleReflection P hreg F i ci ≠ ci)
    (hcjne : simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ cj ≠ cj)
    (V : Submodule ℝ (E n)) (hdim : Module.finrank ℝ V = 2)
    (hαiV : αi ∈ V) (hαjV : αj ∈ V)
    (hciV : ci - O ∈ V) (hcjV : cj - O ∈ V)
    (hmezzo : |(⟪ci - O, cj - O⟫ : ℝ)| =
      ‖ci - O‖ * ‖cj - O‖ *
        Real.cos (Real.pi /
          (coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ : ℝ))) :
    |(⟪αi, αj⟫ : ℝ)| =
      Real.cos (Real.pi /
        (coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ : ℝ)) := by
  have hciO : ci ≠ O := by
    intro heq
    apply hcine
    rw [heq]
    exact hOi
  have hcjO : cj ≠ O := by
    intro heq
    apply hcjne
    rw [heq]
    exact hOj
  have hnormne : ‖ci - O‖ * ‖cj - O‖ ≠ 0 := by
    apply mul_ne_zero
    · exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hciO)
    · exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hcjO)
  have hcos := coseno_da_centroidi P hreg F i hi hαi hαj hri hrj O ci cj
    hOi hOj hci hcj hcine hcjne V hdim hαiV hαjV hciV hcjV
  apply mul_left_cancel₀ hnormne
  calc
    (‖ci - O‖ * ‖cj - O‖) * |(⟪αi, αj⟫ : ℝ)| =
        |(⟪αi, αj⟫ : ℝ)| * (‖ci - O‖ * ‖cj - O‖) := mul_comm _ _
    _ = |(⟪ci - O, cj - O⟫ : ℝ)| := hcos
    _ = (‖ci - O‖ * ‖cj - O‖) *
        Real.cos (Real.pi /
          (coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ : ℝ)) := hmezzo

/-!
Kill-gate del Bersaglio 2.

La firma proposta senza ulteriori ipotesi è falsa: `O`, `ci` e `cj` sono
arbitrari.  Scegliendo `ci = cj ≠ O`, dopo cancellazione della norma la tesi
direbbe `1 = cos (pi / m)`, impossibile per `m ≥ 3`.

Per la versione geometrica intesa non basta aggiungere le sole equazioni di
punto fisso.  `FaccetteConnesse.relative_image_isFace` costruisce il residuo
di salto tre in dimensione tre e conserva le facce, ma non costruisce la sua
sezione (link) poligonale bidimensionale.  Manca quindi un teorema che:

* identifichi le proiezioni dei centroidi di rango `i` e `i+1` con,
  rispettivamente, un raggio di vertice e il bisettore del lato incidente;
* identifichi l'orbita del secondo raggio con tutti e soli gli `m` lati in
  ordine ciclico, dove `m` è `coxeterMatrix ... i (i+1)`.

Il lemma `rotazione_elementare_da_centroidi` sopra certifica che questo è
l'unico ponte ancora necessario per la conclusione algebrica.
-/

end LeanEval.Geometry.PlatonicClassification
