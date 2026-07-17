import Mathlib
import UnicoProofs.Platonici.Killer
import UnicoProofs.Platonici.Ordine
import UnicoProofs.Platonici.OrbitaTraslata
import UnicoProofs.Platonici.RotazionePoligono
import UnicoProofs.Platonici.ArgmaxCoseno
import UnicoProofs.Platonici.FacciaArgmax

/-!
A14 — LO SPIGOLO PUNTA AL VICINO (campagna #50, G1-mio, assemblaggio).

Nel modello 2D: se un funzionale lineare non costante sul poligono orbitale
raggiunge il massimo nel vertice 0 e in un altro punto y ≠ 0 dell'hull,
allora y giace sul segmento da 0 verso UNO dei due vertici adiacenti
cc + rot(±2π/p)(0 − cc). Catena: rotazione del poligono (L1) → estrazione
dell'angolo (killer) → valori come coseno (inner_orbita) → argmax adiacente
(L2', testimoni = inversi modulari come nel killer) → doppio pareggio
impossibile → faccia argmax = segmento (L3).
-/

open Real
open scoped RealInnerProductSpace
open PlatoniciL1 PlatoniciL2 PlatoniciL3 PlatoniciA4 PlatoniciA10

namespace PlatoniciA14

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- Le iterate di un'isometria lineare commutano con lo smul. -/
theorem iterate_smul (f : E ≃ₗᵢ[ℝ] E) (r : ℝ) (x : E) (k : ℕ) :
    (⇑f)^[k] (r • x) = r • (⇑f)^[k] x := by
  induction k with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        map_smul]

/-- Un doppio pareggio del coseno sulle due posizioni adiacenti è
impossibile: costringerebbe sin φ e cos φ a svanire insieme. -/
theorem non_doppio_pareggio {φ b : ℝ} (hb0 : 0 < b) (hbπ : b < π)
    (h1 : Real.cos (φ + b) = Real.cos φ)
    (h2 : Real.cos (φ - b) = Real.cos φ) : False := by
  have hbpos : 0 < Real.sin (b / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hz1 : Real.sin (φ + b / 2) = 0 := by
    have hd : Real.cos (φ + b) - Real.cos φ = 0 := by rw [h1]; ring
    rw [Real.cos_sub_cos] at hd
    have e1 : (φ + b + φ) / 2 = φ + b / 2 := by ring
    have e2 : (φ + b - φ) / 2 = b / 2 := by ring
    rw [e1, e2] at hd
    rcases mul_eq_zero.mp (by linarith :
        Real.sin (φ + b / 2) * Real.sin (b / 2) = 0) with h | h
    · exact h
    · exact absurd h (ne_of_gt hbpos)
  have hz2 : Real.sin (φ - b / 2) = 0 := by
    have hd : Real.cos (φ - b) - Real.cos φ = 0 := by rw [h2]; ring
    rw [Real.cos_sub_cos] at hd
    have e1 : (φ - b + φ) / 2 = φ - b / 2 := by ring
    have e2 : (φ - b - φ) / 2 = -(b / 2) := by ring
    rw [e1, e2, Real.sin_neg] at hd
    rcases mul_eq_zero.mp (by linarith :
        Real.sin (φ - b / 2) * Real.sin (b / 2) = 0) with h | h
    · exact h
    · exact absurd h (ne_of_gt hbpos)
  have hcφ : Real.cos φ * Real.sin (b / 2) = 0 := by
    have hA := Real.sin_add φ (b / 2)
    have hB := Real.sin_sub φ (b / 2)
    have hC : Real.sin (φ + b / 2) - Real.sin (φ - b / 2)
        = 2 * Real.cos φ * Real.sin (b / 2) := by
      rw [hA, hB]; ring
    rw [hz1, hz2] at hC
    linarith
  have hsφ : Real.sin φ * Real.cos (b / 2) = 0 := by
    have hA := Real.sin_add φ (b / 2)
    have hB := Real.sin_sub φ (b / 2)
    have hC : Real.sin (φ + b / 2) + Real.sin (φ - b / 2)
        = 2 * Real.sin φ * Real.cos (b / 2) := by
      rw [hA, hB]; ring
    rw [hz1, hz2] at hC
    linarith
  have hcos0 : Real.cos φ = 0 := by
    rcases mul_eq_zero.mp hcφ with h | h
    · exact h
    · exact absurd h (ne_of_gt hbpos)
  by_cases hcb : Real.cos (b / 2) = 0
  · obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hcb
    have hπ : (0 : ℝ) < π := Real.pi_pos
    have hk0 : k = 0 := by
      by_contra hkne
      rcases lt_or_gt_of_ne hkne with hneg | hpos
      · have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
        nlinarith
      · have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hpos
        nlinarith
    rw [hk0] at hk
    simp at hk
    linarith
  · have hsin0 : Real.sin φ = 0 := by
      rcases mul_eq_zero.mp hsφ with h | h
      · exact h
      · exact absurd h hcb
    have := Real.sin_sq_add_cos_sq φ
    rw [hsin0, hcos0] at this
    norm_num at this

/-- LO SPIGOLO PUNTA AL VICINO. -/
theorem spigolo_verso_vicino (o : Orientation ℝ E (Fin 2))
    (χ : E ≃ᵃⁱ[ℝ] E) (cc : E) (hcc : χ cc = cc)
    {p : ℕ} (hp : 3 ≤ p) (hclosed : (⇑χ)^[p] (0 : E) = 0)
    (hinj : Function.Injective (fun i : Fin p => (⇑χ)^[(i : ℕ)] (0 : E)))
    (l : E →L[ℝ] ℝ)
    (hl0 : ∀ i : Fin p, l ((⇑χ)^[(i : ℕ)] 0) ≤ l 0)
    (hnc : ∃ i : Fin p, l ((⇑χ)^[(i : ℕ)] 0) < l 0)
    {y : E}
    (hy : y ∈ convexHull ℝ
      (Set.range fun i : Fin p => (⇑χ)^[(i : ℕ)] (0 : E)))
    (hy0 : y ≠ 0) (hly : l y = l 0) :
    ∃ n : E,
      (n = cc + (o.rotation ((2 * π / p : ℝ) : Real.Angle)) ((0 : E) - cc) ∨
       n = cc + (o.rotation ((-(2 * π / p) : ℝ) : Real.Angle)) ((0 : E) - cc)) ∧
      ∃ t : ℝ, 0 < t ∧ y = t • n := by
  classical
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hp0R : (0 : ℝ) < p := by positivity
  have hp0 : 0 < p := by omega
  obtain ⟨θ, hord, hdorb⟩ := rotazione_del_poligono o χ cc hcc hp hclosed hinj
  obtain ⟨m, hmp, hgcd, hθval⟩ := killer_estrazione p hp θ hord
  have hcop : Nat.Coprime m p := hgcd
  -- ══ d₀ ≠ 0 e versore ══
  set d₀ : E := (0 : E) - cc with hd₀def
  have hrot0 : ∀ j : ℕ, (⇑(o.rotation θ))^[j] (0 : E) = 0 := by
    intro j
    induction j with
    | zero => rfl
    | succ nn ih => rw [Function.iterate_succ_apply', ih, map_zero]
  have hd₀ : d₀ ≠ 0 := by
    intro h0
    have hcc0 : cc = 0 := by
      have h1 := congrArg (fun z => z + cc) h0
      simp [hd₀def] at h1
      exact h1.symm
    have hall : ∀ k : ℕ, (⇑χ)^[k] (0 : E) = 0 := by
      intro k
      have h1 := hdorb k
      rw [hcc0, sub_zero, h0, hrot0] at h1
      exact h1
    have h10 : (⟨1, by omega⟩ : Fin p) = ⟨0, by omega⟩ := by
      apply hinj
      show (⇑χ)^[1] (0 : E) = (⇑χ)^[0] 0
      rw [hall 1]
      rfl
    have := congrArg Fin.val h10
    simp at this
  have hr0 : (0 : ℝ) < ‖d₀‖ := norm_pos_iff.mpr hd₀
  set ê : E := ‖d₀‖⁻¹ • d₀ with hêdef
  have hê1 : ‖ê‖ = 1 := by
    rw [hêdef, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (ne_of_gt hr0)]
  have hdk : ∀ k : ℕ, (⇑χ)^[k] (0 : E) - cc
      = ‖d₀‖ • (⇑(o.rotation θ))^[k] ê := by
    intro k
    rw [hdorb k, hêdef, iterate_smul (o.rotation θ), smul_smul,
      mul_inv_cancel₀ (ne_of_gt hr0), one_smul]
  -- ══ Riesz e valori come coseno ══
  haveI hfinE : FiniteDimensional ℝ E :=
    Module.finite_of_finrank_eq_succ
      (show Module.finrank ℝ E = 1 + 1 from Fact.out)
  set g : E := (InnerProductSpace.toDual ℝ E).symm l with hgdef
  have hgspec : ∀ z : E, ⟪g, z⟫ = l z := by
    intro z
    rw [hgdef]
    exact InnerProductSpace.toDual_symm_apply
  have hg0 : g ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := hnc
    have h1 : l ((⇑χ)^[(i : ℕ)] 0) = 0 := by
      rw [← hgspec, h0]; simp
    have h2 : l (0 : E) = 0 := by
      rw [← hgspec, h0]; simp
    rw [h1, h2] at hi
    exact lt_irrefl _ hi
  have hgn : (0 : ℝ) < ‖g‖ := norm_pos_iff.mpr hg0
  set φA : Real.Angle := o.oangle g ê with hφAdef
  have hval : ∀ k : ℕ, l ((⇑χ)^[k] (0 : E))
      = l cc + ‖d₀‖ * (‖g‖ * Real.Angle.cos (φA + k • θ)) := by
    intro k
    have hsplit : (⇑χ)^[k] (0 : E) = cc + ((⇑χ)^[k] (0 : E) - cc) := by
      abel
    calc l ((⇑χ)^[k] (0 : E))
        = l (cc + ((⇑χ)^[k] (0 : E) - cc)) := by rw [← hsplit]
      _ = l cc + l ((⇑χ)^[k] (0 : E) - cc) := by rw [map_add]
      _ = l cc + l (‖d₀‖ • (⇑(o.rotation θ))^[k] ê) := by rw [hdk k]
      _ = l cc + ‖d₀‖ * l ((⇑(o.rotation θ))^[k] ê) := by
          rw [map_smul]; rfl
      _ = l cc + ‖d₀‖ * ⟪g, (⇑(o.rotation θ))^[k] ê⟫ := by rw [hgspec]
      _ = l cc + ‖d₀‖ * (‖g‖ * Real.Angle.cos (φA + k • θ)) := by
          rw [inner_orbita o θ g ê hg0 hê1 k, hφAdef]
  -- ══ posizioni reali ══
  set φr : ℝ := φA.toReal with hφrdef
  have hφAr : φA = (φr : Real.Angle) := (φA.coe_toReal).symm
  have hposizione : ∀ k : ℕ, Real.Angle.cos (φA + k • θ)
      = Real.cos (φr + 2 * π * (((k * m) % p : ℕ) : ℝ) / p) := by
    intro k
    rw [hθval, hφAr, ← Real.Angle.coe_nsmul, ← Real.Angle.coe_add,
      Real.Angle.cos_coe, nsmul_eq_mul]
    have hdm := Nat.div_add_mod (k * m) p
    have hkm : ((k * m : ℕ) : ℝ)
        = (p : ℝ) * (((k * m) / p : ℕ) : ℝ) + (((k * m) % p : ℕ) : ℝ) := by
      exact_mod_cast congrArg (Nat.cast (R := ℝ)) hdm.symm
    have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0R
    have harit : φr + (k : ℝ) * ((m : ℝ) / p * (2 * π))
        = (φr + 2 * π * (((k * m) % p : ℕ) : ℝ) / p)
          + (((k * m) / p : ℕ) : ℝ) * (2 * π) := by
      have h1 : (k : ℝ) * ((m : ℝ) / p * (2 * π))
          = 2 * π * ((k * m : ℕ) : ℝ) / p := by
        push_cast
        ring
      have hsplit : 2 * π * ((p : ℝ) * (((k * m) / p : ℕ) : ℝ)
            + (((k * m) % p : ℕ) : ℝ)) / p
          = (((k * m) / p : ℕ) : ℝ) * (2 * π)
            + 2 * π * (((k * m) % p : ℕ) : ℝ) / p := by
        rw [mul_add, add_div]
        congr 1
        rw [show 2 * π * ((p : ℝ) * (((k * m) / p : ℕ) : ℝ))
            = (p : ℝ) * ((((k * m) / p : ℕ) : ℝ) * (2 * π)) from by ring]
        exact mul_div_cancel_left₀ _ hpne
      rw [h1, hkm, hsplit]
      ring
    rw [harit]
    have hper := Real.cos_add_int_mul_two_pi
      (φr + 2 * π * (((k * m) % p : ℕ) : ℝ) / p) (((k * m) / p : ℕ) : ℤ)
    have hcast : ((((k * m) / p : ℕ) : ℤ) : ℝ) = (((k * m) / p : ℕ) : ℝ) := by
      norm_cast
    rw [hcast] at hper
    exact hper
  -- ══ massimo M e disuguaglianze sui vertici ══
  set M : ℝ := Real.cos φr with hMdef
  have hM0 : Real.Angle.cos (φA + (0 : ℕ) • θ) = M := by
    rw [zero_smul, add_zero, hφAr, Real.Angle.cos_coe]
  have hl0' : l (0 : E) = l cc + ‖d₀‖ * (‖g‖ * M) := by
    have h := hval 0
    rw [hM0] at h
    simpa using h
  have hcos_le : ∀ k : ℕ,
      Real.cos (φr + 2 * π * (((k * m) % p : ℕ) : ℝ) / p) ≤ M := by
    intro k
    have hper : (⇑χ)^[k] (0 : E) = (⇑χ)^[k % p] (0 : E) :=
      iterate_mod (⇑χ) (0 : E) p hclosed k
    have h1 : l ((⇑χ)^[k % p] (0 : E)) ≤ l 0 := hl0 ⟨k % p, Nat.mod_lt _ hp0⟩
    have h2 : l ((⇑χ)^[k] (0 : E)) ≤ l 0 := by rw [hper]; exact h1
    rw [hval k, hposizione k, hl0'] at h2
    have h3 : ‖g‖ * Real.cos (φr + 2 * π * (((k * m) % p : ℕ) : ℝ) / p)
        ≤ ‖g‖ * M :=
      le_of_mul_le_mul_left (by linarith) hr0
    exact le_of_mul_le_mul_left h3 hgn
  -- ══ i testimoni delle posizioni 1 e p−1 (inversi modulari) ══
  haveI : NeZero p := ⟨by omega⟩
  set uu : (ZMod p)ˣ := ZMod.unitOfCoprime m hcop with huu
  have hmu : ((m : ℕ) : ZMod p) = (uu : ZMod p) :=
    (ZMod.coe_unitOfCoprime m hcop).symm
  set kP : ℕ := ((uu⁻¹ : (ZMod p)ˣ) : ZMod p).val with hkP
  have hmodP : (kP * m) % p = 1 % p := by
    have hz : ((kP * m : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      push_cast
      rw [hkP, ZMod.natCast_val, ZMod.cast_id, hmu]
      exact uu.inv_mul
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hz
  have h1p : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  set kM : ℕ := ((-(uu⁻¹) : (ZMod p)ˣ) : ZMod p).val with hkM
  have hmodM : (kM * m) % p = (p - 1) % p := by
    have hz : ((kM * m : ℕ) : ZMod p) = ((p - 1 : ℕ) : ZMod p) := by
      push_cast
      rw [hkM, ZMod.natCast_val, ZMod.cast_id, hmu]
      have hneg : ((-(uu⁻¹) : (ZMod p)ˣ) : ZMod p) * (uu : ZMod p)
          = -1 := by
        rw [Units.val_neg, neg_mul, uu.inv_mul]
      rw [hneg, Nat.cast_sub (by omega : 1 ≤ p), ZMod.natCast_self]
      simp
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hz
  have hpm1 : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
  -- ══ i bordi per L2' ══
  have hb1 : Real.cos (φr + 2 * π / p) ≤ M := by
    have h := hcos_le kP
    rw [hmodP, h1p] at h
    simpa using h
  have hbm : Real.cos (φr - 2 * π / p) ≤ M := by
    have h := hcos_le kM
    rw [hmodM, hpm1] at h
    have hper : φr + 2 * π * (((p - 1 : ℕ) : ℝ)) / p
        = (φr - 2 * π / p) + ((1 : ℤ) : ℝ) * (2 * π) := by
      rw [Nat.cast_sub (by omega : 1 ≤ p)]
      push_cast
      field_simp
      ring
    rw [hper, Real.cos_add_int_mul_two_pi] at h
    exact h
  -- ══ classificazione dei vertici argmax non-zero ══
  have hclass : ∀ k : Fin p, l ((⇑χ)^[(k : ℕ)] 0) = l 0 → (k : ℕ) ≠ 0 →
      ((k : ℕ) * m) % p = 1 ∨ ((k : ℕ) * m) % p = p - 1 := by
    intro k hkeq hk0
    have hcosk : Real.cos (φr + 2 * π * ((((k : ℕ) * m) % p : ℕ) : ℝ) / p)
        = M := by
      have h1 : l cc + ‖d₀‖ * (‖g‖ *
          Real.cos (φr + 2 * π * ((((k : ℕ) * m) % p : ℕ) : ℝ) / p))
          = l cc + ‖d₀‖ * (‖g‖ * M) := by
        rw [← hposizione (k : ℕ), ← hval (k : ℕ), hkeq, hl0']
      have h2 := mul_left_cancel₀ (ne_of_gt hr0) (by linarith :
        ‖d₀‖ * (‖g‖ * Real.cos (φr + 2 * π * ((((k : ℕ) * m) % p : ℕ) : ℝ) / p))
          = ‖d₀‖ * (‖g‖ * M))
      exact mul_left_cancel₀ (ne_of_gt hgn) h2
    have hj0 : ((k : ℕ) * m) % p ≠ 0 := by
      intro h0
      have hdvd : p ∣ (k : ℕ) * m := Nat.dvd_of_mod_eq_zero h0
      have hco : Nat.Coprime p m := Nat.coprime_comm.mp hcop
      have hpk : p ∣ (k : ℕ) := hco.dvd_of_dvd_mul_right hdvd
      exact hk0 (Nat.eq_zero_of_dvd_of_lt hpk k.isLt)
    have hjlt : ((k : ℕ) * m) % p < p := Nat.mod_lt _ hp0
    have hMeq : Real.cos (φr + 2 * π * ((((k : ℕ) * m) % p : ℕ) : ℝ) / p)
        = Real.cos φr := hcosk
    exact argmax_coseno_adiacente p hp φr (by omega) (by omega) hMeq hb1 hbm
  -- ══ L3: y sta nell'hull dei vertici argmax ══
  set s : Finset E :=
    Finset.image (fun i : Fin p => (⇑χ)^[(i : ℕ)] 0) Finset.univ with hsdef
  have hscoe : (s : Set E)
      = Set.range fun i : Fin p => (⇑χ)^[(i : ℕ)] (0 : E) := by
    rw [hsdef, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hy' : y ∈ convexHull ℝ (s : Set E) := by
    rw [hscoe]; exact hy
  have hhull_le : ∀ w ∈ convexHull ℝ (s : Set E), l w ≤ l 0 := by
    intro w hw
    have hsub : (s : Set E) ⊆ {z : E | l z ≤ l 0} := by
      intro z hz
      rw [hscoe] at hz
      obtain ⟨i, rfl⟩ := hz
      exact hl0 i
    have hconv : Convex ℝ {z : E | l z ≤ l (0 : E)} :=
      convex_halfSpace_le (LinearMap.isLinear l.toLinearMap) (l 0)
    exact convexHull_min hsub hconv hw
  have hL3 := faccia_argmax s l hy'
    (fun w hw => by rw [hly]; exact hhull_le w hw)
  -- ══ il vertice argmax non-zero esiste ══
  have hexn : ∃ k₁ : Fin p, (k₁ : ℕ) ≠ 0 ∧
      l ((⇑χ)^[(k₁ : ℕ)] 0) = l y ∧ (⇑χ)^[(k₁ : ℕ)] (0 : E) ≠ 0 := by
    by_contra hno
    push_neg at hno
    have hsub1 : {x ∈ (s : Set E) | l x = l y} ⊆ {(0 : E)} := by
      rintro z ⟨hzs, hzl⟩
      rw [hscoe] at hzs
      obtain ⟨i, rfl⟩ := hzs
      by_cases hi0 : (i : ℕ) = 0
      · have h1 : (⇑χ)^[(i : ℕ)] (0 : E) = 0 := by rw [hi0]; rfl
        show (fun i : Fin p => (⇑χ)^[(i : ℕ)] (0 : E)) i ∈ ({0} : Set E)
        simp [h1]
      · have h1 := hno i hi0 hzl
        show (fun i : Fin p => (⇑χ)^[(i : ℕ)] (0 : E)) i ∈ ({0} : Set E)
        simp [h1]
    have := convexHull_mono hsub1 hL3
    rw [convexHull_singleton] at this
    exact hy0 this
  obtain ⟨k₁, hk₁0, hk₁l, hk₁ne⟩ := hexn
  set n : E := (⇑χ)^[(k₁ : ℕ)] (0 : E) with hndef
  -- ══ unicità del vertice argmax non-zero ══
  have hpos_inj : ∀ k k' : Fin p,
      ((k : ℕ) * m) % p = ((k' : ℕ) * m) % p → k = k' := by
    intro k k' hkk
    have hz : (((k : ℕ) * m : ℕ) : ZMod p) = (((k' : ℕ) * m : ℕ) : ZMod p) := by
      rw [ZMod.natCast_eq_natCast_iff']
      exact hkk
    push_cast at hz
    rw [hmu] at hz
    have hz2 : ((k : ℕ) : ZMod p) = ((k' : ℕ) : ZMod p) := by
      have := congrArg (fun z => z * ((uu⁻¹ : (ZMod p)ˣ) : ZMod p)) hz
      simpa [mul_assoc, uu.mul_inv] using this
    apply Fin.ext
    have h1 : ((k : ℕ)) % p = ((k' : ℕ)) % p := by
      rwa [ZMod.natCast_eq_natCast_iff'] at hz2
    rwa [Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt k'.isLt] at h1
  have huniq : ∀ k : Fin p, (k : ℕ) ≠ 0 →
      l ((⇑χ)^[(k : ℕ)] 0) = l 0 → (⇑χ)^[(k : ℕ)] (0 : E) = n := by
    intro k hk0 hkl
    by_cases hkk : k = k₁
    · rw [hkk, hndef]
    · exfalso
      have hj := hclass k hkl hk0
      have hj₁ := hclass k₁ (by rw [hk₁l, hly]) hk₁0
      have hne : ((k : ℕ) * m) % p ≠ ((k₁ : ℕ) * m) % p := by
        intro h
        exact hkk (hpos_inj k k₁ h)
      -- posizioni distinte in {1, p−1} ⟹ entrambi i bordi pareggiano
      have hbordi : Real.cos (φr + 2 * π / p) = M ∧
          Real.cos (φr - 2 * π / p) = M := by
        have hval1 : ∀ kk : Fin p, ((kk : ℕ) * m) % p = 1 →
            l ((⇑χ)^[(kk : ℕ)] 0) = l 0 →
            Real.cos (φr + 2 * π / p) = M := by
          intro kk hpos1 hkkl
          have h1 : l cc + ‖d₀‖ * (‖g‖ *
              Real.cos (φr + 2 * π * ((((kk : ℕ) * m) % p : ℕ) : ℝ) / p))
              = l cc + ‖d₀‖ * (‖g‖ * M) := by
            rw [← hposizione (kk : ℕ), ← hval (kk : ℕ), hkkl, hl0']
          have h2 := mul_left_cancel₀ (ne_of_gt hr0) (by linarith :
            ‖d₀‖ * (‖g‖ * Real.cos (φr + 2 * π * ((((kk : ℕ) * m) % p : ℕ) : ℝ) / p))
              = ‖d₀‖ * (‖g‖ * M))
          have h3 := mul_left_cancel₀ (ne_of_gt hgn) h2
          rw [hpos1] at h3
          simpa using h3
        have hvalm : ∀ kk : Fin p, ((kk : ℕ) * m) % p = p - 1 →
            l ((⇑χ)^[(kk : ℕ)] 0) = l 0 →
            Real.cos (φr - 2 * π / p) = M := by
          intro kk hpos1 hkkl
          have h1 : l cc + ‖d₀‖ * (‖g‖ *
              Real.cos (φr + 2 * π * ((((kk : ℕ) * m) % p : ℕ) : ℝ) / p))
              = l cc + ‖d₀‖ * (‖g‖ * M) := by
            rw [← hposizione (kk : ℕ), ← hval (kk : ℕ), hkkl, hl0']
          have h2 := mul_left_cancel₀ (ne_of_gt hr0) (by linarith :
            ‖d₀‖ * (‖g‖ * Real.cos (φr + 2 * π * ((((kk : ℕ) * m) % p : ℕ) : ℝ) / p))
              = ‖d₀‖ * (‖g‖ * M))
          have h3 := mul_left_cancel₀ (ne_of_gt hgn) h2
          rw [hpos1] at h3
          have hper : φr + 2 * π * (((p - 1 : ℕ) : ℝ)) / p
              = (φr - 2 * π / p) + ((1 : ℤ) : ℝ) * (2 * π) := by
            rw [Nat.cast_sub (by omega : 1 ≤ p)]
            push_cast
            field_simp
            ring
          rw [hper, Real.cos_add_int_mul_two_pi] at h3
          exact h3
        rcases hj with h1 | h1 <;> rcases hj₁ with h2 | h2
        · exact absurd (h1.trans h2.symm) hne
        · exact ⟨hval1 k h1 hkl, hvalm k₁ h2 (by rw [hk₁l, hly])⟩
        · exact ⟨hval1 k₁ h2 (by rw [hk₁l, hly]), hvalm k h1 hkl⟩
        · exact absurd (h1.trans h2.symm) hne
      have hb0' : (0 : ℝ) < 2 * π / p := by positivity
      have hbπ' : 2 * π / p < π := by
        rw [div_lt_iff₀ hp0R]
        have : (3 : ℝ) ≤ p := by exact_mod_cast hp
        nlinarith
      exact non_doppio_pareggio hb0' hbπ' hbordi.1 hbordi.2
  -- ══ y sul segmento [0, n] ══
  have hsub2 : {x ∈ (s : Set E) | l x = l y} ⊆ ({(0 : E), n} : Set E) := by
    rintro z ⟨hzs, hzl⟩
    rw [hscoe] at hzs
    obtain ⟨i, rfl⟩ := hzs
    by_cases hi0 : (i : ℕ) = 0
    · left
      show (⇑χ)^[(i : ℕ)] (0 : E) = 0
      rw [hi0]
      rfl
    · right
      show (⇑χ)^[(i : ℕ)] (0 : E) = n
      exact huniq i hi0 (by rw [hzl, hly])
  have hy2 : y ∈ convexHull ℝ ({(0 : E), n} : Set E) :=
    convexHull_mono hsub2 hL3
  rw [convexHull_pair] at hy2
  rw [segment_eq_image'] at hy2
  obtain ⟨t, ⟨ht0, ht1⟩, hty⟩ := hy2
  have hyn : y = t • n := by
    rw [← hty]
    simp
  have ht0' : (0 : ℝ) < t := by
    rcases lt_or_eq_of_le ht0 with h | h
    · exact h
    · exfalso
      apply hy0
      rw [hyn, ← h, zero_smul]
  -- ══ la posizione di n ══
  have hj₁ := hclass k₁ (by rw [hk₁l, hly]) hk₁0
  have hnrot : n = cc + (⇑(o.rotation θ))^[(k₁ : ℕ)] d₀ := by
    rw [hndef]
    have := hdorb (k₁ : ℕ)
    have h2 : (⇑χ)^[(k₁ : ℕ)] (0 : E)
        = ((⇑χ)^[(k₁ : ℕ)] (0 : E) - cc) + cc := by abel
    rw [h2, this]
    abel
  have hrotk : (⇑(o.rotation θ))^[(k₁ : ℕ)] d₀
      = o.rotation (((k₁ : ℕ) : ℕ) • θ) d₀ := rotation_iterate o θ d₀ (k₁ : ℕ)
  refine ⟨n, ?_, t, ht0', hyn⟩
  have hdm := Nat.div_add_mod ((k₁ : ℕ) * m) p
  have hkm : (((k₁ : ℕ) * m : ℕ) : ℝ)
      = (p : ℝ) * ((((k₁ : ℕ) * m) / p : ℕ) : ℝ)
        + ((((k₁ : ℕ) * m) % p : ℕ) : ℝ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℝ)) hdm.symm
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0R
  rcases hj₁ with hjpos | hjpos
  · left
    have hkm1 : (((k₁ : ℕ) * m : ℕ) : ℝ)
        = (p : ℝ) * ((((k₁ : ℕ) * m) / p : ℕ) : ℝ) + 1 := by
      rw [hkm, hjpos]
      norm_num
    have hang : (k₁ : ℕ) • θ = ((2 * π / p : ℝ) : Real.Angle) := by
      rw [hθval, ← Real.Angle.coe_nsmul, nsmul_eq_mul,
        Real.Angle.angle_eq_iff_two_pi_dvd_sub]
      refine ⟨(((k₁ : ℕ) * m) / p : ℕ), ?_⟩
      have hlhs : ((k₁ : ℕ) : ℝ) * ((m : ℝ) / p * (2 * π)) - 2 * π / p
          = ((((k₁ : ℕ) * m : ℕ) : ℝ) - 1) * (2 * π) / p := by
        push_cast
        ring
      rw [hlhs, hkm1]
      rw [show (((((k₁ : ℕ) * m) / p : ℕ) : ℤ) : ℝ)
          = ((((k₁ : ℕ) * m) / p : ℕ) : ℝ) from by norm_cast]
      field_simp
      ring
    rw [hnrot, hrotk, hang]
  · right
    have hkm1 : (((k₁ : ℕ) * m : ℕ) : ℝ)
        = (p : ℝ) * ((((k₁ : ℕ) * m) / p : ℕ) : ℝ) + ((p : ℝ) - 1) := by
      rw [hkm, hjpos, Nat.cast_sub (by omega : 1 ≤ p)]
      norm_num
    have hang : (k₁ : ℕ) • θ = ((-(2 * π / p) : ℝ) : Real.Angle) := by
      rw [hθval, ← Real.Angle.coe_nsmul, nsmul_eq_mul,
        Real.Angle.angle_eq_iff_two_pi_dvd_sub]
      refine ⟨(((k₁ : ℕ) * m) / p : ℕ) + 1, ?_⟩
      have hlhs : ((k₁ : ℕ) : ℝ) * ((m : ℝ) / p * (2 * π)) - (-(2 * π / p))
          = ((((k₁ : ℕ) * m : ℕ) : ℝ) + 1) * (2 * π) / p := by
        push_cast
        ring
      rw [hlhs, hkm1]
      rw [show ((((((k₁ : ℕ) * m) / p : ℕ) : ℕ) + 1 : ℤ) : ℝ)
          = ((((k₁ : ℕ) * m) / p : ℕ) : ℝ) + 1 from by norm_cast]
      field_simp
      ring
    rw [hnrot, hrotk, hang]

end PlatoniciA14
