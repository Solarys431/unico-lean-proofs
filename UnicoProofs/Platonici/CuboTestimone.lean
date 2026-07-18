import Mathlib
import UnicoProofs.Platonici.Fondamenta
import UnicoProofs.Platonici.TetraedroStadio2
import UnicoProofs.Platonici.FacciaArgmax
import UnicoProofs.Platonici.Trasferimento

/-!
FASE 1B, N2 — IL CUBO, sviluppo import-based (stadio 1 portato + faccia
regolare). Le simmetrie sono permutazioni di coordinate con segni; la faccia
{x = 1} è esposta dal proiettore della prima coordinata, e l'argmax si
schiaccia sui 4 vertici della faccia via `faccia_argmax` (L3, certificato).
-/

open Real Set Metric FiniteConvexPolytope PlatoniciL3
open scoped RealInnerProductSpace

noncomputable section

/-! ## I vertici e il politopo (stadio 1, portato) -/

def c0 : E3 := WithLp.toLp 2 ![1, 1, 1]
def c1 : E3 := WithLp.toLp 2 ![1, 1, -1]
def c2 : E3 := WithLp.toLp 2 ![1, -1, 1]
def c3 : E3 := WithLp.toLp 2 ![1, -1, -1]
def c4 : E3 := WithLp.toLp 2 ![-1, 1, 1]
def c5 : E3 := WithLp.toLp 2 ![-1, 1, -1]
def c6 : E3 := WithLp.toLp 2 ![-1, -1, 1]
def c7 : E3 := WithLp.toLp 2 ![-1, -1, -1]

open Classical in
def verticiCubo : Finset E3 := {c0, c1, c2, c3, c4, c5, c6, c7}

theorem mem_verticiCubo_iff {v : E3} : v ∈ verticiCubo ↔
    v = c0 ∨ v = c1 ∨ v = c2 ∨ v = c3 ∨ v = c4 ∨ v = c5 ∨ v = c6 ∨ v = c7 := by
  simp [verticiCubo]

theorem norm_vertici_cubo : ∀ v ∈ verticiCubo, ‖v‖ = Real.sqrt 3 := by
  intro v hv
  rcases mem_verticiCubo_iff.mp hv with h | h | h | h | h | h | h | h <;> subst h
  · show ‖(WithLp.toLp 2 ![(1:ℝ), 1, 1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(1:ℝ), 1, -1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(1:ℝ), -1, 1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(1:ℝ), -1, -1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(-1:ℝ), 1, 1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(-1:ℝ), 1, -1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(-1:ℝ), -1, 1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(-1:ℝ), -1, -1] : E3)‖ = _
    rw [norma_toLp]; norm_num

/-- IL TESTIMONE (stadio 1): il cubo è un politopo convesso finito legittimo. -/
def cubo : FiniteConvexPolytope E3 where
  vertices := verticiCubo
  nonempty := ⟨c0, by simp [verticiCubo]⟩
  vertices_eq_extremePoints := by
    have hV : (verticiCubo : Set E3) ⊆ Metric.sphere 0 (Real.sqrt 3) := by
      intro v hv
      rw [mem_sphere_zero_iff_norm]
      exact norm_vertici_cubo v (by exact_mod_cast hv)
    exact (cosferico_extremePoints 0 (Real.sqrt 3) _ hV).symm

/-! ## La rotazione della faccia {x = 1} -/

def scambioYZ : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 1 2)

def segnoY : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.refl ℝ ℝ, LinearIsometryEquiv.neg ℝ,
      LinearIsometryEquiv.refl ℝ ℝ]

/-- La rotazione di π/2 attorno all'asse x: (x, y, z) ↦ (x, −z, y). -/
def rotFacciaX : E3 ≃ₗᵢ[ℝ] E3 := scambioYZ.trans segnoY

theorem rotX_c0 : rotFacciaX c0 = c2 := by
  ext j <;> fin_cases j <;>
    simp [rotFacciaX, scambioYZ, segnoY, c0, c2, Equiv.swap_apply_def,
      LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.piLpCongrRight]

theorem rotX_c2 : rotFacciaX c2 = c3 := by
  ext j <;> fin_cases j <;>
    simp [rotFacciaX, scambioYZ, segnoY, c2, c3, Equiv.swap_apply_def,
      LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.piLpCongrRight]

theorem rotX_c3 : rotFacciaX c3 = c1 := by
  ext j <;> fin_cases j <;>
    simp [rotFacciaX, scambioYZ, segnoY, c3, c1, Equiv.swap_apply_def,
      LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.piLpCongrRight]

theorem rotX_c1 : rotFacciaX c1 = c0 := by
  ext j <;> fin_cases j <;>
    simp [rotFacciaX, scambioYZ, segnoY, c1, c0, Equiv.swap_apply_def,
      LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.piLpCongrRight]

/-- La versione affine della rotazione. -/
def rotAffX : E3 ≃ᵃⁱ[ℝ] E3 := rotFacciaX.toAffineIsometryEquiv

theorem rotAffX_apply (z : E3) : rotAffX z = rotFacciaX z := rfl

/-! ## La faccia {x = 1} e il suo ciclo -/

open Classical in
def facciaX1 : Finset E3 := {c0, c2, c3, c1}

def F₀ : Set E3 := convexHull ℝ (facciaX1 : Set E3)

/-- Le coordinate distinguono i vertici del ciclo. -/
theorem c0_ne_c2 : c0 ≠ c2 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 1) h
  simp [c0, c2] at this
  norm_num at this

theorem c0_ne_c3 : c0 ≠ c3 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 1) h
  simp [c0, c3] at this
  norm_num at this

theorem c0_ne_c1 : c0 ≠ c1 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 2) h
  simp [c0, c1] at this
  norm_num at this

theorem c2_ne_c3 : c2 ≠ c3 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 2) h
  simp [c2, c3] at this
  norm_num at this

theorem c2_ne_c1 : c2 ≠ c1 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 1) h
  simp [c2, c1] at this
  norm_num at this

theorem c3_ne_c1 : c3 ≠ c1 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 1) h
  simp [c3, c1] at this
  norm_num at this

/-- L'orbita di c0 sotto la rotazione: i quattro vertici della faccia in
ordine ciclico c0 → c2 → c3 → c1. -/
theorem orbita_rotX : ∀ i : Fin 4, (⇑rotAffX)^[(i : ℕ)] c0
    = ![c0, c2, c3, c1] i := by
  intro i
  fin_cases i
  · rfl
  · show rotAffX c0 = c2
    rw [rotAffX_apply, rotX_c0]
  · show rotAffX (rotAffX c0) = c3
    rw [rotAffX_apply, rotAffX_apply, rotX_c0, rotX_c2]
  · show rotAffX (rotAffX (rotAffX c0)) = c1
    rw [rotAffX_apply, rotAffX_apply, rotAffX_apply, rotX_c0, rotX_c2, rotX_c3]

theorem ciclo_chiuso : (⇑rotAffX)^[4] c0 = c0 := by
  show rotAffX ((⇑rotAffX)^[3] c0) = c0
  have h3 := orbita_rotX 3
  simp only [show ((3 : Fin 4) : ℕ) = 3 from rfl] at h3
  rw [h3]
  show rotAffX c1 = c0
  rw [rotAffX_apply, rotX_c1]

theorem ciclo_iniettivo : Function.Injective
    (fun i : Fin 4 => (⇑rotAffX)^[(i : ℕ)] c0) := by
  intro i j hij
  have hij' : (⇑rotAffX)^[(i : ℕ)] c0 = (⇑rotAffX)^[(j : ℕ)] c0 := hij
  rw [orbita_rotX i, orbita_rotX j] at hij'
  clear hij
  rename' hij' => hij
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (exfalso; revert hij; simp only []
       first
         | exact fun h => c0_ne_c2 h
         | exact fun h => c0_ne_c3 h
         | exact fun h => c0_ne_c1 h
         | exact fun h => c2_ne_c3 h
         | exact fun h => c2_ne_c1 h
         | exact fun h => c3_ne_c1 h
         | exact fun h => c0_ne_c2 h.symm
         | exact fun h => c0_ne_c3 h.symm
         | exact fun h => c0_ne_c1 h.symm
         | exact fun h => c2_ne_c3 h.symm
         | exact fun h => c2_ne_c1 h.symm
         | exact fun h => c3_ne_c1 h.symm)

theorem range_orbita : Set.range (fun i : Fin 4 => (⇑rotAffX)^[(i : ℕ)] c0)
    = (facciaX1 : Set E3) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    show (⇑rotAffX)^[(i : ℕ)] c0 ∈ (facciaX1 : Set E3)
    rw [orbita_rotX i]
    fin_cases i <;> simp [facciaX1]
  · intro hz
    have hcasi : z = c0 ∨ z = c2 ∨ z = c3 ∨ z = c1 := by
      simpa [facciaX1] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨0, by
        show (⇑rotAffX)^[((0 : Fin 4) : ℕ)] c0 = c0
        rw [orbita_rotX 0]
        rfl⟩
    · exact ⟨1, by
        show (⇑rotAffX)^[((1 : Fin 4) : ℕ)] c0 = c2
        rw [orbita_rotX 1]
        rfl⟩
    · exact ⟨2, by
        show (⇑rotAffX)^[((2 : Fin 4) : ℕ)] c0 = c3
        rw [orbita_rotX 2]
        rfl⟩
    · exact ⟨3, by
        show (⇑rotAffX)^[((3 : Fin 4) : ℕ)] c0 = c1
        rw [orbita_rotX 3]
        rfl⟩

/-- Il lato della faccia: dist c0 c2 = 2. -/
theorem lato_cubo : dist c0 (rotAffX c0) = 2 := by
  rw [rotAffX_apply, rotX_c0]
  rw [dist_eq_norm]
  have hsub : c0 - c2 = WithLp.toLp 2 ![0, 2, 0] := by
    ext j <;> fin_cases j <;> simp [c0, c2] <;> norm_num
  rw [hsub, norma_toLp]
  rw [show (0:ℝ)^2 + 2^2 + 0^2 = 4 by norm_num]
  rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

/-! ## L'esposizione della faccia {x = 1} e la regolarità -/

/-- Il proiettore della prima coordinata. -/
def lX : E3 →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 3)

theorem lX_toLp (a b c : ℝ) : lX (WithLp.toLp 2 ![a, b, c]) = a := rfl

theorem lX_vertici : lX c0 = 1 ∧ lX c1 = 1 ∧ lX c2 = 1 ∧ lX c3 = 1 ∧
    lX c4 = -1 ∧ lX c5 = -1 ∧ lX c6 = -1 ∧ lX c7 = -1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- I vertici con lX = 1 sono esattamente quelli della faccia. -/
theorem argmax_verticiX : {x ∈ (verticiCubo : Set E3) | lX x = 1}
    = (facciaX1 : Set E3) := by
  ext z
  constructor
  · rintro ⟨hz, hlz⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · simp [facciaX1]
    · simp [facciaX1]
    · simp [facciaX1]
    · simp [facciaX1]
    · exfalso; rw [lX_vertici.2.2.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lX_vertici.2.2.2.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lX_vertici.2.2.2.2.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lX_vertici.2.2.2.2.2.2.2] at hlz; norm_num at hlz
  · intro hz
    have hcasi : z = c0 ∨ z = c2 ∨ z = c3 ∨ z = c1 := by
      simpa [facciaX1] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨by simp [verticiCubo], lX_vertici.1⟩
    · exact ⟨by simp [verticiCubo], lX_vertici.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lX_vertici.2.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lX_vertici.2.1⟩

/-- Il corpo del cubo sta nel semispazio lX ≤ 1. -/
theorem toSet_le_uno : ∀ z ∈ cubo.toSet, lX z ≤ 1 := by
  intro z hz
  have hsub : (verticiCubo : Set E3) ⊆ {w : E3 | lX w ≤ 1} := by
    intro w hw
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
      h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq] <;>
      first
        | (rw [lX_vertici.1])
        | (rw [lX_vertici.2.1])
        | (rw [lX_vertici.2.2.1])
        | (rw [lX_vertici.2.2.2.1])
        | (rw [lX_vertici.2.2.2.2.1]; norm_num)
        | (rw [lX_vertici.2.2.2.2.2.1]; norm_num)
        | (rw [lX_vertici.2.2.2.2.2.2.1]; norm_num)
        | (rw [lX_vertici.2.2.2.2.2.2.2]; norm_num)
  have hcx : Convex ℝ {w : E3 | lX w ≤ 1} :=
    convex_halfSpace_le (LinearMap.isLinear lX.toLinearMap) 1
  exact convexHull_min hsub hcx hz

/-- La faccia sta nel semispazio lX ≥ 1 (dunque lX = 1 su F₀). -/
theorem F₀_ge_uno : ∀ z ∈ F₀, 1 ≤ lX z := by
  intro z hz
  have hsub : (facciaX1 : Set E3) ⊆ {w : E3 | 1 ≤ lX w} := by
    intro w hw
    have hcasi : w = c0 ∨ w = c2 ∨ w = c3 ∨ w = c1 := by
      simpa [facciaX1] using hw
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq]
    · rw [lX_vertici.1]
    · rw [lX_vertici.2.2.1]
    · rw [lX_vertici.2.2.2.1]
    · rw [lX_vertici.2.1]
  have hcx : Convex ℝ {w : E3 | 1 ≤ lX w} :=
    convex_halfSpace_ge (LinearMap.isLinear lX.toLinearMap) 1
  exact convexHull_min hsub hcx hz

theorem F₀_sub_toSet : F₀ ⊆ cubo.toSet := by
  apply convexHull_mono
  intro z hz
  have hcasi : z = c0 ∨ z = c2 ∨ z = c3 ∨ z = c1 := by
    simpa [facciaX1] using hz
  rcases hcasi with h | h | h | h <;> subst h <;> simp [cubo, verticiCubo]

/-- L'ESPOSIZIONE: F₀ è la faccia di massimo di lX sul cubo. -/
theorem facciaX1_esposta : IsExposed ℝ cubo.toSet F₀ := by
  intro _
  refine ⟨lX, ?_⟩
  ext z
  constructor
  · intro hz
    have hz1 : lX z = 1 := le_antisymm
      (toSet_le_uno z (F₀_sub_toSet hz)) (F₀_ge_uno z hz)
    refine ⟨F₀_sub_toSet hz, ?_⟩
    intro y hy
    rw [hz1]
    exact toSet_le_uno y hy
  · rintro ⟨hzS, hzmax⟩
    have hc0S : c0 ∈ cubo.toSet := by
      apply subset_convexHull
      simp [cubo, verticiCubo]
    have hz1 : lX z = 1 := by
      have h1 : lX c0 ≤ lX z := hzmax c0 hc0S
      rw [lX_vertici.1] at h1
      exact le_antisymm (toSet_le_uno z hzS) h1
    have hL3 := faccia_argmax verticiCubo lX hzS
      (fun w hw => hzmax w hw)
    have hset : {x ∈ (verticiCubo : Set E3) | lX x = lX z}
        = (facciaX1 : Set E3) := by
      rw [hz1]
      exact argmax_verticiX
    rw [hset] at hL3
    exact hL3

/-- La rotazione preserva la faccia (a livello di hull). -/
theorem rotAffX_preserva_F₀ : (⇑rotAffX) '' F₀ = F₀ := by
  show (⇑rotAffX) '' (convexHull ℝ (facciaX1 : Set E3)) = _
  have haff : (⇑rotAffX) '' (convexHull ℝ (facciaX1 : Set E3))
      = convexHull ℝ ((⇑rotAffX) '' (facciaX1 : Set E3)) :=
    AffineMap.image_convexHull rotAffX.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hcasi : y = c0 ∨ y = c2 ∨ y = c3 ∨ y = c1 := by
      simpa [facciaX1] using hy
    rcases hcasi with h | h | h | h <;> subst h <;>
      rw [rotAffX_apply] <;>
      first
        | (rw [rotX_c0]; simp [facciaX1])
        | (rw [rotX_c2]; simp [facciaX1])
        | (rw [rotX_c3]; simp [facciaX1])
        | (rw [rotX_c1]; simp [facciaX1])
  · intro hz
    have hcasi : z = c0 ∨ z = c2 ∨ z = c3 ∨ z = c1 := by
      simpa [facciaX1] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨c1, by simp [facciaX1], by rw [rotAffX_apply, rotX_c1]⟩
    · exact ⟨c0, by simp [facciaX1], by rw [rotAffX_apply, rotX_c0]⟩
    · exact ⟨c2, by simp [facciaX1], by rw [rotAffX_apply, rotX_c2]⟩
    · exact ⟨c3, by simp [facciaX1], by rw [rotAffX_apply, rotX_c3]⟩

/-! ## Lo span bidimensionale e la faccetta regolare -/

/-- lX vale 1 su tutta la faccia (dalla caratterizzazione argmax). -/
theorem lX_su_faccia : ∀ u ∈ (facciaX1 : Set E3), lX u = 1 := by
  intro u hu
  rw [← argmax_verticiX] at hu
  exact hu.2

/-- Le differenze della faccia stanno nel nucleo di lX. -/
theorem span_le_ker : vectorSpan ℝ (facciaX1 : Set E3)
    ≤ LinearMap.ker lX.toLinearMap := by
  show Submodule.span ℝ ((facciaX1 : Set E3) -ᵥ (facciaX1 : Set E3)) ≤ _
  rw [Submodule.span_le]
  rintro d ⟨u, hu, v, hv, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  show lX (u -ᵥ v) = 0
  rw [vsub_eq_sub, map_sub, lX_su_faccia u hu, lX_su_faccia v hv, sub_self]

/-- Il nucleo di lX ha dimensione 2 (rango-nullità: lX è suriettivo). -/
theorem finrank_ker_lX :
    Module.finrank ℝ (LinearMap.ker lX.toLinearMap) = 2 := by
  have hsurj : Function.Surjective lX.toLinearMap := by
    intro t
    refine ⟨t • c0, ?_⟩
    rw [map_smul]
    show t • lX c0 = t
    rw [lX_vertici.1, smul_eq_mul, mul_one]
  have hrn := LinearMap.finrank_range_add_finrank_ker lX.toLinearMap
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrn
  have hE3 : Module.finrank ℝ E3 = 3 := by
    simp [E3, finrank_euclideanSpace_fin]
  rw [hE3] at hrn
  have hR : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ
  omega

/-- I due lati uscenti da c0. -/
noncomputable def d1 : E3 := c0 - c2
noncomputable def d2 : E3 := c0 - c1

theorem indep_d : LinearIndependent ℝ ![d1, d2] := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have := congrArg (fun v : E3 => (WithLp.ofLp v) 2) h
    simp [d2, c0, c1] at this
  · intro a h
    have := congrArg (fun v : E3 => (WithLp.ofLp v) 1) h
    simp [d1, d2, c0, c1, c2] at this
    norm_num at this

/-- Lo span direzionale della faccia è esattamente 2-dimensionale. -/
theorem finrank_span_faccia :
    Module.finrank ℝ (vectorSpan ℝ (facciaX1 : Set E3)) = 2 := by
  refine le_antisymm ?_ ?_
  · calc Module.finrank ℝ (vectorSpan ℝ (facciaX1 : Set E3))
        ≤ Module.finrank ℝ (LinearMap.ker lX.toLinearMap) :=
          Submodule.finrank_mono span_le_ker
      _ = 2 := finrank_ker_lX
  · have hsub : Submodule.span ℝ (Set.range ![d1, d2])
        ≤ vectorSpan ℝ (facciaX1 : Set E3) := by
      rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      fin_cases i
      · have hm := vsub_mem_vectorSpan ℝ
          (show c0 ∈ (facciaX1 : Set E3) by simp [facciaX1])
          (show c2 ∈ (facciaX1 : Set E3) by simp [facciaX1])
        simpa [d1, vsub_eq_sub] using hm
      · have hm := vsub_mem_vectorSpan ℝ
          (show c0 ∈ (facciaX1 : Set E3) by simp [facciaX1])
          (show c1 ∈ (facciaX1 : Set E3) by simp [facciaX1])
        simpa [d2, vsub_eq_sub] using hm
    have h2 : Module.finrank ℝ (Submodule.span ℝ (Set.range ![d1, d2])) = 2 := by
      rw [finrank_span_eq_card indep_d]
      simp
    calc (2 : ℕ) = Module.finrank ℝ (Submodule.span ℝ (Set.range ![d1, d2])) :=
          h2.symm
      _ ≤ Module.finrank ℝ (vectorSpan ℝ (facciaX1 : Set E3)) :=
          Submodule.finrank_mono hsub

/-- Lo span di F₀ coincide con quello dei vertici della faccia. -/
theorem span_F₀ : vectorSpan ℝ F₀ = vectorSpan ℝ (facciaX1 : Set E3) := by
  show vectorSpan ℝ (convexHull ℝ (facciaX1 : Set E3)) = _
  rw [← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]

theorem F₀_nonempty : F₀.Nonempty :=
  ⟨c0, subset_convexHull ℝ _ (by simp [facciaX1])⟩

theorem c0_mem_F₀ : c0 ∈ F₀ :=
  subset_convexHull ℝ _ (by simp [facciaX1])

/-- F₀ è una faccetta del cubo. -/
theorem facciaX1_isFacet : cubo.IsFacet F₀ :=
  ⟨⟨facciaX1_esposta, F₀_nonempty⟩, by rw [span_F₀]; exact finrank_span_faccia⟩

theorem F₀_eq_hull_orbita : F₀ = convexHull ℝ
    (Set.range fun i : Fin 4 => (⇑rotAffX)^[(i : ℕ)] c0) := by
  rw [range_orbita]
  rfl

/-- LA FACCETTA REGOLARE: il quadrato {x=1} è 4-gonale regolare di lato 2. -/
theorem facciaX1_regolare : cubo.IsRegularFacet F₀ 4 2 :=
  ⟨facciaX1_isFacet, by norm_num, by norm_num,
    rotAffX, c0, c0_mem_F₀, rotAffX_preserva_F₀, ciclo_iniettivo,
    ciclo_chiuso, F₀_eq_hull_orbita, lato_cubo⟩


/-! ## La dimensione globale del cubo e il lemma dei vertici esposti -/

/-- I vertici del cubo generano tutto lo spazio: span direzionale 3D. -/
theorem cubo_finrank :
    Module.finrank ℝ (vectorSpan ℝ (cubo.vertices : Set E3)) = 3 := by
  have hc0 : c0 ∈ (cubo.vertices : Set E3) := by simp [cubo, verticiCubo]
  have hc1 : c1 ∈ (cubo.vertices : Set E3) := by simp [cubo, verticiCubo]
  have hc2 : c2 ∈ (cubo.vertices : Set E3) := by simp [cubo, verticiCubo]
  have hc4 : c4 ∈ (cubo.vertices : Set E3) := by simp [cubo, verticiCubo]
  have htop : vectorSpan ℝ (cubo.vertices : Set E3) = ⊤ := by
    apply le_antisymm le_top
    rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.span_eq, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    all_goals simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      SetLike.mem_coe]
    · show EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
        ∈ vectorSpan ℝ (cubo.vertices : Set E3)
      have hd : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
          = (2⁻¹ : ℝ) • (c0 -ᵥ c4) := by
        ext j <;> fin_cases j <;>
          simp [c0, c4, EuclideanSpace.single_apply] <;> norm_num
      rw [hd]
      exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ hc0 hc4)
    · show EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
        ∈ vectorSpan ℝ (cubo.vertices : Set E3)
      have hd : (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
          = (2⁻¹ : ℝ) • (c0 -ᵥ c2) := by
        ext j <;> fin_cases j <;>
          simp [c0, c2, EuclideanSpace.single_apply] <;> norm_num
      rw [hd]
      exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ hc0 hc2)
    · show EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
        ∈ vectorSpan ℝ (cubo.vertices : Set E3)
      have hd : (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
          = (2⁻¹ : ℝ) • (c0 -ᵥ c1) := by
        ext j <;> fin_cases j <;>
          simp [c0, c1, EuclideanSpace.single_apply] <;> norm_num
      rw [hd]
      exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ hc0 hc1)
  rw [htop, finrank_top]
  simp [E3]

open Classical in
/-- Ogni faccia esposta del cubo è l'hull dei vertici che contiene
(il pattern del tetraedro, parola per parola). -/
theorem exposedFace_eq_convexHull_vertices_cubo {F : Set E3}
    (hF : cubo.IsFace F) :
    F = convexHull ℝ ((cubo.vertices.filter (· ∈ F) : Finset E3) : Set E3) := by
  classical
  let S : Finset E3 := cubo.vertices.filter (· ∈ F)
  have hPcompact : IsCompact cubo.toSet :=
    (cubo.vertices.finite_toSet.isCompact_convexHull ℝ)
  have hFcompact : IsCompact F := hF.1.isCompact hPcompact
  have hFconvex : Convex ℝ F := hF.1.convex (convex_convexHull ℝ _)
  have hKM := closure_convexHull_extremePoints hFcompact hFconvex
  have hext : F.extremePoints ℝ = (S : Set E3) := by
    rw [hF.1.isExtreme.extremePoints_eq]
    ext x
    simp only [S, Finset.mem_coe, Finset.mem_filter, mem_inter_iff]
    change (x ∈ F ∧ x ∈ cubo.toSet.extremePoints ℝ) ↔
      x ∈ cubo.vertices ∧ x ∈ F
    rw [FiniteConvexPolytope.toSet, ← cubo.vertices_eq_extremePoints]
    tauto
  calc
    F = closure (convexHull ℝ (F.extremePoints ℝ)) := hKM.symm
    _ = closure (convexHull ℝ (S : Set E3)) := by rw [hext]
    _ = convexHull ℝ (S : Set E3) :=
      (S.finite_toSet.isClosed_convexHull ℝ).closure_eq
    _ = convexHull ℝ
        ((cubo.vertices.filter (· ∈ F) : Finset E3) : Set E3) := rfl

/-! ## Le sei simmetrie che portano la faccia {x=1} sulle sei facce -/

def segnoX : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.neg ℝ, LinearIsometryEquiv.refl ℝ ℝ,
      LinearIsometryEquiv.refl ℝ ℝ]

def scambioXY : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 1)

def scambioXZ : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 2)

/-- (x,y,z) ↦ (a,−1,b) sulla faccia {x=1}: porta {x=1} su {y=−1}. -/
def portaYm : E3 ≃ₗᵢ[ℝ] E3 := segnoX.trans scambioXY

/-- porta {x=1} su {z=−1}. -/
def portaZm : E3 ≃ₗᵢ[ℝ] E3 := segnoX.trans scambioXZ

/-- Le azioni di segnoX sugli otto vertici. -/
theorem segnoX_vertici : segnoX c0 = c4 ∧ segnoX c1 = c5 ∧ segnoX c2 = c6 ∧
    segnoX c3 = c7 ∧ segnoX c4 = c0 ∧ segnoX c5 = c1 ∧ segnoX c6 = c2 ∧
    segnoX c7 = c3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [segnoX, c0, c1, c2, c3, c4, c5, c6, c7,
        LinearIsometryEquiv.piLpCongrRight])

/-- Le azioni di scambioXY sugli otto vertici. -/
theorem scambioXY_vertici : scambioXY c0 = c0 ∧ scambioXY c1 = c1 ∧
    scambioXY c2 = c4 ∧ scambioXY c3 = c5 ∧ scambioXY c4 = c2 ∧
    scambioXY c5 = c3 ∧ scambioXY c6 = c6 ∧ scambioXY c7 = c7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [scambioXY, c0, c1, c2, c3, c4, c5, c6, c7, Equiv.swap_apply_def,
        LinearIsometryEquiv.piLpCongrLeft])

/-- Le azioni di scambioXZ sugli otto vertici. -/
theorem scambioXZ_vertici : scambioXZ c0 = c0 ∧ scambioXZ c1 = c4 ∧
    scambioXZ c2 = c2 ∧ scambioXZ c3 = c6 ∧ scambioXZ c4 = c1 ∧
    scambioXZ c5 = c5 ∧ scambioXZ c6 = c3 ∧ scambioXZ c7 = c7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [scambioXZ, c0, c1, c2, c3, c4, c5, c6, c7, Equiv.swap_apply_def,
        LinearIsometryEquiv.piLpCongrLeft])

/-! ## L'aritmetica dell'argmax -/

/-- I proiettori delle altre due coordinate. -/
def lY : E3 →L[ℝ] ℝ := EuclideanSpace.proj (1 : Fin 3)
def lZ : E3 →L[ℝ] ℝ := EuclideanSpace.proj (2 : Fin 3)

theorem lY_vertici : lY c0 = 1 ∧ lY c1 = 1 ∧ lY c2 = -1 ∧ lY c3 = -1 ∧
    lY c4 = 1 ∧ lY c5 = 1 ∧ lY c6 = -1 ∧ lY c7 = -1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem lZ_vertici : lZ c0 = 1 ∧ lZ c1 = -1 ∧ lZ c2 = 1 ∧ lZ c3 = -1 ∧
    lZ c4 = 1 ∧ lZ c5 = -1 ∧ lZ c6 = 1 ∧ lZ c7 = -1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

section Classificazione

variable (l : E3 →L[ℝ] ℝ)

/-- Le tre componenti del funzionale. -/
def compL (i : Fin 3) : ℝ := l (EuclideanSpace.single i 1)

theorem decomposizione_toLp (s0 s1 s2 : ℝ) :
    (WithLp.toLp 2 ![s0, s1, s2] : E3)
      = s0 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
        + s1 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
        + s2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
  ext j <;> fin_cases j <;> simp [EuclideanSpace.single_apply]

theorem l_toLp3 (s0 s1 s2 : ℝ) :
    l (WithLp.toLp 2 ![s0, s1, s2])
      = s0 * compL l 0 + s1 * compL l 1 + s2 * compL l 2 := by
  rw [decomposizione_toLp, map_add, map_add, map_smul, map_smul, map_smul]
  simp [compL, smul_eq_mul]

theorem l_c0 : l c0 = compL l 0 + compL l 1 + compL l 2 := by
  show l (WithLp.toLp 2 ![1, 1, 1]) = _
  rw [l_toLp3]
  ring

theorem l_c1 : l c1 = compL l 0 + compL l 1 - compL l 2 := by
  show l (WithLp.toLp 2 ![1, 1, -1]) = _
  rw [l_toLp3]
  ring

theorem l_c2 : l c2 = compL l 0 - compL l 1 + compL l 2 := by
  show l (WithLp.toLp 2 ![1, -1, 1]) = _
  rw [l_toLp3]
  ring

theorem l_c3 : l c3 = compL l 0 - compL l 1 - compL l 2 := by
  show l (WithLp.toLp 2 ![1, -1, -1]) = _
  rw [l_toLp3]
  ring

theorem l_c4 : l c4 = -compL l 0 + compL l 1 + compL l 2 := by
  show l (WithLp.toLp 2 ![-1, 1, 1]) = _
  rw [l_toLp3]
  ring

theorem l_c5 : l c5 = -compL l 0 + compL l 1 - compL l 2 := by
  show l (WithLp.toLp 2 ![-1, 1, -1]) = _
  rw [l_toLp3]
  ring

theorem l_c6 : l c6 = -compL l 0 - compL l 1 + compL l 2 := by
  show l (WithLp.toLp 2 ![-1, -1, 1]) = _
  rw [l_toLp3]
  ring

theorem l_c7 : l c7 = -compL l 0 - compL l 1 - compL l 2 := by
  show l (WithLp.toLp 2 ![-1, -1, -1]) = _
  rw [l_toLp3]
  ring

end Classificazione

/-- Lo span di un insieme dentro una coppia ha rango ≤ 1. -/
theorem span_coppia_le {T : Set E3} {v w : E3} (hT : T ⊆ {v, w}) :
    Module.finrank ℝ (vectorSpan ℝ T) ≤ 1 := by
  have hmono : vectorSpan ℝ T ≤ vectorSpan ℝ ({v, w} : Set E3) :=
    vectorSpan_mono ℝ hT
  have hle := Submodule.finrank_mono hmono
  have hpair : Module.finrank ℝ (vectorSpan ℝ ({v, w} : Set E3)) ≤ 1 := by
    rw [vectorSpan_pair]
    rcases eq_or_ne (v -ᵥ w) 0 with h0 | h0
    · rw [h0, Submodule.span_zero_singleton]
      simp
    · rw [finrank_span_singleton h0]
  omega

/-! ## Le sei facce come Finset e le caratterizzazioni per coordinate -/

def facciaXm : Finset E3 := {c4, c6, c7, c5}
def facciaY1 : Finset E3 := {c0, c4, c5, c1}
def facciaYm : Finset E3 := {c2, c6, c7, c3}
def facciaZ1 : Finset E3 := {c0, c2, c6, c4}
def facciaZm : Finset E3 := {c1, c3, c7, c5}

theorem argmax_verticiXm : {x ∈ (verticiCubo : Set E3) | lX x = -1}
    = (facciaXm : Set E3) := by
  ext z
  constructor
  · rintro ⟨hz, hlz⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exfalso; rw [lX_vertici.1] at hlz; norm_num at hlz
    · exfalso; rw [lX_vertici.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lX_vertici.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lX_vertici.2.2.2.1] at hlz; norm_num at hlz
    · simp [facciaXm]
    · simp [facciaXm]
    · simp [facciaXm]
    · simp [facciaXm]
  · intro hz
    have hcasi : z = c4 ∨ z = c6 ∨ z = c7 ∨ z = c5 := by
      simpa [facciaXm] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨by simp [verticiCubo], lX_vertici.2.2.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lX_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lX_vertici.2.2.2.2.2.2.2⟩
    · exact ⟨by simp [verticiCubo], lX_vertici.2.2.2.2.2.1⟩

theorem argmax_verticiY1 : {x ∈ (verticiCubo : Set E3) | lY x = 1}
    = (facciaY1 : Set E3) := by
  ext z
  constructor
  · rintro ⟨hz, hlz⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · simp [facciaY1]
    · simp [facciaY1]
    · exfalso; rw [lY_vertici.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lY_vertici.2.2.2.1] at hlz; norm_num at hlz
    · simp [facciaY1]
    · simp [facciaY1]
    · exfalso; rw [lY_vertici.2.2.2.2.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lY_vertici.2.2.2.2.2.2.2] at hlz; norm_num at hlz
  · intro hz
    have hcasi : z = c0 ∨ z = c4 ∨ z = c5 ∨ z = c1 := by
      simpa [facciaY1] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨by simp [verticiCubo], lY_vertici.1⟩
    · exact ⟨by simp [verticiCubo], lY_vertici.2.2.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lY_vertici.2.2.2.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lY_vertici.2.1⟩

theorem argmax_verticiYm : {x ∈ (verticiCubo : Set E3) | lY x = -1}
    = (facciaYm : Set E3) := by
  ext z
  constructor
  · rintro ⟨hz, hlz⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exfalso; rw [lY_vertici.1] at hlz; norm_num at hlz
    · exfalso; rw [lY_vertici.2.1] at hlz; norm_num at hlz
    · simp [facciaYm]
    · simp [facciaYm]
    · exfalso; rw [lY_vertici.2.2.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lY_vertici.2.2.2.2.2.1] at hlz; norm_num at hlz
    · simp [facciaYm]
    · simp [facciaYm]
  · intro hz
    have hcasi : z = c2 ∨ z = c6 ∨ z = c7 ∨ z = c3 := by
      simpa [facciaYm] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨by simp [verticiCubo], lY_vertici.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lY_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lY_vertici.2.2.2.2.2.2.2⟩
    · exact ⟨by simp [verticiCubo], lY_vertici.2.2.2.1⟩

theorem argmax_verticiZ1 : {x ∈ (verticiCubo : Set E3) | lZ x = 1}
    = (facciaZ1 : Set E3) := by
  ext z
  constructor
  · rintro ⟨hz, hlz⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · simp [facciaZ1]
    · exfalso; rw [lZ_vertici.2.1] at hlz; norm_num at hlz
    · simp [facciaZ1]
    · exfalso; rw [lZ_vertici.2.2.2.1] at hlz; norm_num at hlz
    · simp [facciaZ1]
    · exfalso; rw [lZ_vertici.2.2.2.2.2.1] at hlz; norm_num at hlz
    · simp [facciaZ1]
    · exfalso; rw [lZ_vertici.2.2.2.2.2.2.2] at hlz; norm_num at hlz
  · intro hz
    have hcasi : z = c0 ∨ z = c2 ∨ z = c6 ∨ z = c4 := by
      simpa [facciaZ1] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨by simp [verticiCubo], lZ_vertici.1⟩
    · exact ⟨by simp [verticiCubo], lZ_vertici.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lZ_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lZ_vertici.2.2.2.2.1⟩

theorem argmax_verticiZm : {x ∈ (verticiCubo : Set E3) | lZ x = -1}
    = (facciaZm : Set E3) := by
  ext z
  constructor
  · rintro ⟨hz, hlz⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exfalso; rw [lZ_vertici.1] at hlz; norm_num at hlz
    · simp [facciaZm]
    · exfalso; rw [lZ_vertici.2.2.1] at hlz; norm_num at hlz
    · simp [facciaZm]
    · exfalso; rw [lZ_vertici.2.2.2.2.1] at hlz; norm_num at hlz
    · simp [facciaZm]
    · exfalso; rw [lZ_vertici.2.2.2.2.2.2.1] at hlz; norm_num at hlz
    · simp [facciaZm]
  · intro hz
    have hcasi : z = c1 ∨ z = c3 ∨ z = c7 ∨ z = c5 := by
      simpa [facciaZm] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨by simp [verticiCubo], lZ_vertici.2.1⟩
    · exact ⟨by simp [verticiCubo], lZ_vertici.2.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lZ_vertici.2.2.2.2.2.2.2⟩
    · exact ⟨by simp [verticiCubo], lZ_vertici.2.2.2.2.2.1⟩

/-! ## Le sei esclusioni di segno -/

section Esclusioni

variable (l : E3 →L[ℝ] ℝ)

theorem esclusione_xp (hx : 0 < compL l 0) {u : E3}
    (hu : u ∈ (verticiCubo : Set E3))
    (hmax : ∀ w ∈ (verticiCubo : Set E3), l w ≤ l u) : lX u = 1 := by
  rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
    h | h | h | h | h | h | h | h <;> subst h
  · exact lX_vertici.1
  · exact lX_vertici.2.1
  · exact lX_vertici.2.2.1
  · exact lX_vertici.2.2.2.1
  · exfalso; have h := hmax c0 (by simp [verticiCubo])
    rw [l_c0, l_c4] at h; linarith
  · exfalso; have h := hmax c1 (by simp [verticiCubo])
    rw [l_c1, l_c5] at h; linarith
  · exfalso; have h := hmax c2 (by simp [verticiCubo])
    rw [l_c2, l_c6] at h; linarith
  · exfalso; have h := hmax c3 (by simp [verticiCubo])
    rw [l_c3, l_c7] at h; linarith

theorem esclusione_xm (hx : compL l 0 < 0) {u : E3}
    (hu : u ∈ (verticiCubo : Set E3))
    (hmax : ∀ w ∈ (verticiCubo : Set E3), l w ≤ l u) : lX u = -1 := by
  rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
    h | h | h | h | h | h | h | h <;> subst h
  · exfalso; have h := hmax c4 (by simp [verticiCubo])
    rw [l_c4, l_c0] at h; linarith
  · exfalso; have h := hmax c5 (by simp [verticiCubo])
    rw [l_c5, l_c1] at h; linarith
  · exfalso; have h := hmax c6 (by simp [verticiCubo])
    rw [l_c6, l_c2] at h; linarith
  · exfalso; have h := hmax c7 (by simp [verticiCubo])
    rw [l_c7, l_c3] at h; linarith
  · exact lX_vertici.2.2.2.2.1
  · exact lX_vertici.2.2.2.2.2.1
  · exact lX_vertici.2.2.2.2.2.2.1
  · exact lX_vertici.2.2.2.2.2.2.2

theorem esclusione_yp (hy : 0 < compL l 1) {u : E3}
    (hu : u ∈ (verticiCubo : Set E3))
    (hmax : ∀ w ∈ (verticiCubo : Set E3), l w ≤ l u) : lY u = 1 := by
  rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
    h | h | h | h | h | h | h | h <;> subst h
  · exact lY_vertici.1
  · exact lY_vertici.2.1
  · exfalso; have h := hmax c0 (by simp [verticiCubo])
    rw [l_c0, l_c2] at h; linarith
  · exfalso; have h := hmax c1 (by simp [verticiCubo])
    rw [l_c1, l_c3] at h; linarith
  · exact lY_vertici.2.2.2.2.1
  · exact lY_vertici.2.2.2.2.2.1
  · exfalso; have h := hmax c4 (by simp [verticiCubo])
    rw [l_c4, l_c6] at h; linarith
  · exfalso; have h := hmax c5 (by simp [verticiCubo])
    rw [l_c5, l_c7] at h; linarith

theorem esclusione_ym (hy : compL l 1 < 0) {u : E3}
    (hu : u ∈ (verticiCubo : Set E3))
    (hmax : ∀ w ∈ (verticiCubo : Set E3), l w ≤ l u) : lY u = -1 := by
  rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
    h | h | h | h | h | h | h | h <;> subst h
  · exfalso; have h := hmax c2 (by simp [verticiCubo])
    rw [l_c2, l_c0] at h; linarith
  · exfalso; have h := hmax c3 (by simp [verticiCubo])
    rw [l_c3, l_c1] at h; linarith
  · exact lY_vertici.2.2.1
  · exact lY_vertici.2.2.2.1
  · exfalso; have h := hmax c6 (by simp [verticiCubo])
    rw [l_c6, l_c4] at h; linarith
  · exfalso; have h := hmax c7 (by simp [verticiCubo])
    rw [l_c7, l_c5] at h; linarith
  · exact lY_vertici.2.2.2.2.2.2.1
  · exact lY_vertici.2.2.2.2.2.2.2

theorem esclusione_zp (hz : 0 < compL l 2) {u : E3}
    (hu : u ∈ (verticiCubo : Set E3))
    (hmax : ∀ w ∈ (verticiCubo : Set E3), l w ≤ l u) : lZ u = 1 := by
  rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
    h | h | h | h | h | h | h | h <;> subst h
  · exact lZ_vertici.1
  · exfalso; have h := hmax c0 (by simp [verticiCubo])
    rw [l_c0, l_c1] at h; linarith
  · exact lZ_vertici.2.2.1
  · exfalso; have h := hmax c2 (by simp [verticiCubo])
    rw [l_c2, l_c3] at h; linarith
  · exact lZ_vertici.2.2.2.2.1
  · exfalso; have h := hmax c4 (by simp [verticiCubo])
    rw [l_c4, l_c5] at h; linarith
  · exact lZ_vertici.2.2.2.2.2.2.1
  · exfalso; have h := hmax c6 (by simp [verticiCubo])
    rw [l_c6, l_c7] at h; linarith

theorem esclusione_zm (hz : compL l 2 < 0) {u : E3}
    (hu : u ∈ (verticiCubo : Set E3))
    (hmax : ∀ w ∈ (verticiCubo : Set E3), l w ≤ l u) : lZ u = -1 := by
  rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
    h | h | h | h | h | h | h | h <;> subst h
  · exfalso; have h := hmax c1 (by simp [verticiCubo])
    rw [l_c1, l_c0] at h; linarith
  · exact lZ_vertici.2.1
  · exfalso; have h := hmax c3 (by simp [verticiCubo])
    rw [l_c3, l_c2] at h; linarith
  · exact lZ_vertici.2.2.2.1
  · exfalso; have h := hmax c5 (by simp [verticiCubo])
    rw [l_c5, l_c4] at h; linarith
  · exact lZ_vertici.2.2.2.2.2.1
  · exfalso; have h := hmax c7 (by simp [verticiCubo])
    rw [l_c7, l_c6] at h; linarith
  · exact lZ_vertici.2.2.2.2.2.2.2

end Esclusioni

/-! ## Azioni delle composizioni sui vertici -/

theorem portaYm_vertici : portaYm c0 = c2 ∧ portaYm c1 = c3 ∧ portaYm c2 = c6 ∧
    portaYm c3 = c7 ∧ portaYm c4 = c0 ∧ portaYm c5 = c1 ∧ portaYm c6 = c4 ∧
    portaYm c7 = c5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [portaYm, segnoX, scambioXY, c0, c1, c2, c3, c4, c5, c6, c7,
        Equiv.swap_apply_def, LinearIsometryEquiv.piLpCongrLeft,
        LinearIsometryEquiv.piLpCongrRight])

theorem portaZm_vertici : portaZm c0 = c1 ∧ portaZm c1 = c5 ∧ portaZm c2 = c3 ∧
    portaZm c3 = c7 ∧ portaZm c4 = c0 ∧ portaZm c5 = c4 ∧ portaZm c6 = c2 ∧
    portaZm c7 = c6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [portaZm, segnoX, scambioXZ, c0, c1, c2, c3, c4, c5, c6, c7,
        Equiv.swap_apply_def, LinearIsometryEquiv.piLpCongrLeft,
        LinearIsometryEquiv.piLpCongrRight])

/-! ## Le cinque permutazioni dei vertici e la preservazione del politopo -/

theorem segnoX_vertset :
    (⇑segnoX) '' (verticiCubo : Set E3) = (verticiCubo : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [segnoX_vertici.1, segnoX_vertici.2.1, segnoX_vertici.2.2.1,
        segnoX_vertici.2.2.2.1, segnoX_vertici.2.2.2.2.1,
        segnoX_vertici.2.2.2.2.2.1, segnoX_vertici.2.2.2.2.2.2.1,
        segnoX_vertici.2.2.2.2.2.2.2] <;>
      simp [verticiCubo]
  · intro hz
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exact ⟨c4, by simp [verticiCubo], segnoX_vertici.2.2.2.2.1⟩
    · exact ⟨c5, by simp [verticiCubo], segnoX_vertici.2.2.2.2.2.1⟩
    · exact ⟨c6, by simp [verticiCubo], segnoX_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨c7, by simp [verticiCubo], segnoX_vertici.2.2.2.2.2.2.2⟩
    · exact ⟨c0, by simp [verticiCubo], segnoX_vertici.1⟩
    · exact ⟨c1, by simp [verticiCubo], segnoX_vertici.2.1⟩
    · exact ⟨c2, by simp [verticiCubo], segnoX_vertici.2.2.1⟩
    · exact ⟨c3, by simp [verticiCubo], segnoX_vertici.2.2.2.1⟩

theorem scambioXY_vertset :
    (⇑scambioXY) '' (verticiCubo : Set E3) = (verticiCubo : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [scambioXY_vertici.1, scambioXY_vertici.2.1,
        scambioXY_vertici.2.2.1, scambioXY_vertici.2.2.2.1,
        scambioXY_vertici.2.2.2.2.1, scambioXY_vertici.2.2.2.2.2.1,
        scambioXY_vertici.2.2.2.2.2.2.1, scambioXY_vertici.2.2.2.2.2.2.2] <;>
      simp [verticiCubo]
  · intro hz
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exact ⟨c0, by simp [verticiCubo], scambioXY_vertici.1⟩
    · exact ⟨c1, by simp [verticiCubo], scambioXY_vertici.2.1⟩
    · exact ⟨c4, by simp [verticiCubo], scambioXY_vertici.2.2.2.2.1⟩
    · exact ⟨c5, by simp [verticiCubo], scambioXY_vertici.2.2.2.2.2.1⟩
    · exact ⟨c2, by simp [verticiCubo], scambioXY_vertici.2.2.1⟩
    · exact ⟨c3, by simp [verticiCubo], scambioXY_vertici.2.2.2.1⟩
    · exact ⟨c6, by simp [verticiCubo], scambioXY_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨c7, by simp [verticiCubo], scambioXY_vertici.2.2.2.2.2.2.2⟩

theorem scambioXZ_vertset :
    (⇑scambioXZ) '' (verticiCubo : Set E3) = (verticiCubo : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [scambioXZ_vertici.1, scambioXZ_vertici.2.1,
        scambioXZ_vertici.2.2.1, scambioXZ_vertici.2.2.2.1,
        scambioXZ_vertici.2.2.2.2.1, scambioXZ_vertici.2.2.2.2.2.1,
        scambioXZ_vertici.2.2.2.2.2.2.1, scambioXZ_vertici.2.2.2.2.2.2.2] <;>
      simp [verticiCubo]
  · intro hz
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exact ⟨c0, by simp [verticiCubo], scambioXZ_vertici.1⟩
    · exact ⟨c4, by simp [verticiCubo], scambioXZ_vertici.2.2.2.2.1⟩
    · exact ⟨c2, by simp [verticiCubo], scambioXZ_vertici.2.2.1⟩
    · exact ⟨c6, by simp [verticiCubo], scambioXZ_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨c1, by simp [verticiCubo], scambioXZ_vertici.2.1⟩
    · exact ⟨c5, by simp [verticiCubo], scambioXZ_vertici.2.2.2.2.2.1⟩
    · exact ⟨c3, by simp [verticiCubo], scambioXZ_vertici.2.2.2.1⟩
    · exact ⟨c7, by simp [verticiCubo], scambioXZ_vertici.2.2.2.2.2.2.2⟩

theorem portaYm_vertset :
    (⇑portaYm) '' (verticiCubo : Set E3) = (verticiCubo : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [portaYm_vertici.1, portaYm_vertici.2.1, portaYm_vertici.2.2.1,
        portaYm_vertici.2.2.2.1, portaYm_vertici.2.2.2.2.1,
        portaYm_vertici.2.2.2.2.2.1, portaYm_vertici.2.2.2.2.2.2.1,
        portaYm_vertici.2.2.2.2.2.2.2] <;>
      simp [verticiCubo]
  · intro hz
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exact ⟨c4, by simp [verticiCubo], portaYm_vertici.2.2.2.2.1⟩
    · exact ⟨c5, by simp [verticiCubo], portaYm_vertici.2.2.2.2.2.1⟩
    · exact ⟨c0, by simp [verticiCubo], portaYm_vertici.1⟩
    · exact ⟨c1, by simp [verticiCubo], portaYm_vertici.2.1⟩
    · exact ⟨c6, by simp [verticiCubo], portaYm_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨c7, by simp [verticiCubo], portaYm_vertici.2.2.2.2.2.2.2⟩
    · exact ⟨c2, by simp [verticiCubo], portaYm_vertici.2.2.1⟩
    · exact ⟨c3, by simp [verticiCubo], portaYm_vertici.2.2.2.1⟩

theorem portaZm_vertset :
    (⇑portaZm) '' (verticiCubo : Set E3) = (verticiCubo : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [portaZm_vertici.1, portaZm_vertici.2.1, portaZm_vertici.2.2.1,
        portaZm_vertici.2.2.2.1, portaZm_vertici.2.2.2.2.1,
        portaZm_vertici.2.2.2.2.2.1, portaZm_vertici.2.2.2.2.2.2.1,
        portaZm_vertici.2.2.2.2.2.2.2] <;>
      simp [verticiCubo]
  · intro hz
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exact ⟨c4, by simp [verticiCubo], portaZm_vertici.2.2.2.2.1⟩
    · exact ⟨c0, by simp [verticiCubo], portaZm_vertici.1⟩
    · exact ⟨c6, by simp [verticiCubo], portaZm_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨c2, by simp [verticiCubo], portaZm_vertici.2.2.1⟩
    · exact ⟨c5, by simp [verticiCubo], portaZm_vertici.2.2.2.2.2.1⟩
    · exact ⟨c1, by simp [verticiCubo], portaZm_vertici.2.1⟩
    · exact ⟨c7, by simp [verticiCubo], portaZm_vertici.2.2.2.2.2.2.2⟩
    · exact ⟨c3, by simp [verticiCubo], portaZm_vertici.2.2.2.1⟩

/-- Se un'isometria lineare permuta i vertici, la versione affine preserva il
corpo del cubo. -/
theorem preserva_toSet_di_vertici (g : E3 ≃ₗᵢ[ℝ] E3)
    (hv : (⇑g) '' (verticiCubo : Set E3) = (verticiCubo : Set E3)) :
    (⇑g.toAffineIsometryEquiv) '' cubo.toSet = cubo.toSet := by
  show (⇑g.toAffineIsometryEquiv) '' (convexHull ℝ (verticiCubo : Set E3))
    = convexHull ℝ (verticiCubo : Set E3)
  have haff : (⇑g.toAffineIsometryEquiv) '' (convexHull ℝ (verticiCubo : Set E3))
      = convexHull ℝ ((⇑g.toAffineIsometryEquiv) '' (verticiCubo : Set E3)) :=
    AffineMap.image_convexHull g.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff, show (⇑g.toAffineIsometryEquiv) '' (verticiCubo : Set E3)
    = (verticiCubo : Set E3) from hv]

/-! ## Le cinque immagini della faccia F₀ -/

theorem segnoX_F₀ : (⇑segnoX.toAffineIsometryEquiv) '' F₀
    = convexHull ℝ (facciaXm : Set E3) := by
  show (⇑segnoX.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3)) = _
  have haff : (⇑segnoX.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3))
      = convexHull ℝ ((⇑segnoX.toAffineIsometryEquiv) '' (facciaX1 : Set E3)) :=
    AffineMap.image_convexHull segnoX.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑segnoX.toAffineIsometryEquiv) u = segnoX u := rfl
    rw [hcv]
    have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
      simpa [facciaX1] using hu
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [segnoX_vertici.1, segnoX_vertici.2.1, segnoX_vertici.2.2.1,
        segnoX_vertici.2.2.2.1] <;>
      simp [facciaXm]
  · intro hz
    have hcasi : z = c4 ∨ z = c6 ∨ z = c7 ∨ z = c5 := by
      simpa [facciaXm] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨c0, by simp [facciaX1], segnoX_vertici.1⟩
    · exact ⟨c2, by simp [facciaX1], segnoX_vertici.2.2.1⟩
    · exact ⟨c3, by simp [facciaX1], segnoX_vertici.2.2.2.1⟩
    · exact ⟨c1, by simp [facciaX1], segnoX_vertici.2.1⟩

theorem scambioXY_F₀ : (⇑scambioXY.toAffineIsometryEquiv) '' F₀
    = convexHull ℝ (facciaY1 : Set E3) := by
  show (⇑scambioXY.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3)) = _
  have haff : (⇑scambioXY.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3))
      = convexHull ℝ ((⇑scambioXY.toAffineIsometryEquiv) '' (facciaX1 : Set E3)) :=
    AffineMap.image_convexHull scambioXY.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑scambioXY.toAffineIsometryEquiv) u = scambioXY u := rfl
    rw [hcv]
    have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
      simpa [facciaX1] using hu
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [scambioXY_vertici.1, scambioXY_vertici.2.1,
        scambioXY_vertici.2.2.1, scambioXY_vertici.2.2.2.1] <;>
      simp [facciaY1]
  · intro hz
    have hcasi : z = c0 ∨ z = c4 ∨ z = c5 ∨ z = c1 := by
      simpa [facciaY1] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨c0, by simp [facciaX1], scambioXY_vertici.1⟩
    · exact ⟨c2, by simp [facciaX1], scambioXY_vertici.2.2.1⟩
    · exact ⟨c3, by simp [facciaX1], scambioXY_vertici.2.2.2.1⟩
    · exact ⟨c1, by simp [facciaX1], scambioXY_vertici.2.1⟩

theorem portaYm_F₀ : (⇑portaYm.toAffineIsometryEquiv) '' F₀
    = convexHull ℝ (facciaYm : Set E3) := by
  show (⇑portaYm.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3)) = _
  have haff : (⇑portaYm.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3))
      = convexHull ℝ ((⇑portaYm.toAffineIsometryEquiv) '' (facciaX1 : Set E3)) :=
    AffineMap.image_convexHull portaYm.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑portaYm.toAffineIsometryEquiv) u = portaYm u := rfl
    rw [hcv]
    have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
      simpa [facciaX1] using hu
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [portaYm_vertici.1, portaYm_vertici.2.1, portaYm_vertici.2.2.1,
        portaYm_vertici.2.2.2.1] <;>
      simp [facciaYm]
  · intro hz
    have hcasi : z = c2 ∨ z = c6 ∨ z = c7 ∨ z = c3 := by
      simpa [facciaYm] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨c0, by simp [facciaX1], portaYm_vertici.1⟩
    · exact ⟨c2, by simp [facciaX1], portaYm_vertici.2.2.1⟩
    · exact ⟨c3, by simp [facciaX1], portaYm_vertici.2.2.2.1⟩
    · exact ⟨c1, by simp [facciaX1], portaYm_vertici.2.1⟩

theorem scambioXZ_F₀ : (⇑scambioXZ.toAffineIsometryEquiv) '' F₀
    = convexHull ℝ (facciaZ1 : Set E3) := by
  show (⇑scambioXZ.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3)) = _
  have haff : (⇑scambioXZ.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3))
      = convexHull ℝ ((⇑scambioXZ.toAffineIsometryEquiv) '' (facciaX1 : Set E3)) :=
    AffineMap.image_convexHull scambioXZ.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑scambioXZ.toAffineIsometryEquiv) u = scambioXZ u := rfl
    rw [hcv]
    have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
      simpa [facciaX1] using hu
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [scambioXZ_vertici.1, scambioXZ_vertici.2.1,
        scambioXZ_vertici.2.2.1, scambioXZ_vertici.2.2.2.1] <;>
      simp [facciaZ1]
  · intro hz
    have hcasi : z = c0 ∨ z = c2 ∨ z = c6 ∨ z = c4 := by
      simpa [facciaZ1] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨c0, by simp [facciaX1], scambioXZ_vertici.1⟩
    · exact ⟨c2, by simp [facciaX1], scambioXZ_vertici.2.2.1⟩
    · exact ⟨c3, by simp [facciaX1], scambioXZ_vertici.2.2.2.1⟩
    · exact ⟨c1, by simp [facciaX1], scambioXZ_vertici.2.1⟩

theorem portaZm_F₀ : (⇑portaZm.toAffineIsometryEquiv) '' F₀
    = convexHull ℝ (facciaZm : Set E3) := by
  show (⇑portaZm.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3)) = _
  have haff : (⇑portaZm.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3))
      = convexHull ℝ ((⇑portaZm.toAffineIsometryEquiv) '' (facciaX1 : Set E3)) :=
    AffineMap.image_convexHull portaZm.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑portaZm.toAffineIsometryEquiv) u = portaZm u := rfl
    rw [hcv]
    have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
      simpa [facciaX1] using hu
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [portaZm_vertici.1, portaZm_vertici.2.1, portaZm_vertici.2.2.1,
        portaZm_vertici.2.2.2.1] <;>
      simp [facciaZm]
  · intro hz
    have hcasi : z = c1 ∨ z = c3 ∨ z = c7 ∨ z = c5 := by
      simpa [facciaZm] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨c0, by simp [facciaX1], portaZm_vertici.1⟩
    · exact ⟨c2, by simp [facciaX1], portaZm_vertici.2.2.1⟩
    · exact ⟨c3, by simp [facciaX1], portaZm_vertici.2.2.2.1⟩
    · exact ⟨c1, by simp [facciaX1], portaZm_vertici.2.1⟩

/-! ## LA CLASSIFICAZIONE DELLE FACCETTE DEL CUBO -/

set_option maxHeartbeats 1600000 in
/-- LA CLASSIFICAZIONE: ogni faccetta del cubo è una delle sei facce. -/
theorem facet_classification_cubo {F : Set E3} (hF : cubo.IsFacet F) :
    F = convexHull ℝ (facciaX1 : Set E3) ∨ F = convexHull ℝ (facciaXm : Set E3)
    ∨ F = convexHull ℝ (facciaY1 : Set E3) ∨ F = convexHull ℝ (facciaYm : Set E3)
    ∨ F = convexHull ℝ (facciaZ1 : Set E3) ∨ F = convexHull ℝ (facciaZm : Set E3) := by
  classical
  obtain ⟨l, hl⟩ := hF.1.1 hF.1.2
  have hFS := exposedFace_eq_convexHull_vertices_cubo hF.1
  set S : Finset E3 := cubo.vertices.filter (· ∈ F) with hSdef
  have hspanS : vectorSpan ℝ (S : Set E3)
      = vectorSpan ℝ (convexHull ℝ (S : Set E3)) := by
    rw [← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]
  have hd : Module.finrank ℝ (vectorSpan ℝ (S : Set E3)) = 2 := by
    have hdF := hF.2
    rw [hFS, ← hspanS] at hdF
    exact hdF
  have hSsub : (S : Set E3) ⊆ (cubo.vertices : Set E3) := by
    intro u hu
    have : u ∈ cubo.vertices.filter (· ∈ F) := by exact_mod_cast hu
    exact_mod_cast Finset.filter_subset _ _ this
  have hcrit : ∀ u ∈ (cubo.vertices : Set E3),
      (u ∈ (S : Set E3) ↔ ∀ w ∈ (cubo.vertices : Set E3), l w ≤ l u) := by
    intro u hu
    constructor
    · intro huS w hw
      have huF : u ∈ F :=
        (Finset.mem_filter.mp (by exact_mod_cast huS)).2
      rw [hl] at huF
      exact huF.2 w (subset_convexHull ℝ _ hw)
    · intro hargmax
      have huF : u ∈ F := by
        rw [hl]
        refine ⟨subset_convexHull ℝ _ hu, ?_⟩
        intro y hy
        exact convexHull_min hargmax
          (convex_halfSpace_le (LinearMap.isLinear l.toLinearMap) (l u)) hy
      show u ∈ ((cubo.vertices.filter (· ∈ F) : Finset E3) : Set E3)
      exact_mod_cast Finset.mem_filter.mpr ⟨by exact_mod_cast hu, huF⟩
  -- lo scheletro comune dei rami-coppia
  have hcoppia : ∀ v w : E3, (S : Set E3) ⊆ {v, w} → False := by
    intro v w hsub
    have := span_coppia_le hsub
    omega
  rcases lt_trichotomy (compL l 0) 0 with hx | hx | hx
  · -- a0 < 0
    rcases lt_trichotomy (compL l 1) 0 with hy | hy | hy
    · -- a0 < 0, a1 < 0 → S ⊆ {c6, c7}
      exact absurd hd (by
        have hsub : (S : Set E3) ⊆ {c6, c7} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hx1 := esclusione_xm l hx hu hmax
          have hy1 := esclusione_ym l hy hu hmax
          have hux : u ∈ (facciaXm : Set E3) := by
            rw [← argmax_verticiXm]; exact ⟨hu, hx1⟩
          have hcasi : u = c4 ∨ u = c6 ∨ u = c7 ∨ u = c5 := by
            simpa [facciaXm] using hux
          rcases hcasi with h | h | h | h <;> subst h
          · rw [lY_vertici.2.2.2.2.1] at hy1; norm_num at hy1
          · simp
          · simp
          · rw [lY_vertici.2.2.2.2.2.1] at hy1; norm_num at hy1
        have := span_coppia_le hsub
        omega)
    · -- a0 < 0, a1 = 0
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- a0 < 0, a2 < 0 → S ⊆ {c5, c7}
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {c5, c7} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            have hx1 := esclusione_xm l hx hu hmax
            have hz1 := esclusione_zm l hz hu hmax
            have hux : u ∈ (facciaXm : Set E3) := by
              rw [← argmax_verticiXm]; exact ⟨hu, hx1⟩
            have hcasi : u = c4 ∨ u = c6 ∨ u = c7 ∨ u = c5 := by
              simpa [facciaXm] using hux
            rcases hcasi with h | h | h | h <;> subst h
            · rw [lZ_vertici.2.2.2.2.1] at hz1; norm_num at hz1
            · rw [lZ_vertici.2.2.2.2.2.2.1] at hz1; norm_num at hz1
            · simp
            · simp
          have := span_coppia_le hsub
          omega)
      · -- SOLO a0 < 0: la faccia {x = -1}
        refine Or.inr (Or.inl ?_)
        rw [hFS]
        congr 1
        ext u
        constructor
        · intro huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hx1 := esclusione_xm l hx hu hmax
          rw [← argmax_verticiXm]
          exact ⟨hu, hx1⟩
        · intro huf
          have hcasi : u = c4 ∨ u = c6 ∨ u = c7 ∨ u = c5 := by
            simpa [facciaXm] using huf
          have hu : u ∈ (cubo.vertices : Set E3) := by
            rcases hcasi with h | h | h | h <;> subst h <;>
              simp [cubo, verticiCubo]
          refine (hcrit u hu).mpr ?_
          intro w hw
          rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
            h | h | h | h | h | h | h | h <;> subst h <;>
          rcases hcasi with h | h | h | h <;> subst h <;>
            simp only [l_c0, l_c1, l_c2, l_c3, l_c4, l_c5, l_c6, l_c7] <;>
            linarith
      · -- a0 < 0, a2 > 0 → S ⊆ {c4, c6}
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {c4, c6} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            have hx1 := esclusione_xm l hx hu hmax
            have hz1 := esclusione_zp l hz hu hmax
            have hux : u ∈ (facciaXm : Set E3) := by
              rw [← argmax_verticiXm]; exact ⟨hu, hx1⟩
            have hcasi : u = c4 ∨ u = c6 ∨ u = c7 ∨ u = c5 := by
              simpa [facciaXm] using hux
            rcases hcasi with h | h | h | h <;> subst h
            · simp
            · simp
            · rw [lZ_vertici.2.2.2.2.2.2.2] at hz1; norm_num at hz1
            · rw [lZ_vertici.2.2.2.2.2.1] at hz1; norm_num at hz1
          have := span_coppia_le hsub
          omega)
    · -- a0 < 0, a1 > 0 → S ⊆ {c4, c5}
      exact absurd hd (by
        have hsub : (S : Set E3) ⊆ {c4, c5} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hx1 := esclusione_xm l hx hu hmax
          have hy1 := esclusione_yp l hy hu hmax
          have hux : u ∈ (facciaXm : Set E3) := by
            rw [← argmax_verticiXm]; exact ⟨hu, hx1⟩
          have hcasi : u = c4 ∨ u = c6 ∨ u = c7 ∨ u = c5 := by
            simpa [facciaXm] using hux
          rcases hcasi with h | h | h | h <;> subst h
          · simp
          · rw [lY_vertici.2.2.2.2.2.2.1] at hy1; norm_num at hy1
          · rw [lY_vertici.2.2.2.2.2.2.2] at hy1; norm_num at hy1
          · simp
        have := span_coppia_le hsub
        omega)
  · -- a0 = 0
    rcases lt_trichotomy (compL l 1) 0 with hy | hy | hy
    · -- a0 = 0, a1 < 0
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- a1 < 0, a2 < 0 → S ⊆ {c3, c7}
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {c3, c7} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            have hy1 := esclusione_ym l hy hu hmax
            have hz1 := esclusione_zm l hz hu hmax
            have huy : u ∈ (facciaYm : Set E3) := by
              rw [← argmax_verticiYm]; exact ⟨hu, hy1⟩
            have hcasi : u = c2 ∨ u = c6 ∨ u = c7 ∨ u = c3 := by
              simpa [facciaYm] using huy
            rcases hcasi with h | h | h | h <;> subst h
            · rw [lZ_vertici.2.2.1] at hz1; norm_num at hz1
            · rw [lZ_vertici.2.2.2.2.2.2.1] at hz1; norm_num at hz1
            · simp
            · simp
          have := span_coppia_le hsub
          omega)
      · -- SOLO a1 < 0: la faccia {y = -1}
        refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        rw [hFS]
        congr 1
        ext u
        constructor
        · intro huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hy1 := esclusione_ym l hy hu hmax
          rw [← argmax_verticiYm]
          exact ⟨hu, hy1⟩
        · intro huf
          have hcasi : u = c2 ∨ u = c6 ∨ u = c7 ∨ u = c3 := by
            simpa [facciaYm] using huf
          have hu : u ∈ (cubo.vertices : Set E3) := by
            rcases hcasi with h | h | h | h <;> subst h <;>
              simp [cubo, verticiCubo]
          refine (hcrit u hu).mpr ?_
          intro w hw
          rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
            h | h | h | h | h | h | h | h <;> subst h <;>
          rcases hcasi with h | h | h | h <;> subst h <;>
            simp only [l_c0, l_c1, l_c2, l_c3, l_c4, l_c5, l_c6, l_c7] <;>
            linarith
      · -- a1 < 0, a2 > 0 → S ⊆ {c2, c6}
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {c2, c6} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            have hy1 := esclusione_ym l hy hu hmax
            have hz1 := esclusione_zp l hz hu hmax
            have huy : u ∈ (facciaYm : Set E3) := by
              rw [← argmax_verticiYm]; exact ⟨hu, hy1⟩
            have hcasi : u = c2 ∨ u = c6 ∨ u = c7 ∨ u = c3 := by
              simpa [facciaYm] using huy
            rcases hcasi with h | h | h | h <;> subst h
            · simp
            · simp
            · rw [lZ_vertici.2.2.2.2.2.2.2] at hz1; norm_num at hz1
            · rw [lZ_vertici.2.2.2.1] at hz1; norm_num at hz1
          have := span_coppia_le hsub
          omega)
    · -- a0 = 0, a1 = 0
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- SOLO a2 < 0: la faccia {z = -1}
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
        rw [hFS]
        congr 1
        ext u
        constructor
        · intro huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hz1 := esclusione_zm l hz hu hmax
          rw [← argmax_verticiZm]
          exact ⟨hu, hz1⟩
        · intro huf
          have hcasi : u = c1 ∨ u = c3 ∨ u = c7 ∨ u = c5 := by
            simpa [facciaZm] using huf
          have hu : u ∈ (cubo.vertices : Set E3) := by
            rcases hcasi with h | h | h | h <;> subst h <;>
              simp [cubo, verticiCubo]
          refine (hcrit u hu).mpr ?_
          intro w hw
          rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
            h | h | h | h | h | h | h | h <;> subst h <;>
          rcases hcasi with h | h | h | h <;> subst h <;>
            simp only [l_c0, l_c1, l_c2, l_c3, l_c4, l_c5, l_c6, l_c7] <;>
            linarith
      · -- TUTTI NULLI: S = tutti i vertici, span 3D, assurdo
        exfalso
        have hSall : (S : Set E3) = (cubo.vertices : Set E3) := by
          apply Set.Subset.antisymm hSsub
          intro u hu
          refine (hcrit u hu).mpr ?_
          intro w hw
          rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
            h | h | h | h | h | h | h | h <;> subst h <;>
          rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h | h | h <;> subst h <;>
            simp only [l_c0, l_c1, l_c2, l_c3, l_c4, l_c5, l_c6, l_c7] <;>
            linarith
        rw [hSall, cubo_finrank] at hd
        omega
      · -- SOLO a2 > 0: la faccia {z = 1}
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        rw [hFS]
        congr 1
        ext u
        constructor
        · intro huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hz1 := esclusione_zp l hz hu hmax
          rw [← argmax_verticiZ1]
          exact ⟨hu, hz1⟩
        · intro huf
          have hcasi : u = c0 ∨ u = c2 ∨ u = c6 ∨ u = c4 := by
            simpa [facciaZ1] using huf
          have hu : u ∈ (cubo.vertices : Set E3) := by
            rcases hcasi with h | h | h | h <;> subst h <;>
              simp [cubo, verticiCubo]
          refine (hcrit u hu).mpr ?_
          intro w hw
          rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
            h | h | h | h | h | h | h | h <;> subst h <;>
          rcases hcasi with h | h | h | h <;> subst h <;>
            simp only [l_c0, l_c1, l_c2, l_c3, l_c4, l_c5, l_c6, l_c7] <;>
            linarith
    · -- a0 = 0, a1 > 0
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- a1 > 0, a2 < 0 → S ⊆ {c1, c5}
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {c1, c5} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            have hy1 := esclusione_yp l hy hu hmax
            have hz1 := esclusione_zm l hz hu hmax
            have huy : u ∈ (facciaY1 : Set E3) := by
              rw [← argmax_verticiY1]; exact ⟨hu, hy1⟩
            have hcasi : u = c0 ∨ u = c4 ∨ u = c5 ∨ u = c1 := by
              simpa [facciaY1] using huy
            rcases hcasi with h | h | h | h <;> subst h
            · rw [lZ_vertici.1] at hz1; norm_num at hz1
            · rw [lZ_vertici.2.2.2.2.1] at hz1; norm_num at hz1
            · simp
            · simp
          have := span_coppia_le hsub
          omega)
      · -- SOLO a1 > 0: la faccia {y = 1}
        refine Or.inr (Or.inr (Or.inl ?_))
        rw [hFS]
        congr 1
        ext u
        constructor
        · intro huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hy1 := esclusione_yp l hy hu hmax
          rw [← argmax_verticiY1]
          exact ⟨hu, hy1⟩
        · intro huf
          have hcasi : u = c0 ∨ u = c4 ∨ u = c5 ∨ u = c1 := by
            simpa [facciaY1] using huf
          have hu : u ∈ (cubo.vertices : Set E3) := by
            rcases hcasi with h | h | h | h <;> subst h <;>
              simp [cubo, verticiCubo]
          refine (hcrit u hu).mpr ?_
          intro w hw
          rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
            h | h | h | h | h | h | h | h <;> subst h <;>
          rcases hcasi with h | h | h | h <;> subst h <;>
            simp only [l_c0, l_c1, l_c2, l_c3, l_c4, l_c5, l_c6, l_c7] <;>
            linarith
      · -- a1 > 0, a2 > 0 → S ⊆ {c0, c4}
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {c0, c4} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            have hy1 := esclusione_yp l hy hu hmax
            have hz1 := esclusione_zp l hz hu hmax
            have huy : u ∈ (facciaY1 : Set E3) := by
              rw [← argmax_verticiY1]; exact ⟨hu, hy1⟩
            have hcasi : u = c0 ∨ u = c4 ∨ u = c5 ∨ u = c1 := by
              simpa [facciaY1] using huy
            rcases hcasi with h | h | h | h <;> subst h
            · simp
            · simp
            · rw [lZ_vertici.2.2.2.2.2.1] at hz1; norm_num at hz1
            · rw [lZ_vertici.2.1] at hz1; norm_num at hz1
          have := span_coppia_le hsub
          omega)
  · -- a0 > 0
    rcases lt_trichotomy (compL l 1) 0 with hy | hy | hy
    · -- a0 > 0, a1 < 0 → S ⊆ {c2, c3}
      exact absurd hd (by
        have hsub : (S : Set E3) ⊆ {c2, c3} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hx1 := esclusione_xp l hx hu hmax
          have hy1 := esclusione_ym l hy hu hmax
          have hux : u ∈ (facciaX1 : Set E3) := by
            rw [← argmax_verticiX]; exact ⟨hu, hx1⟩
          have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
            simpa [facciaX1] using hux
          rcases hcasi with h | h | h | h <;> subst h
          · rw [lY_vertici.1] at hy1; norm_num at hy1
          · simp
          · simp
          · rw [lY_vertici.2.1] at hy1; norm_num at hy1
        have := span_coppia_le hsub
        omega)
    · -- a0 > 0, a1 = 0
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- a0 > 0, a2 < 0 → S ⊆ {c1, c3}
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {c1, c3} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            have hx1 := esclusione_xp l hx hu hmax
            have hz1 := esclusione_zm l hz hu hmax
            have hux : u ∈ (facciaX1 : Set E3) := by
              rw [← argmax_verticiX]; exact ⟨hu, hx1⟩
            have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
              simpa [facciaX1] using hux
            rcases hcasi with h | h | h | h <;> subst h
            · rw [lZ_vertici.1] at hz1; norm_num at hz1
            · rw [lZ_vertici.2.2.1] at hz1; norm_num at hz1
            · simp
            · simp
          have := span_coppia_le hsub
          omega)
      · -- SOLO a0 > 0: la faccia {x = 1}, identità
        refine Or.inl ?_
        rw [hFS]
        congr 1
        ext u
        constructor
        · intro huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hx1 := esclusione_xp l hx hu hmax
          rw [← argmax_verticiX]
          exact ⟨hu, hx1⟩
        · intro huf
          have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
            simpa [facciaX1] using huf
          have hu : u ∈ (cubo.vertices : Set E3) := by
            rcases hcasi with h | h | h | h <;> subst h <;>
              simp [cubo, verticiCubo]
          refine (hcrit u hu).mpr ?_
          intro w hw
          rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
            h | h | h | h | h | h | h | h <;> subst h <;>
          rcases hcasi with h | h | h | h <;> subst h <;>
            simp only [l_c0, l_c1, l_c2, l_c3, l_c4, l_c5, l_c6, l_c7] <;>
            linarith
      · -- a0 > 0, a2 > 0 → S ⊆ {c0, c2}
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {c0, c2} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            have hx1 := esclusione_xp l hx hu hmax
            have hz1 := esclusione_zp l hz hu hmax
            have hux : u ∈ (facciaX1 : Set E3) := by
              rw [← argmax_verticiX]; exact ⟨hu, hx1⟩
            have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
              simpa [facciaX1] using hux
            rcases hcasi with h | h | h | h <;> subst h
            · simp
            · simp
            · rw [lZ_vertici.2.2.2.1] at hz1; norm_num at hz1
            · rw [lZ_vertici.2.1] at hz1; norm_num at hz1
          have := span_coppia_le hsub
          omega)
    · -- a0 > 0, a1 > 0 → S ⊆ {c0, c1}
      exact absurd hd (by
        have hsub : (S : Set E3) ⊆ {c0, c1} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hx1 := esclusione_xp l hx hu hmax
          have hy1 := esclusione_yp l hy hu hmax
          have hux : u ∈ (facciaX1 : Set E3) := by
            rw [← argmax_verticiX]; exact ⟨hu, hx1⟩
          have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
            simpa [facciaX1] using hux
          rcases hcasi with h | h | h | h <;> subst h
          · simp
          · rw [lY_vertici.2.2.1] at hy1; norm_num at hy1
          · rw [lY_vertici.2.2.2.1] at hy1; norm_num at hy1
          · simp
        have := span_coppia_le hsub
        omega)

/-- TUTTE le faccette del cubo sono quadrati regolari di lato 2. -/
theorem cubo_faccette_regolari :
    ∀ F, cubo.IsFacet F → cubo.IsRegularFacet F 4 2 := by
  intro F hF
  rcases facet_classification_cubo hF with h | h | h | h | h | h <;> subst h
  · exact facciaX1_regolare
  · rw [← segnoX_F₀]
    exact isRegularFacet_image cubo _
      (preserva_toSet_di_vertici segnoX segnoX_vertset) facciaX1_regolare
  · rw [← scambioXY_F₀]
    exact isRegularFacet_image cubo _
      (preserva_toSet_di_vertici scambioXY scambioXY_vertset) facciaX1_regolare
  · rw [← portaYm_F₀]
    exact isRegularFacet_image cubo _
      (preserva_toSet_di_vertici portaYm portaYm_vertset) facciaX1_regolare
  · rw [← scambioXZ_F₀]
    exact isRegularFacet_image cubo _
      (preserva_toSet_di_vertici scambioXZ scambioXZ_vertset) facciaX1_regolare
  · rw [← portaZm_F₀]
    exact isRegularFacet_image cubo _
      (preserva_toSet_di_vertici portaZm portaZm_vertset) facciaX1_regolare

/-! ## Il 3-ciclo diagonale e i semispazi delle facce -/

def cicloCoord : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- La rotazione di 2π/3 attorno alla diagonale (1,1,1): (x,y,z) ↦ (z,x,y). -/
def rotDiag : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ cicloCoord

theorem rotDiag_vertici : rotDiag c0 = c0 ∧ rotDiag c1 = c4 ∧ rotDiag c2 = c1 ∧
    rotDiag c3 = c5 ∧ rotDiag c4 = c2 ∧ rotDiag c5 = c6 ∧ rotDiag c6 = c3 ∧
    rotDiag c7 = c7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [rotDiag, cicloCoord, c0, c1, c2, c3, c4, c5, c6, c7,
        LinearIsometryEquiv.piLpCongrLeft])

theorem rotDiag_vertset :
    (⇑rotDiag) '' (verticiCubo : Set E3) = (verticiCubo : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [rotDiag_vertici.1, rotDiag_vertici.2.1, rotDiag_vertici.2.2.1,
        rotDiag_vertici.2.2.2.1, rotDiag_vertici.2.2.2.2.1,
        rotDiag_vertici.2.2.2.2.2.1, rotDiag_vertici.2.2.2.2.2.2.1,
        rotDiag_vertici.2.2.2.2.2.2.2] <;>
      simp [verticiCubo]
  · intro hz
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exact ⟨c0, by simp [verticiCubo], rotDiag_vertici.1⟩
    · exact ⟨c2, by simp [verticiCubo], rotDiag_vertici.2.2.1⟩
    · exact ⟨c4, by simp [verticiCubo], rotDiag_vertici.2.2.2.2.1⟩
    · exact ⟨c6, by simp [verticiCubo], rotDiag_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨c1, by simp [verticiCubo], rotDiag_vertici.2.1⟩
    · exact ⟨c3, by simp [verticiCubo], rotDiag_vertici.2.2.2.1⟩
    · exact ⟨c5, by simp [verticiCubo], rotDiag_vertici.2.2.2.2.2.1⟩
    · exact ⟨c7, by simp [verticiCubo], rotDiag_vertici.2.2.2.2.2.2.2⟩

/-- rotDiag manda la faccia {x=1} sulla faccia {y=1}. -/
theorem rotDiag_X1 : (⇑rotDiag.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3))
    = convexHull ℝ (facciaY1 : Set E3) := by
  have haff : (⇑rotDiag.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3))
      = convexHull ℝ ((⇑rotDiag.toAffineIsometryEquiv) '' (facciaX1 : Set E3)) :=
    AffineMap.image_convexHull rotDiag.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑rotDiag.toAffineIsometryEquiv) u = rotDiag u := rfl
    rw [hcv]
    have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
      simpa [facciaX1] using hu
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [rotDiag_vertici.1, rotDiag_vertici.2.1, rotDiag_vertici.2.2.1,
        rotDiag_vertici.2.2.2.1] <;>
      simp [facciaY1]
  · intro hz
    have hcasi : z = c0 ∨ z = c4 ∨ z = c5 ∨ z = c1 := by
      simpa [facciaY1] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨c0, by simp [facciaX1], rotDiag_vertici.1⟩
    · exact ⟨c1, by simp [facciaX1], rotDiag_vertici.2.1⟩
    · exact ⟨c3, by simp [facciaX1], rotDiag_vertici.2.2.2.1⟩
    · exact ⟨c2, by simp [facciaX1], rotDiag_vertici.2.2.1⟩

/-- rotDiag manda la faccia {y=1} sulla faccia {z=1}. -/
theorem rotDiag_Y1 : (⇑rotDiag.toAffineIsometryEquiv) '' (convexHull ℝ (facciaY1 : Set E3))
    = convexHull ℝ (facciaZ1 : Set E3) := by
  have haff : (⇑rotDiag.toAffineIsometryEquiv) '' (convexHull ℝ (facciaY1 : Set E3))
      = convexHull ℝ ((⇑rotDiag.toAffineIsometryEquiv) '' (facciaY1 : Set E3)) :=
    AffineMap.image_convexHull rotDiag.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑rotDiag.toAffineIsometryEquiv) u = rotDiag u := rfl
    rw [hcv]
    have hcasi : u = c0 ∨ u = c4 ∨ u = c5 ∨ u = c1 := by
      simpa [facciaY1] using hu
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [rotDiag_vertici.1, rotDiag_vertici.2.2.2.2.1,
        rotDiag_vertici.2.2.2.2.2.1, rotDiag_vertici.2.1] <;>
      simp [facciaZ1]
  · intro hz
    have hcasi : z = c0 ∨ z = c2 ∨ z = c6 ∨ z = c4 := by
      simpa [facciaZ1] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨c0, by simp [facciaY1], rotDiag_vertici.1⟩
    · exact ⟨c4, by simp [facciaY1], rotDiag_vertici.2.2.2.2.1⟩
    · exact ⟨c5, by simp [facciaY1], rotDiag_vertici.2.2.2.2.2.1⟩
    · exact ⟨c1, by simp [facciaY1], rotDiag_vertici.2.1⟩

/-- rotDiag manda la faccia {z=1} sulla faccia {x=1}. -/
theorem rotDiag_Z1 : (⇑rotDiag.toAffineIsometryEquiv) '' (convexHull ℝ (facciaZ1 : Set E3))
    = convexHull ℝ (facciaX1 : Set E3) := by
  have haff : (⇑rotDiag.toAffineIsometryEquiv) '' (convexHull ℝ (facciaZ1 : Set E3))
      = convexHull ℝ ((⇑rotDiag.toAffineIsometryEquiv) '' (facciaZ1 : Set E3)) :=
    AffineMap.image_convexHull rotDiag.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑rotDiag.toAffineIsometryEquiv) u = rotDiag u := rfl
    rw [hcv]
    have hcasi : u = c0 ∨ u = c2 ∨ u = c6 ∨ u = c4 := by
      simpa [facciaZ1] using hu
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [rotDiag_vertici.1, rotDiag_vertici.2.2.1,
        rotDiag_vertici.2.2.2.2.2.2.1, rotDiag_vertici.2.2.2.2.1] <;>
      simp [facciaX1]
  · intro hz
    have hcasi : z = c0 ∨ z = c2 ∨ z = c3 ∨ z = c1 := by
      simpa [facciaX1] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨c0, by simp [facciaZ1], rotDiag_vertici.1⟩
    · exact ⟨c4, by simp [facciaZ1], rotDiag_vertici.2.2.2.2.1⟩
    · exact ⟨c6, by simp [facciaZ1], rotDiag_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨c2, by simp [facciaZ1], rotDiag_vertici.2.2.1⟩

/-! ## Semispazi per lY e lZ -/

theorem toSet_lY_le : ∀ z ∈ cubo.toSet, lY z ≤ 1 := by
  intro z hz
  have hsub : (verticiCubo : Set E3) ⊆ {w : E3 | lY w ≤ 1} := by
    intro w hw
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
      h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq] <;>
      first
        | (rw [lY_vertici.1])
        | (rw [lY_vertici.2.1])
        | (rw [lY_vertici.2.2.1]; norm_num)
        | (rw [lY_vertici.2.2.2.1]; norm_num)
        | (rw [lY_vertici.2.2.2.2.1])
        | (rw [lY_vertici.2.2.2.2.2.1])
        | (rw [lY_vertici.2.2.2.2.2.2.1]; norm_num)
        | (rw [lY_vertici.2.2.2.2.2.2.2]; norm_num)
  exact convexHull_min hsub
    (convex_halfSpace_le (LinearMap.isLinear lY.toLinearMap) 1) hz

theorem toSet_lZ_le : ∀ z ∈ cubo.toSet, lZ z ≤ 1 := by
  intro z hz
  have hsub : (verticiCubo : Set E3) ⊆ {w : E3 | lZ w ≤ 1} := by
    intro w hw
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
      h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq] <;>
      first
        | (rw [lZ_vertici.1])
        | (rw [lZ_vertici.2.1]; norm_num)
        | (rw [lZ_vertici.2.2.1])
        | (rw [lZ_vertici.2.2.2.1]; norm_num)
        | (rw [lZ_vertici.2.2.2.2.1])
        | (rw [lZ_vertici.2.2.2.2.2.1]; norm_num)
        | (rw [lZ_vertici.2.2.2.2.2.2.1])
        | (rw [lZ_vertici.2.2.2.2.2.2.2]; norm_num)
  exact convexHull_min hsub
    (convex_halfSpace_le (LinearMap.isLinear lZ.toLinearMap) 1) hz

theorem hullY1_ge : ∀ z ∈ convexHull ℝ (facciaY1 : Set E3), 1 ≤ lY z := by
  intro z hz
  have hsub : (facciaY1 : Set E3) ⊆ {w : E3 | 1 ≤ lY w} := by
    intro w hw
    have hcasi : w = c0 ∨ w = c4 ∨ w = c5 ∨ w = c1 := by
      simpa [facciaY1] using hw
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq]
    · rw [lY_vertici.1]
    · rw [lY_vertici.2.2.2.2.1]
    · rw [lY_vertici.2.2.2.2.2.1]
    · rw [lY_vertici.2.1]
  exact convexHull_min hsub
    (convex_halfSpace_ge (LinearMap.isLinear lY.toLinearMap) 1) hz

theorem hullZ1_ge : ∀ z ∈ convexHull ℝ (facciaZ1 : Set E3), 1 ≤ lZ z := by
  intro z hz
  have hsub : (facciaZ1 : Set E3) ⊆ {w : E3 | 1 ≤ lZ w} := by
    intro w hw
    have hcasi : w = c0 ∨ w = c2 ∨ w = c6 ∨ w = c4 := by
      simpa [facciaZ1] using hw
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq]
    · rw [lZ_vertici.1]
    · rw [lZ_vertici.2.2.1]
    · rw [lZ_vertici.2.2.2.2.2.2.1]
    · rw [lZ_vertici.2.2.2.2.1]
  exact convexHull_min hsub
    (convex_halfSpace_ge (LinearMap.isLinear lZ.toLinearMap) 1) hz

theorem hullXm_le : ∀ z ∈ convexHull ℝ (facciaXm : Set E3), lX z ≤ -1 := by
  intro z hz
  have hsub : (facciaXm : Set E3) ⊆ {w : E3 | lX w ≤ -1} := by
    intro w hw
    have hcasi : w = c4 ∨ w = c6 ∨ w = c7 ∨ w = c5 := by
      simpa [facciaXm] using hw
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq]
    · rw [lX_vertici.2.2.2.2.1]
    · rw [lX_vertici.2.2.2.2.2.2.1]
    · rw [lX_vertici.2.2.2.2.2.2.2]
    · rw [lX_vertici.2.2.2.2.2.1]
  exact convexHull_min hsub
    (convex_halfSpace_le (LinearMap.isLinear lX.toLinearMap) (-1)) hz

theorem hullYm_le : ∀ z ∈ convexHull ℝ (facciaYm : Set E3), lY z ≤ -1 := by
  intro z hz
  have hsub : (facciaYm : Set E3) ⊆ {w : E3 | lY w ≤ -1} := by
    intro w hw
    have hcasi : w = c2 ∨ w = c6 ∨ w = c7 ∨ w = c3 := by
      simpa [facciaYm] using hw
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq]
    · rw [lY_vertici.2.2.1]
    · rw [lY_vertici.2.2.2.2.2.2.1]
    · rw [lY_vertici.2.2.2.2.2.2.2]
    · rw [lY_vertici.2.2.2.1]
  exact convexHull_min hsub
    (convex_halfSpace_le (LinearMap.isLinear lY.toLinearMap) (-1)) hz

theorem hullZm_le : ∀ z ∈ convexHull ℝ (facciaZm : Set E3), lZ z ≤ -1 := by
  intro z hz
  have hsub : (facciaZm : Set E3) ⊆ {w : E3 | lZ w ≤ -1} := by
    intro w hw
    have hcasi : w = c1 ∨ w = c3 ∨ w = c7 ∨ w = c5 := by
      simpa [facciaZm] using hw
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq]
    · rw [lZ_vertici.2.1]
    · rw [lZ_vertici.2.2.2.1]
    · rw [lZ_vertici.2.2.2.2.2.2.2]
    · rw [lZ_vertici.2.2.2.2.2.1]
  exact convexHull_min hsub
    (convex_halfSpace_le (LinearMap.isLinear lZ.toLinearMap) (-1)) hz

/-- Le tre facce del fan stanno nel corpo del cubo. -/
theorem hullX1_sub : convexHull ℝ (facciaX1 : Set E3) ⊆ cubo.toSet := F₀_sub_toSet

theorem hullY1_sub : convexHull ℝ (facciaY1 : Set E3) ⊆ cubo.toSet := by
  apply convexHull_mono
  intro z hz
  have hcasi : z = c0 ∨ z = c4 ∨ z = c5 ∨ z = c1 := by
    simpa [facciaY1] using hz
  rcases hcasi with h | h | h | h <;> subst h <;> simp [cubo, verticiCubo]

theorem hullZ1_sub : convexHull ℝ (facciaZ1 : Set E3) ⊆ cubo.toSet := by
  apply convexHull_mono
  intro z hz
  have hcasi : z = c0 ∨ z = c2 ∨ z = c6 ∨ z = c4 := by
    simpa [facciaZ1] using hz
  rcases hcasi with h | h | h | h <;> subst h <;> simp [cubo, verticiCubo]

/-! ## L'argmax triplo: solo c0 ha tutte e tre le coordinate a 1 -/

theorem c0_ne_c4 : c0 ≠ c4 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 0) h
  simp [c0, c4] at this
  norm_num at this

theorem tre_uni_c0 : ∀ z ∈ cubo.toSet,
    lX z = 1 → lY z = 1 → lZ z = 1 → z = c0 := by
  intro z hz hx hy hzc
  have hz3 : (lX + lY + lZ) z = 3 := by
    simp only [ContinuousLinearMap.add_apply, hx, hy, hzc]
    norm_num
  have hmax : ∀ w ∈ cubo.toSet, (lX + lY + lZ) w ≤ (lX + lY + lZ) z := by
    intro w hw
    have h1 := toSet_le_uno w hw
    have h2 := toSet_lY_le w hw
    have h3 := toSet_lZ_le w hw
    rw [hz3]
    simp only [ContinuousLinearMap.add_apply]
    linarith
  have hL3 := faccia_argmax verticiCubo (lX + lY + lZ) hz hmax
  have hset : {x ∈ (verticiCubo : Set E3) | (lX + lY + lZ) x = (lX + lY + lZ) z}
      = {c0} := by
    rw [hz3]
    ext u
    constructor
    · rintro ⟨hu, hu3⟩
      simp only [ContinuousLinearMap.add_apply] at hu3
      rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
        h | h | h | h | h | h | h | h <;> subst h
      · rfl
      · rw [lX_vertici.2.1, lY_vertici.2.1, lZ_vertici.2.1] at hu3
        norm_num at hu3
      · rw [lX_vertici.2.2.1, lY_vertici.2.2.1, lZ_vertici.2.2.1] at hu3
        norm_num at hu3
      · rw [lX_vertici.2.2.2.1, lY_vertici.2.2.2.1, lZ_vertici.2.2.2.1] at hu3
        norm_num at hu3
      · rw [lX_vertici.2.2.2.2.1, lY_vertici.2.2.2.2.1,
          lZ_vertici.2.2.2.2.1] at hu3
        norm_num at hu3
      · rw [lX_vertici.2.2.2.2.2.1, lY_vertici.2.2.2.2.2.1,
          lZ_vertici.2.2.2.2.2.1] at hu3
        norm_num at hu3
      · rw [lX_vertici.2.2.2.2.2.2.1, lY_vertici.2.2.2.2.2.2.1,
          lZ_vertici.2.2.2.2.2.2.1] at hu3
        norm_num at hu3
      · rw [lX_vertici.2.2.2.2.2.2.2, lY_vertici.2.2.2.2.2.2.2,
          lZ_vertici.2.2.2.2.2.2.2] at hu3
        norm_num at hu3
    · intro hu
      have : u = c0 := hu
      subst this
      refine ⟨by simp [verticiCubo], ?_⟩
      simp only [ContinuousLinearMap.add_apply]
      rw [lX_vertici.1, lY_vertici.1, lZ_vertici.1]
      norm_num
  rw [hset] at hL3
  simpa using hL3

/-! ## Le tre facce del fan sono distinte -/

theorem X1_ne_Y1 : convexHull ℝ (facciaX1 : Set E3)
    ≠ convexHull ℝ (facciaY1 : Set E3) := by
  intro h
  have hc2 : c2 ∈ convexHull ℝ (facciaX1 : Set E3) :=
    subset_convexHull ℝ _ (by simp [facciaX1])
  rw [h] at hc2
  have := hullY1_ge c2 hc2
  rw [lY_vertici.2.2.1] at this
  norm_num at this

theorem X1_ne_Z1 : convexHull ℝ (facciaX1 : Set E3)
    ≠ convexHull ℝ (facciaZ1 : Set E3) := by
  intro h
  have hc1 : c1 ∈ convexHull ℝ (facciaX1 : Set E3) :=
    subset_convexHull ℝ _ (by simp [facciaX1])
  rw [h] at hc1
  have := hullZ1_ge c1 hc1
  rw [lZ_vertici.2.1] at this
  norm_num at this

theorem Y1_ne_Z1 : convexHull ℝ (facciaY1 : Set E3)
    ≠ convexHull ℝ (facciaZ1 : Set E3) := by
  intro h
  have hc5 : c5 ∈ convexHull ℝ (facciaY1 : Set E3) :=
    subset_convexHull ℝ _ (by simp [facciaY1])
  rw [h] at hc5
  have := hullZ1_ge c5 hc5
  rw [lZ_vertici.2.2.2.2.2.1] at this
  norm_num at this

/-! ## IL FAN DEL VERTICE c0 -/

set_option maxHeartbeats 800000 in
theorem c0_ciclico : cubo.IsCyclicVertex c0 3 := by
  refine ⟨⟨![convexHull ℝ (facciaX1 : Set E3), convexHull ℝ (facciaY1 : Set E3),
    convexHull ℝ (facciaZ1 : Set E3)], ?_, ?_, ?_, ?_,
    rotDiag.toAffineIsometryEquiv, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- isFacet
    intro i
    fin_cases i
    · exact facciaX1_isFacet
    · show cubo.IsFacet (convexHull ℝ (facciaY1 : Set E3))
      rw [← scambioXY_F₀]
      exact isFacet_image cubo _
        (preserva_toSet_di_vertici scambioXY scambioXY_vertset) facciaX1_isFacet
    · show cubo.IsFacet (convexHull ℝ (facciaZ1 : Set E3))
      rw [← scambioXZ_F₀]
      exact isFacet_image cubo _
        (preserva_toSet_di_vertici scambioXZ scambioXZ_vertset) facciaX1_isFacet
  · -- mem_v
    intro i
    fin_cases i
    · exact subset_convexHull ℝ _ (by simp [facciaX1])
    · exact subset_convexHull ℝ _ (by simp [facciaY1])
    · exact subset_convexHull ℝ _ (by simp [facciaZ1])
  · -- distinte
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij X1_ne_Y1
    · exact absurd hij X1_ne_Z1
    · exact absurd hij.symm X1_ne_Y1
    · rfl
    · exact absurd hij Y1_ne_Z1
    · exact absurd hij.symm X1_ne_Z1
    · exact absurd hij.symm Y1_ne_Z1
    · rfl
  · -- complete
    intro F hF hc0F
    rcases facet_classification_cubo hF with h | h | h | h | h | h <;> subst h
    · exact ⟨0, rfl⟩
    · exfalso
      have := hullXm_le c0 hc0F
      rw [lX_vertici.1] at this
      norm_num at this
    · exact ⟨1, rfl⟩
    · exfalso
      have := hullYm_le c0 hc0F
      rw [lY_vertici.1] at this
      norm_num at this
    · exact ⟨2, rfl⟩
    · exfalso
      have := hullZm_le c0 hc0F
      rw [lZ_vertici.1] at this
      norm_num at this
  · -- fissa_v
    exact rotDiag_vertici.1
  · -- preserva
    exact preserva_toSet_di_vertici rotDiag rotDiag_vertset
  · -- ruota
    intro i
    fin_cases i
    · have h1 : finRotate 3 (0 : Fin 3) = 1 := by decide
      show (⇑rotDiag.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3))
        = ![convexHull ℝ (facciaX1 : Set E3), convexHull ℝ (facciaY1 : Set E3),
            convexHull ℝ (facciaZ1 : Set E3)] (finRotate 3 0)
      rw [h1]
      exact rotDiag_X1
    · have h1 : finRotate 3 (1 : Fin 3) = 2 := by decide
      show (⇑rotDiag.toAffineIsometryEquiv) '' (convexHull ℝ (facciaY1 : Set E3))
        = ![convexHull ℝ (facciaX1 : Set E3), convexHull ℝ (facciaY1 : Set E3),
            convexHull ℝ (facciaZ1 : Set E3)] (finRotate 3 1)
      rw [h1]
      exact rotDiag_Y1
    · have h1 : finRotate 3 (2 : Fin 3) = 0 := by decide
      show (⇑rotDiag.toAffineIsometryEquiv) '' (convexHull ℝ (facciaZ1 : Set E3))
        = ![convexHull ℝ (facciaX1 : Set E3), convexHull ℝ (facciaY1 : Set E3),
            convexHull ℝ (facciaZ1 : Set E3)] (finRotate 3 2)
      rw [h1]
      exact rotDiag_Z1
  · -- spigolo
    intro i
    fin_cases i
    · refine ⟨c1, fun h => c0_ne_c1 h.symm, ?_⟩
      constructor
      · show c1 ∈ convexHull ℝ (facciaX1 : Set E3)
        exact subset_convexHull ℝ _ (by simp [facciaX1])
      · show c1 ∈ convexHull ℝ (facciaY1 : Set E3)
        exact subset_convexHull ℝ _ (by simp [facciaY1])
    · refine ⟨c4, fun h => c0_ne_c4 h.symm, ?_⟩
      constructor
      · show c4 ∈ convexHull ℝ (facciaY1 : Set E3)
        exact subset_convexHull ℝ _ (by simp [facciaY1])
      · show c4 ∈ convexHull ℝ (facciaZ1 : Set E3)
        exact subset_convexHull ℝ _ (by simp [facciaZ1])
    · refine ⟨c2, fun h => c0_ne_c2 h.symm, ?_⟩
      constructor
      · show c2 ∈ convexHull ℝ (facciaZ1 : Set E3)
        exact subset_convexHull ℝ _ (by simp [facciaZ1])
      · show c2 ∈ convexHull ℝ (facciaX1 : Set E3)
        exact subset_convexHull ℝ _ (by simp [facciaX1])
  · -- spigolo_due: un punto di spigolo diverso da c0 vive SOLO nelle due facce
    intro i j x hx hxv hxj
    fin_cases i <;> fin_cases j
    · exact Or.inl rfl
    · exact Or.inr (by decide)
    · exfalso
      have hx1 : x ∈ convexHull ℝ (facciaX1 : Set E3) := hx.1
      have hx2 : x ∈ convexHull ℝ (facciaY1 : Set E3) := hx.2
      have hx3 : x ∈ convexHull ℝ (facciaZ1 : Set E3) := hxj
      have hlx : lX x = 1 :=
        le_antisymm (toSet_le_uno x (hullX1_sub hx1)) (F₀_ge_uno x hx1)
      have hly : lY x = 1 :=
        le_antisymm (toSet_lY_le x (hullY1_sub hx2)) (hullY1_ge x hx2)
      have hlz : lZ x = 1 :=
        le_antisymm (toSet_lZ_le x (hullZ1_sub hx3)) (hullZ1_ge x hx3)
      exact hxv (tre_uni_c0 x (hullX1_sub hx1) hlx hly hlz)
    · exfalso
      have hx1 : x ∈ convexHull ℝ (facciaY1 : Set E3) := hx.1
      have hx2 : x ∈ convexHull ℝ (facciaZ1 : Set E3) := hx.2
      have hx3 : x ∈ convexHull ℝ (facciaX1 : Set E3) := hxj
      have hlx : lX x = 1 :=
        le_antisymm (toSet_le_uno x (hullX1_sub hx3)) (F₀_ge_uno x hx3)
      have hly : lY x = 1 :=
        le_antisymm (toSet_lY_le x (hullY1_sub hx1)) (hullY1_ge x hx1)
      have hlz : lZ x = 1 :=
        le_antisymm (toSet_lZ_le x (hullZ1_sub hx2)) (hullZ1_ge x hx2)
      exact hxv (tre_uni_c0 x (hullX1_sub hx3) hlx hly hlz)
    · exact Or.inl rfl
    · exact Or.inr (by decide)
    · exact Or.inr (by decide)
    · exfalso
      have hx1 : x ∈ convexHull ℝ (facciaZ1 : Set E3) := hx.1
      have hx2 : x ∈ convexHull ℝ (facciaX1 : Set E3) := hx.2
      have hx3 : x ∈ convexHull ℝ (facciaY1 : Set E3) := hxj
      have hlx : lX x = 1 :=
        le_antisymm (toSet_le_uno x (hullX1_sub hx2)) (F₀_ge_uno x hx2)
      have hly : lY x = 1 :=
        le_antisymm (toSet_lY_le x (hullY1_sub hx3)) (hullY1_ge x hx3)
      have hlz : lZ x = 1 :=
        le_antisymm (toSet_lZ_le x (hullZ1_sub hx1)) (hullZ1_ge x hx1)
      exact hxv (tre_uni_c0 x (hullX1_sub hx2) hlx hly hlz)
    · exact Or.inl rfl

/-! ## Gli otto vertici sono ciclici: simmetrie di segno e trasferimento -/

def segnoZ : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.refl ℝ ℝ, LinearIsometryEquiv.refl ℝ ℝ,
      LinearIsometryEquiv.neg ℝ]

theorem segnoY_vertici : segnoY c0 = c2 ∧ segnoY c1 = c3 ∧ segnoY c2 = c0 ∧
    segnoY c3 = c1 ∧ segnoY c4 = c6 ∧ segnoY c5 = c7 ∧ segnoY c6 = c4 ∧
    segnoY c7 = c5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [segnoY, c0, c1, c2, c3, c4, c5, c6, c7,
        LinearIsometryEquiv.piLpCongrRight])

theorem segnoZ_vertici : segnoZ c0 = c1 ∧ segnoZ c1 = c0 ∧ segnoZ c2 = c3 ∧
    segnoZ c3 = c2 ∧ segnoZ c4 = c5 ∧ segnoZ c5 = c4 ∧ segnoZ c6 = c7 ∧
    segnoZ c7 = c6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [segnoZ, c0, c1, c2, c3, c4, c5, c6, c7,
        LinearIsometryEquiv.piLpCongrRight])

theorem segnoY_vertset :
    (⇑segnoY) '' (verticiCubo : Set E3) = (verticiCubo : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [segnoY_vertici.1, segnoY_vertici.2.1, segnoY_vertici.2.2.1,
        segnoY_vertici.2.2.2.1, segnoY_vertici.2.2.2.2.1,
        segnoY_vertici.2.2.2.2.2.1, segnoY_vertici.2.2.2.2.2.2.1,
        segnoY_vertici.2.2.2.2.2.2.2] <;>
      simp [verticiCubo]
  · intro hz
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exact ⟨c2, by simp [verticiCubo], segnoY_vertici.2.2.1⟩
    · exact ⟨c3, by simp [verticiCubo], segnoY_vertici.2.2.2.1⟩
    · exact ⟨c0, by simp [verticiCubo], segnoY_vertici.1⟩
    · exact ⟨c1, by simp [verticiCubo], segnoY_vertici.2.1⟩
    · exact ⟨c6, by simp [verticiCubo], segnoY_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨c7, by simp [verticiCubo], segnoY_vertici.2.2.2.2.2.2.2⟩
    · exact ⟨c4, by simp [verticiCubo], segnoY_vertici.2.2.2.2.1⟩
    · exact ⟨c5, by simp [verticiCubo], segnoY_vertici.2.2.2.2.2.1⟩

theorem segnoZ_vertset :
    (⇑segnoZ) '' (verticiCubo : Set E3) = (verticiCubo : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [segnoZ_vertici.1, segnoZ_vertici.2.1, segnoZ_vertici.2.2.1,
        segnoZ_vertici.2.2.2.1, segnoZ_vertici.2.2.2.2.1,
        segnoZ_vertici.2.2.2.2.2.1, segnoZ_vertici.2.2.2.2.2.2.1,
        segnoZ_vertici.2.2.2.2.2.2.2] <;>
      simp [verticiCubo]
  · intro hz
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exact ⟨c1, by simp [verticiCubo], segnoZ_vertici.2.1⟩
    · exact ⟨c0, by simp [verticiCubo], segnoZ_vertici.1⟩
    · exact ⟨c3, by simp [verticiCubo], segnoZ_vertici.2.2.2.1⟩
    · exact ⟨c2, by simp [verticiCubo], segnoZ_vertici.2.2.1⟩
    · exact ⟨c5, by simp [verticiCubo], segnoZ_vertici.2.2.2.2.2.1⟩
    · exact ⟨c4, by simp [verticiCubo], segnoZ_vertici.2.2.2.2.1⟩
    · exact ⟨c7, by simp [verticiCubo], segnoZ_vertici.2.2.2.2.2.2.2⟩
    · exact ⟨c6, by simp [verticiCubo], segnoZ_vertici.2.2.2.2.2.2.1⟩

/-- La permutazione dei vertici passa alla composizione. -/
theorem vertset_trans (f g : E3 ≃ₗᵢ[ℝ] E3)
    (hf : (⇑f) '' (verticiCubo : Set E3) = (verticiCubo : Set E3))
    (hg : (⇑g) '' (verticiCubo : Set E3) = (verticiCubo : Set E3)) :
    (⇑(f.trans g)) '' (verticiCubo : Set E3) = (verticiCubo : Set E3) := by
  have hcomp : (⇑(f.trans g)) '' (verticiCubo : Set E3)
      = (⇑g) '' ((⇑f) '' (verticiCubo : Set E3)) := by
    rw [← Set.image_comp]
    rfl
  rw [hcomp, hf, hg]

/-- OGNI vertice del cubo è 3-ciclico. -/
theorem cubo_vertici_ciclici : ∀ v ∈ cubo.vertices, cubo.IsCyclicVertex v 3 := by
  intro v hv
  rcases mem_verticiCubo_iff.mp (by exact_mod_cast hv) with
    h | h | h | h | h | h | h | h <;> subst h
  · exact c0_ciclico
  · -- c1 = segnoZ c0
    have h1 : (segnoZ.toAffineIsometryEquiv) c0 = c1 := segnoZ_vertici.1
    rw [← h1]
    exact isCyclicVertex_image cubo _
      (preserva_toSet_di_vertici segnoZ segnoZ_vertset) c0_ciclico
  · -- c2 = segnoY c0
    have h1 : (segnoY.toAffineIsometryEquiv) c0 = c2 := segnoY_vertici.1
    rw [← h1]
    exact isCyclicVertex_image cubo _
      (preserva_toSet_di_vertici segnoY segnoY_vertset) c0_ciclico
  · -- c3 = (segnoY.trans segnoZ) c0
    have h1 : ((segnoY.trans segnoZ).toAffineIsometryEquiv) c0 = c3 := by
      show segnoZ (segnoY c0) = c3
      rw [segnoY_vertici.1, segnoZ_vertici.2.2.1]
    rw [← h1]
    exact isCyclicVertex_image cubo _
      (preserva_toSet_di_vertici _ (vertset_trans segnoY segnoZ
        segnoY_vertset segnoZ_vertset)) c0_ciclico
  · -- c4 = segnoX c0
    have h1 : (segnoX.toAffineIsometryEquiv) c0 = c4 := segnoX_vertici.1
    rw [← h1]
    exact isCyclicVertex_image cubo _
      (preserva_toSet_di_vertici segnoX segnoX_vertset) c0_ciclico
  · -- c5 = (segnoX.trans segnoZ) c0
    have h1 : ((segnoX.trans segnoZ).toAffineIsometryEquiv) c0 = c5 := by
      show segnoZ (segnoX c0) = c5
      rw [segnoX_vertici.1, segnoZ_vertici.2.2.2.2.1]
    rw [← h1]
    exact isCyclicVertex_image cubo _
      (preserva_toSet_di_vertici _ (vertset_trans segnoX segnoZ
        segnoX_vertset segnoZ_vertset)) c0_ciclico
  · -- c6 = (segnoX.trans segnoY) c0
    have h1 : ((segnoX.trans segnoY).toAffineIsometryEquiv) c0 = c6 := by
      show segnoY (segnoX c0) = c6
      rw [segnoX_vertici.1, segnoY_vertici.2.2.2.2.1]
    rw [← h1]
    exact isCyclicVertex_image cubo _
      (preserva_toSet_di_vertici _ (vertset_trans segnoX segnoY
        segnoX_vertset segnoY_vertset)) c0_ciclico
  · -- c7 = ((segnoX.trans segnoY).trans segnoZ) c0
    have h1 : (((segnoX.trans segnoY).trans segnoZ).toAffineIsometryEquiv) c0
        = c7 := by
      show segnoZ (segnoY (segnoX c0)) = c7
      rw [segnoX_vertici.1, segnoY_vertici.2.2.2.2.1,
        segnoZ_vertici.2.2.2.2.2.2.1]
    rw [← h1]
    exact isCyclicVertex_image cubo _
      (preserva_toSet_di_vertici _ (vertset_trans _ segnoZ
        (vertset_trans segnoX segnoY segnoX_vertset segnoY_vertset)
        segnoZ_vertset)) c0_ciclico

/-! ## IL TESTIMONE -/

/-- IL CUBO È CICLICAMENTE REGOLARE DI TIPO (4,3): il secondo testimone dei
cinque solidi, dopo il tetraedro (3,3). -/
theorem cubo_cyclicallyRegular : cubo.IsCyclicallyRegularOfType 4 3 :=
  ⟨cubo_finrank, by norm_num, by norm_num, 2, by norm_num,
    cubo_faccette_regolari, cubo_vertici_ciclici⟩
