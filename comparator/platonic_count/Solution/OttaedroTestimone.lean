import Mathlib
import Solution.Fondamenta
import Solution.TetraedroStadio2
import Solution.Trasferimento
import Solution.CuboTestimone

/-!
FASE 1B, N3 — L'OTTAEDRO (3,4), stadio 1 + faccetta regolare (18 lug, notte).
I sei vertici ±eᵢ sulla sfera unitaria; la faccia (+,+,+) è il triangolo
{o0,o1,o2}, esposta da lX+lY+lZ, ruotata dal 3-ciclo diagonale rotDiag
(ereditato dal cubo: la stessa rotazione serve entrambi i solidi).
-/

open Real Set Metric FiniteConvexPolytope PlatoniciL3
open scoped RealInnerProductSpace

noncomputable section

def o0 : E3 := WithLp.toLp 2 ![1, 0, 0]
def o1 : E3 := WithLp.toLp 2 ![0, 1, 0]
def o2 : E3 := WithLp.toLp 2 ![0, 0, 1]
def o3 : E3 := WithLp.toLp 2 ![-1, 0, 0]
def o4 : E3 := WithLp.toLp 2 ![0, -1, 0]
def o5 : E3 := WithLp.toLp 2 ![0, 0, -1]

open Classical in
def verticiOtta : Finset E3 := {o0, o1, o2, o3, o4, o5}

theorem mem_verticiOtta_iff {v : E3} : v ∈ verticiOtta ↔
    v = o0 ∨ v = o1 ∨ v = o2 ∨ v = o3 ∨ v = o4 ∨ v = o5 := by
  simp [verticiOtta]

theorem norm_vertici_otta : ∀ v ∈ verticiOtta, ‖v‖ = 1 := by
  intro v hv
  rcases mem_verticiOtta_iff.mp hv with h | h | h | h | h | h <;> subst h
  · show ‖(WithLp.toLp 2 ![(1:ℝ), 0, 0] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(0:ℝ), 1, 0] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(0:ℝ), 0, 1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(-1:ℝ), 0, 0] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(0:ℝ), -1, 0] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(0:ℝ), 0, -1] : E3)‖ = _
    rw [norma_toLp]; norm_num

/-- L'OTTAEDRO (stadio 1): politopo convesso finito legittimo. -/
def ottaedro : FiniteConvexPolytope E3 where
  vertices := verticiOtta
  nonempty := ⟨o0, by simp [verticiOtta]⟩
  vertices_eq_extremePoints := by
    have hV : (verticiOtta : Set E3) ⊆ Metric.sphere 0 1 := by
      intro v hv
      rw [mem_sphere_zero_iff_norm]
      exact norm_vertici_otta v (by exact_mod_cast hv)
    exact (cosferico_extremePoints 0 1 _ hV).symm

/-! ## Il funzionale della faccia (+,+,+) e i suoi valori -/

theorem lS_vertici_otta : (lX + lY + lZ) o0 = 1 ∧ (lX + lY + lZ) o1 = 1 ∧
    (lX + lY + lZ) o2 = 1 ∧ (lX + lY + lZ) o3 = -1 ∧
    (lX + lY + lZ) o4 = -1 ∧ (lX + lY + lZ) o5 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [ContinuousLinearMap.add_apply]; norm_num [lX, lY, lZ, o0, o1,
      o2, o3, o4, o5]) <;>
    rfl

def facciaOtta : Finset E3 := {o0, o1, o2}

/-- Il triangolo della faccia (+,+,+). -/
def T₀ : Set E3 := convexHull ℝ (facciaOtta : Set E3)

theorem argmax_verticiOtta :
    {x ∈ (verticiOtta : Set E3) | (lX + lY + lZ) x = 1}
      = (facciaOtta : Set E3) := by
  ext z
  constructor
  · rintro ⟨hz, hlz⟩
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h <;> subst h
    · simp [facciaOtta]
    · simp [facciaOtta]
    · simp [facciaOtta]
    · exfalso; rw [lS_vertici_otta.2.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lS_vertici_otta.2.2.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lS_vertici_otta.2.2.2.2.2] at hlz; norm_num at hlz
  · intro hz
    have hcasi : z = o0 ∨ z = o1 ∨ z = o2 := by
      simpa [facciaOtta] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨by simp [verticiOtta], lS_vertici_otta.1⟩
    · exact ⟨by simp [verticiOtta], lS_vertici_otta.2.1⟩
    · exact ⟨by simp [verticiOtta], lS_vertici_otta.2.2.1⟩

theorem toSet_otta_le : ∀ z ∈ ottaedro.toSet, (lX + lY + lZ) z ≤ 1 := by
  intro z hz
  have hsub : (verticiOtta : Set E3) ⊆ {w : E3 | (lX + lY + lZ) w ≤ 1} := by
    intro w hw
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hw) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq] <;>
      first
        | (rw [lS_vertici_otta.1])
        | (rw [lS_vertici_otta.2.1])
        | (rw [lS_vertici_otta.2.2.1])
        | (rw [lS_vertici_otta.2.2.2.1]; norm_num)
        | (rw [lS_vertici_otta.2.2.2.2.1]; norm_num)
        | (rw [lS_vertici_otta.2.2.2.2.2]; norm_num)
  exact convexHull_min hsub
    (convex_halfSpace_le (LinearMap.isLinear (lX + lY + lZ).toLinearMap) 1) hz

theorem T₀_ge_uno : ∀ z ∈ T₀, 1 ≤ (lX + lY + lZ) z := by
  intro z hz
  have hsub : (facciaOtta : Set E3) ⊆ {w : E3 | 1 ≤ (lX + lY + lZ) w} := by
    intro w hw
    have hcasi : w = o0 ∨ w = o1 ∨ w = o2 := by
      simpa [facciaOtta] using hw
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq]
    · rw [lS_vertici_otta.1]
    · rw [lS_vertici_otta.2.1]
    · rw [lS_vertici_otta.2.2.1]
  exact convexHull_min hsub
    (convex_halfSpace_ge (LinearMap.isLinear (lX + lY + lZ).toLinearMap) 1) hz

theorem T₀_sub_toSet : T₀ ⊆ ottaedro.toSet := by
  apply convexHull_mono
  intro z hz
  have hcasi : z = o0 ∨ z = o1 ∨ z = o2 := by
    simpa [facciaOtta] using hz
  rcases hcasi with h | h | h <;> subst h <;> simp [ottaedro, verticiOtta]

/-- L'ESPOSIZIONE della faccia (+,+,+). -/
theorem facciaOtta_esposta : IsExposed ℝ ottaedro.toSet T₀ := by
  intro _
  refine ⟨lX + lY + lZ, ?_⟩
  ext z
  constructor
  · intro hz
    have hz1 : (lX + lY + lZ) z = 1 := le_antisymm
      (toSet_otta_le z (T₀_sub_toSet hz)) (T₀_ge_uno z hz)
    refine ⟨T₀_sub_toSet hz, ?_⟩
    intro y hy
    rw [hz1]
    exact toSet_otta_le y hy
  · rintro ⟨hzS, hzmax⟩
    have ho0S : o0 ∈ ottaedro.toSet := by
      apply subset_convexHull
      simp [ottaedro, verticiOtta]
    have hz1 : (lX + lY + lZ) z = 1 := by
      have h1 := hzmax o0 ho0S
      rw [lS_vertici_otta.1] at h1
      exact le_antisymm (toSet_otta_le z hzS) h1
    have hL3 := faccia_argmax verticiOtta (lX + lY + lZ) hzS
      (fun w hw => hzmax w hw)
    have hset : {x ∈ (verticiOtta : Set E3) | (lX + lY + lZ) x
        = (lX + lY + lZ) z} = (facciaOtta : Set E3) := by
      rw [hz1]
      exact argmax_verticiOtta
    rw [hset] at hL3
    exact hL3

/-! ## Il ciclo di rotDiag sulla faccia e la regolarità -/

theorem rotDiag_o : rotDiag o0 = o1 ∧ rotDiag o1 = o2 ∧ rotDiag o2 = o0 ∧
    rotDiag o3 = o4 ∧ rotDiag o4 = o5 ∧ rotDiag o5 = o3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [rotDiag, cicloCoord, o0, o1, o2, o3, o4, o5,
        LinearIsometryEquiv.piLpCongrLeft])

theorem o0_ne_o1 : o0 ≠ o1 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 0) h
  simp [o0, o1] at this

theorem o0_ne_o2 : o0 ≠ o2 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 0) h
  simp [o0, o2] at this

theorem o1_ne_o2 : o1 ≠ o2 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 1) h
  simp [o1, o2] at this

theorem orbita_otta : ∀ i : Fin 3,
    (⇑rotDiag.toAffineIsometryEquiv)^[(i : ℕ)] o0 = ![o0, o1, o2] i := by
  intro i
  fin_cases i
  · rfl
  · show rotDiag o0 = o1
    exact rotDiag_o.1
  · show rotDiag (rotDiag o0) = o2
    rw [rotDiag_o.1, rotDiag_o.2.1]

theorem ciclo_otta_chiuso : (⇑rotDiag.toAffineIsometryEquiv)^[3] o0 = o0 := by
  show rotDiag (rotDiag (rotDiag o0)) = o0
  rw [rotDiag_o.1, rotDiag_o.2.1, rotDiag_o.2.2.1]

theorem ciclo_otta_iniettivo : Function.Injective
    (fun i : Fin 3 => (⇑rotDiag.toAffineIsometryEquiv)^[(i : ℕ)] o0) := by
  intro i j hij
  have hij' : (⇑rotDiag.toAffineIsometryEquiv)^[(i : ℕ)] o0
      = (⇑rotDiag.toAffineIsometryEquiv)^[(j : ℕ)] o0 := hij
  rw [orbita_otta i, orbita_otta j] at hij'
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (exfalso; revert hij'; simp only []
       first
         | exact fun h => o0_ne_o1 h
         | exact fun h => o0_ne_o2 h
         | exact fun h => o1_ne_o2 h
         | exact fun h => o0_ne_o1 h.symm
         | exact fun h => o0_ne_o2 h.symm
         | exact fun h => o1_ne_o2 h.symm)

theorem range_orbita_otta :
    Set.range (fun i : Fin 3 => (⇑rotDiag.toAffineIsometryEquiv)^[(i : ℕ)] o0)
      = (facciaOtta : Set E3) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    show (⇑rotDiag.toAffineIsometryEquiv)^[(i : ℕ)] o0 ∈ (facciaOtta : Set E3)
    rw [orbita_otta i]
    fin_cases i
    · simp [facciaOtta]
    · simp [facciaOtta]
    · simp [facciaOtta]
  · intro hz
    have hcasi : z = o0 ∨ z = o1 ∨ z = o2 := by
      simpa [facciaOtta] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨0, orbita_otta 0⟩
    · exact ⟨1, orbita_otta 1⟩
    · exact ⟨2, orbita_otta 2⟩

theorem lato_otta : dist o0 (rotDiag.toAffineIsometryEquiv o0) = Real.sqrt 2 := by
  show dist o0 (rotDiag o0) = _
  rw [rotDiag_o.1, dist_eq_norm]
  have hsub : o0 - o1 = WithLp.toLp 2 ![1, -1, 0] := by
    ext j <;> fin_cases j <;> simp [o0, o1] <;> norm_num
  rw [hsub, norma_toLp]
  norm_num

theorem rotDiag_preserva_T₀ : (⇑rotDiag.toAffineIsometryEquiv) '' T₀ = T₀ := by
  show (⇑rotDiag.toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3)) = _
  have haff : (⇑rotDiag.toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3))
      = convexHull ℝ ((⇑rotDiag.toAffineIsometryEquiv) '' (facciaOtta : Set E3)) :=
    AffineMap.image_convexHull rotDiag.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑rotDiag.toAffineIsometryEquiv) u = rotDiag u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
      simpa [facciaOtta] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [rotDiag_o.1, rotDiag_o.2.1, rotDiag_o.2.2.1] <;>
      simp [facciaOtta]
  · intro hz
    have hcasi : z = o0 ∨ z = o1 ∨ z = o2 := by
      simpa [facciaOtta] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o2, by simp [facciaOtta], rotDiag_o.2.2.1⟩
    · exact ⟨o0, by simp [facciaOtta], rotDiag_o.1⟩
    · exact ⟨o1, by simp [facciaOtta], rotDiag_o.2.1⟩

/-! ## Lo span 2D della faccia -/

theorem lS_su_facciaOtta : ∀ u ∈ (facciaOtta : Set E3), (lX + lY + lZ) u = 1 := by
  intro u hu
  rw [← argmax_verticiOtta] at hu
  exact hu.2

theorem span_le_ker_otta : vectorSpan ℝ (facciaOtta : Set E3)
    ≤ LinearMap.ker (lX + lY + lZ).toLinearMap := by
  show Submodule.span ℝ ((facciaOtta : Set E3) -ᵥ (facciaOtta : Set E3)) ≤ _
  rw [Submodule.span_le]
  rintro d ⟨u, hu, v, hv, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  show (lX + lY + lZ) (u -ᵥ v) = 0
  rw [vsub_eq_sub, map_sub, lS_su_facciaOtta u hu, lS_su_facciaOtta v hv,
    sub_self]

theorem finrank_ker_lS :
    Module.finrank ℝ (LinearMap.ker (lX + lY + lZ).toLinearMap) = 2 := by
  have hsurj : Function.Surjective (lX + lY + lZ).toLinearMap := by
    intro t
    refine ⟨t • o0, ?_⟩
    rw [map_smul]
    show t • (lX + lY + lZ) o0 = t
    rw [lS_vertici_otta.1, smul_eq_mul, mul_one]
  have hrn := LinearMap.finrank_range_add_finrank_ker (lX + lY + lZ).toLinearMap
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrn
  have hE3 : Module.finrank ℝ E3 = 3 := by
    simp [E3]
  rw [hE3] at hrn
  have hR : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ
  omega

noncomputable def dOtta1 : E3 := o0 - o1
noncomputable def dOtta2 : E3 := o0 - o2

theorem indep_dOtta : LinearIndependent ℝ ![dOtta1, dOtta2] := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have := congrArg (fun v : E3 => (WithLp.ofLp v) 2) h
    simp [dOtta2, o0, o2] at this
  · intro a h
    have := congrArg (fun v : E3 => (WithLp.ofLp v) 1) h
    simp [dOtta1, dOtta2, o0, o1, o2] at this

theorem finrank_span_facciaOtta :
    Module.finrank ℝ (vectorSpan ℝ (facciaOtta : Set E3)) = 2 := by
  refine le_antisymm ?_ ?_
  · calc Module.finrank ℝ (vectorSpan ℝ (facciaOtta : Set E3))
        ≤ Module.finrank ℝ (LinearMap.ker (lX + lY + lZ).toLinearMap) :=
          Submodule.finrank_mono span_le_ker_otta
      _ = 2 := finrank_ker_lS
  · have hsub : Submodule.span ℝ (Set.range ![dOtta1, dOtta2])
        ≤ vectorSpan ℝ (facciaOtta : Set E3) := by
      rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      fin_cases i
      · have hm := vsub_mem_vectorSpan ℝ
          (show o0 ∈ (facciaOtta : Set E3) by simp [facciaOtta])
          (show o1 ∈ (facciaOtta : Set E3) by simp [facciaOtta])
        simpa [dOtta1, vsub_eq_sub] using hm
      · have hm := vsub_mem_vectorSpan ℝ
          (show o0 ∈ (facciaOtta : Set E3) by simp [facciaOtta])
          (show o2 ∈ (facciaOtta : Set E3) by simp [facciaOtta])
        simpa [dOtta2, vsub_eq_sub] using hm
    have h2 : Module.finrank ℝ (Submodule.span ℝ (Set.range ![dOtta1, dOtta2]))
        = 2 := by
      rw [finrank_span_eq_card indep_dOtta]
      simp
    calc (2 : ℕ) = Module.finrank ℝ (Submodule.span ℝ
          (Set.range ![dOtta1, dOtta2])) := h2.symm
      _ ≤ Module.finrank ℝ (vectorSpan ℝ (facciaOtta : Set E3)) :=
          Submodule.finrank_mono hsub

theorem span_T₀ : vectorSpan ℝ T₀ = vectorSpan ℝ (facciaOtta : Set E3) := by
  show vectorSpan ℝ (convexHull ℝ (facciaOtta : Set E3)) = _
  rw [← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]

theorem T₀_nonempty : T₀.Nonempty :=
  ⟨o0, subset_convexHull ℝ _ (by simp [facciaOtta])⟩

theorem o0_mem_T₀ : o0 ∈ T₀ :=
  subset_convexHull ℝ _ (by simp [facciaOtta])

theorem facciaOtta_isFacet : ottaedro.IsFacet T₀ :=
  ⟨⟨facciaOtta_esposta, T₀_nonempty⟩, by rw [span_T₀]; exact finrank_span_facciaOtta⟩

theorem T₀_eq_hull_orbita : T₀ = convexHull ℝ
    (Set.range fun i : Fin 3 => (⇑rotDiag.toAffineIsometryEquiv)^[(i : ℕ)] o0) := by
  rw [range_orbita_otta]
  rfl

/-- LA FACCETTA REGOLARE dell'ottaedro: triangolo di lato √2. -/
theorem facciaOtta_regolare : ottaedro.IsRegularFacet T₀ 3 (Real.sqrt 2) :=
  ⟨facciaOtta_isFacet, by positivity, by norm_num,
    rotDiag.toAffineIsometryEquiv, o0, o0_mem_T₀, rotDiag_preserva_T₀,
    ciclo_otta_iniettivo, ciclo_otta_chiuso, T₀_eq_hull_orbita, lato_otta⟩

/-! ## La dimensione globale e il lemma dei vertici esposti -/

theorem ottaedro_finrank :
    Module.finrank ℝ (vectorSpan ℝ (ottaedro.vertices : Set E3)) = 3 := by
  have ho0 : o0 ∈ (ottaedro.vertices : Set E3) := by simp [ottaedro, verticiOtta]
  have ho1 : o1 ∈ (ottaedro.vertices : Set E3) := by simp [ottaedro, verticiOtta]
  have ho2 : o2 ∈ (ottaedro.vertices : Set E3) := by simp [ottaedro, verticiOtta]
  have ho3 : o3 ∈ (ottaedro.vertices : Set E3) := by simp [ottaedro, verticiOtta]
  have ho4 : o4 ∈ (ottaedro.vertices : Set E3) := by simp [ottaedro, verticiOtta]
  have ho5 : o5 ∈ (ottaedro.vertices : Set E3) := by simp [ottaedro, verticiOtta]
  have htop : vectorSpan ℝ (ottaedro.vertices : Set E3) = ⊤ := by
    apply le_antisymm le_top
    rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.span_eq, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    all_goals simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      SetLike.mem_coe]
    · show EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
        ∈ vectorSpan ℝ (ottaedro.vertices : Set E3)
      have hd : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
          = (2⁻¹ : ℝ) • (o0 -ᵥ o3) := by
        ext j <;> fin_cases j <;>
          simp [o0, o3, EuclideanSpace.single_apply] <;> norm_num
      rw [hd]
      exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ ho0 ho3)
    · show EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
        ∈ vectorSpan ℝ (ottaedro.vertices : Set E3)
      have hd : (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
          = (2⁻¹ : ℝ) • (o1 -ᵥ o4) := by
        ext j <;> fin_cases j <;>
          simp [o1, o4, EuclideanSpace.single_apply] <;> norm_num
      rw [hd]
      exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ ho1 ho4)
    · show EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
        ∈ vectorSpan ℝ (ottaedro.vertices : Set E3)
      have hd : (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
          = (2⁻¹ : ℝ) • (o2 -ᵥ o5) := by
        ext j <;> fin_cases j <;>
          simp [o2, o5, EuclideanSpace.single_apply] <;> norm_num
      rw [hd]
      exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ ho2 ho5)
  rw [htop, finrank_top]
  simp [E3]

open Classical in
/-- Ogni faccia esposta dell'ottaedro è l'hull dei vertici che contiene. -/
theorem exposedFace_eq_convexHull_vertices_otta {F : Set E3}
    (hF : ottaedro.IsFace F) :
    F = convexHull ℝ ((ottaedro.vertices.filter (· ∈ F) : Finset E3) : Set E3) := by
  classical
  let S : Finset E3 := ottaedro.vertices.filter (· ∈ F)
  have hPcompact : IsCompact ottaedro.toSet :=
    (ottaedro.vertices.finite_toSet.isCompact_convexHull ℝ)
  have hFcompact : IsCompact F := hF.1.isCompact hPcompact
  have hFconvex : Convex ℝ F := hF.1.convex (convex_convexHull ℝ _)
  have hKM := closure_convexHull_extremePoints hFcompact hFconvex
  have hext : F.extremePoints ℝ = (S : Set E3) := by
    rw [hF.1.isExtreme.extremePoints_eq]
    ext x
    simp only [S, Finset.mem_coe, Finset.mem_filter, mem_inter_iff]
    change (x ∈ F ∧ x ∈ ottaedro.toSet.extremePoints ℝ) ↔
      x ∈ ottaedro.vertices ∧ x ∈ F
    rw [FiniteConvexPolytope.toSet, ← ottaedro.vertices_eq_extremePoints]
    tauto
  calc
    F = closure (convexHull ℝ (F.extremePoints ℝ)) := hKM.symm
    _ = closure (convexHull ℝ (S : Set E3)) := by rw [hext]
    _ = convexHull ℝ (S : Set E3) :=
      (S.finite_toSet.isClosed_convexHull ℝ).closure_eq
    _ = convexHull ℝ
        ((ottaedro.vertices.filter (· ∈ F) : Finset E3) : Set E3) := rfl

/-! ## I valori di un funzionale generico sui sei vertici -/

section ClassOtta

variable (l : E3 →L[ℝ] ℝ)

theorem l_o0 : l o0 = compL l 0 := by
  show l (WithLp.toLp 2 ![1, 0, 0]) = _
  rw [l_toLp3]; ring

theorem l_o1 : l o1 = compL l 1 := by
  show l (WithLp.toLp 2 ![0, 1, 0]) = _
  rw [l_toLp3]; ring

theorem l_o2 : l o2 = compL l 2 := by
  show l (WithLp.toLp 2 ![0, 0, 1]) = _
  rw [l_toLp3]; ring

theorem l_o3 : l o3 = -compL l 0 := by
  show l (WithLp.toLp 2 ![-1, 0, 0]) = _
  rw [l_toLp3]; ring

theorem l_o4 : l o4 = -compL l 1 := by
  show l (WithLp.toLp 2 ![0, -1, 0]) = _
  rw [l_toLp3]; ring

theorem l_o5 : l o5 = -compL l 2 := by
  show l (WithLp.toLp 2 ![0, 0, -1]) = _
  rw [l_toLp3]; ring

end ClassOtta

/-! ## Le azioni dei segni sui vertici dell'ottaedro -/

theorem segnoX_o : segnoX o0 = o3 ∧ segnoX o1 = o1 ∧ segnoX o2 = o2 ∧
    segnoX o3 = o0 ∧ segnoX o4 = o4 ∧ segnoX o5 = o5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [segnoX, o0, o1, o2, o3, o4, o5,
        LinearIsometryEquiv.piLpCongrRight])

theorem segnoY_o : segnoY o0 = o0 ∧ segnoY o1 = o4 ∧ segnoY o2 = o2 ∧
    segnoY o3 = o3 ∧ segnoY o4 = o1 ∧ segnoY o5 = o5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [segnoY, o0, o1, o2, o3, o4, o5,
        LinearIsometryEquiv.piLpCongrRight])

theorem segnoZ_o : segnoZ o0 = o0 ∧ segnoZ o1 = o1 ∧ segnoZ o2 = o5 ∧
    segnoZ o3 = o3 ∧ segnoZ o4 = o4 ∧ segnoZ o5 = o2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [segnoZ, o0, o1, o2, o3, o4, o5,
        LinearIsometryEquiv.piLpCongrRight])

theorem segnoX_overtset :
    (⇑segnoX) '' (verticiOtta : Set E3) = (verticiOtta : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [segnoX_o.1, segnoX_o.2.1, segnoX_o.2.2.1, segnoX_o.2.2.2.1,
        segnoX_o.2.2.2.2.1, segnoX_o.2.2.2.2.2] <;>
      simp [verticiOtta]
  · intro hz
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h <;> subst h
    · exact ⟨o3, by simp [verticiOtta], segnoX_o.2.2.2.1⟩
    · exact ⟨o1, by simp [verticiOtta], segnoX_o.2.1⟩
    · exact ⟨o2, by simp [verticiOtta], segnoX_o.2.2.1⟩
    · exact ⟨o0, by simp [verticiOtta], segnoX_o.1⟩
    · exact ⟨o4, by simp [verticiOtta], segnoX_o.2.2.2.2.1⟩
    · exact ⟨o5, by simp [verticiOtta], segnoX_o.2.2.2.2.2⟩

theorem segnoY_overtset :
    (⇑segnoY) '' (verticiOtta : Set E3) = (verticiOtta : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [segnoY_o.1, segnoY_o.2.1, segnoY_o.2.2.1, segnoY_o.2.2.2.1,
        segnoY_o.2.2.2.2.1, segnoY_o.2.2.2.2.2] <;>
      simp [verticiOtta]
  · intro hz
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h <;> subst h
    · exact ⟨o0, by simp [verticiOtta], segnoY_o.1⟩
    · exact ⟨o4, by simp [verticiOtta], segnoY_o.2.2.2.2.1⟩
    · exact ⟨o2, by simp [verticiOtta], segnoY_o.2.2.1⟩
    · exact ⟨o3, by simp [verticiOtta], segnoY_o.2.2.2.1⟩
    · exact ⟨o1, by simp [verticiOtta], segnoY_o.2.1⟩
    · exact ⟨o5, by simp [verticiOtta], segnoY_o.2.2.2.2.2⟩

theorem segnoZ_overtset :
    (⇑segnoZ) '' (verticiOtta : Set E3) = (verticiOtta : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [segnoZ_o.1, segnoZ_o.2.1, segnoZ_o.2.2.1, segnoZ_o.2.2.2.1,
        segnoZ_o.2.2.2.2.1, segnoZ_o.2.2.2.2.2] <;>
      simp [verticiOtta]
  · intro hz
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h <;> subst h
    · exact ⟨o0, by simp [verticiOtta], segnoZ_o.1⟩
    · exact ⟨o1, by simp [verticiOtta], segnoZ_o.2.1⟩
    · exact ⟨o5, by simp [verticiOtta], segnoZ_o.2.2.2.2.2⟩
    · exact ⟨o3, by simp [verticiOtta], segnoZ_o.2.2.2.1⟩
    · exact ⟨o4, by simp [verticiOtta], segnoZ_o.2.2.2.2.1⟩
    · exact ⟨o2, by simp [verticiOtta], segnoZ_o.2.2.1⟩

/-- La permutazione dei vertici dell'ottaedro passa alla composizione. -/
theorem overtset_trans (f g : E3 ≃ₗᵢ[ℝ] E3)
    (hf : (⇑f) '' (verticiOtta : Set E3) = (verticiOtta : Set E3))
    (hg : (⇑g) '' (verticiOtta : Set E3) = (verticiOtta : Set E3)) :
    (⇑(f.trans g)) '' (verticiOtta : Set E3) = (verticiOtta : Set E3) := by
  have hcomp : (⇑(f.trans g)) '' (verticiOtta : Set E3)
      = (⇑g) '' ((⇑f) '' (verticiOtta : Set E3)) := by
    rw [← Set.image_comp]
    rfl
  rw [hcomp, hf, hg]

/-- Se un'isometria lineare permuta i vertici dell'ottaedro, la versione
affine preserva il corpo. -/
theorem preserva_toSet_otta (g : E3 ≃ₗᵢ[ℝ] E3)
    (hv : (⇑g) '' (verticiOtta : Set E3) = (verticiOtta : Set E3)) :
    (⇑g.toAffineIsometryEquiv) '' ottaedro.toSet = ottaedro.toSet := by
  show (⇑g.toAffineIsometryEquiv) '' (convexHull ℝ (verticiOtta : Set E3))
    = convexHull ℝ (verticiOtta : Set E3)
  have haff : (⇑g.toAffineIsometryEquiv) '' (convexHull ℝ (verticiOtta : Set E3))
      = convexHull ℝ ((⇑g.toAffineIsometryEquiv) '' (verticiOtta : Set E3)) :=
    AffineMap.image_convexHull g.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff, show (⇑g.toAffineIsometryEquiv) '' (verticiOtta : Set E3)
    = (verticiOtta : Set E3) from hv]

/-! ## Le otto facce dell'ottaedro e le immagini di T₀ -/

def fmpp : Finset E3 := {o3, o1, o2}
def fpmp : Finset E3 := {o0, o4, o2}
def fppm : Finset E3 := {o0, o1, o5}
def fmmp : Finset E3 := {o3, o4, o2}
def fmpm : Finset E3 := {o3, o1, o5}
def fpmm : Finset E3 := {o0, o4, o5}
def fmmm : Finset E3 := {o3, o4, o5}

theorem sXY_o : (segnoX.trans segnoY) o0 = o3 ∧ (segnoX.trans segnoY) o1 = o4
    ∧ (segnoX.trans segnoY) o2 = o2 := by
  refine ⟨?_, ?_, ?_⟩
  · show segnoY (segnoX o0) = o3
    rw [segnoX_o.1, segnoY_o.2.2.2.1]
  · show segnoY (segnoX o1) = o4
    rw [segnoX_o.2.1, segnoY_o.2.1]
  · show segnoY (segnoX o2) = o2
    rw [segnoX_o.2.2.1, segnoY_o.2.2.1]

theorem sXZ_o : (segnoX.trans segnoZ) o0 = o3 ∧ (segnoX.trans segnoZ) o1 = o1
    ∧ (segnoX.trans segnoZ) o2 = o5 := by
  refine ⟨?_, ?_, ?_⟩
  · show segnoZ (segnoX o0) = o3
    rw [segnoX_o.1, segnoZ_o.2.2.2.1]
  · show segnoZ (segnoX o1) = o1
    rw [segnoX_o.2.1, segnoZ_o.2.1]
  · show segnoZ (segnoX o2) = o5
    rw [segnoX_o.2.2.1, segnoZ_o.2.2.1]

theorem sYZ_o : (segnoY.trans segnoZ) o0 = o0 ∧ (segnoY.trans segnoZ) o1 = o4
    ∧ (segnoY.trans segnoZ) o2 = o5 := by
  refine ⟨?_, ?_, ?_⟩
  · show segnoZ (segnoY o0) = o0
    rw [segnoY_o.1, segnoZ_o.1]
  · show segnoZ (segnoY o1) = o4
    rw [segnoY_o.2.1, segnoZ_o.2.2.2.2.1]
  · show segnoZ (segnoY o2) = o5
    rw [segnoY_o.2.2.1, segnoZ_o.2.2.1]

theorem sXYZ_o : ((segnoX.trans segnoY).trans segnoZ) o0 = o3
    ∧ ((segnoX.trans segnoY).trans segnoZ) o1 = o4
    ∧ ((segnoX.trans segnoY).trans segnoZ) o2 = o5 := by
  refine ⟨?_, ?_, ?_⟩
  · show segnoZ ((segnoX.trans segnoY) o0) = o3
    rw [sXY_o.1, segnoZ_o.2.2.2.1]
  · show segnoZ ((segnoX.trans segnoY) o1) = o4
    rw [sXY_o.2.1, segnoZ_o.2.2.2.2.1]
  · show segnoZ ((segnoX.trans segnoY) o2) = o5
    rw [sXY_o.2.2, segnoZ_o.2.2.1]

theorem segnoX_f : segnoX o0 = o3 ∧ segnoX o1 = o1 ∧ segnoX o2 = o2 :=
  ⟨segnoX_o.1, segnoX_o.2.1, segnoX_o.2.2.1⟩

theorem segnoY_f : segnoY o0 = o0 ∧ segnoY o1 = o4 ∧ segnoY o2 = o2 :=
  ⟨segnoY_o.1, segnoY_o.2.1, segnoY_o.2.2.1⟩

theorem segnoZ_f : segnoZ o0 = o0 ∧ segnoZ o1 = o1 ∧ segnoZ o2 = o5 :=
  ⟨segnoZ_o.1, segnoZ_o.2.1, segnoZ_o.2.2.1⟩

theorem segnoX_T₀ : (⇑segnoX.toAffineIsometryEquiv) '' T₀
    = convexHull ℝ (fmpp : Set E3) := by
  show (⇑segnoX.toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3)) = _
  have haff : (⇑segnoX.toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3))
      = convexHull ℝ ((⇑segnoX.toAffineIsometryEquiv) '' (facciaOtta : Set E3)) :=
    AffineMap.image_convexHull segnoX.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑segnoX.toAffineIsometryEquiv) u = segnoX u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
      simpa [facciaOtta] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [segnoX_f.1, segnoX_f.2.1, segnoX_f.2.2] <;>
      simp [fmpp]
  · intro hz
    have hcasi : z = o3 ∨ z = o1 ∨ z = o2 := by
      simpa [fmpp] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o0, by simp [facciaOtta], segnoX_f.1⟩
    · exact ⟨o1, by simp [facciaOtta], segnoX_f.2.1⟩
    · exact ⟨o2, by simp [facciaOtta], segnoX_f.2.2⟩

theorem segnoY_T₀ : (⇑segnoY.toAffineIsometryEquiv) '' T₀
    = convexHull ℝ (fpmp : Set E3) := by
  show (⇑segnoY.toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3)) = _
  have haff : (⇑segnoY.toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3))
      = convexHull ℝ ((⇑segnoY.toAffineIsometryEquiv) '' (facciaOtta : Set E3)) :=
    AffineMap.image_convexHull segnoY.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑segnoY.toAffineIsometryEquiv) u = segnoY u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
      simpa [facciaOtta] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [segnoY_f.1, segnoY_f.2.1, segnoY_f.2.2] <;>
      simp [fpmp]
  · intro hz
    have hcasi : z = o0 ∨ z = o4 ∨ z = o2 := by
      simpa [fpmp] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o0, by simp [facciaOtta], segnoY_f.1⟩
    · exact ⟨o1, by simp [facciaOtta], segnoY_f.2.1⟩
    · exact ⟨o2, by simp [facciaOtta], segnoY_f.2.2⟩

theorem segnoZ_T₀ : (⇑segnoZ.toAffineIsometryEquiv) '' T₀
    = convexHull ℝ (fppm : Set E3) := by
  show (⇑segnoZ.toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3)) = _
  have haff : (⇑segnoZ.toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3))
      = convexHull ℝ ((⇑segnoZ.toAffineIsometryEquiv) '' (facciaOtta : Set E3)) :=
    AffineMap.image_convexHull segnoZ.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑segnoZ.toAffineIsometryEquiv) u = segnoZ u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
      simpa [facciaOtta] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [segnoZ_f.1, segnoZ_f.2.1, segnoZ_f.2.2] <;>
      simp [fppm]
  · intro hz
    have hcasi : z = o0 ∨ z = o1 ∨ z = o5 := by
      simpa [fppm] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o0, by simp [facciaOtta], segnoZ_f.1⟩
    · exact ⟨o1, by simp [facciaOtta], segnoZ_f.2.1⟩
    · exact ⟨o2, by simp [facciaOtta], segnoZ_f.2.2⟩

theorem sXY_T₀ : (⇑(segnoX.trans segnoY).toAffineIsometryEquiv) '' T₀
    = convexHull ℝ (fmmp : Set E3) := by
  show (⇑(segnoX.trans segnoY).toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3)) = _
  have haff : (⇑(segnoX.trans segnoY).toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3))
      = convexHull ℝ ((⇑(segnoX.trans segnoY).toAffineIsometryEquiv) '' (facciaOtta : Set E3)) :=
    AffineMap.image_convexHull (segnoX.trans segnoY).toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑(segnoX.trans segnoY).toAffineIsometryEquiv) u = (segnoX.trans segnoY) u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
      simpa [facciaOtta] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [sXY_o.1, sXY_o.2.1, sXY_o.2.2] <;>
      simp [fmmp]
  · intro hz
    have hcasi : z = o3 ∨ z = o4 ∨ z = o2 := by
      simpa [fmmp] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o0, by simp [facciaOtta], sXY_o.1⟩
    · exact ⟨o1, by simp [facciaOtta], sXY_o.2.1⟩
    · exact ⟨o2, by simp [facciaOtta], sXY_o.2.2⟩

theorem sXZ_T₀ : (⇑(segnoX.trans segnoZ).toAffineIsometryEquiv) '' T₀
    = convexHull ℝ (fmpm : Set E3) := by
  show (⇑(segnoX.trans segnoZ).toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3)) = _
  have haff : (⇑(segnoX.trans segnoZ).toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3))
      = convexHull ℝ ((⇑(segnoX.trans segnoZ).toAffineIsometryEquiv) '' (facciaOtta : Set E3)) :=
    AffineMap.image_convexHull (segnoX.trans segnoZ).toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑(segnoX.trans segnoZ).toAffineIsometryEquiv) u = (segnoX.trans segnoZ) u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
      simpa [facciaOtta] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [sXZ_o.1, sXZ_o.2.1, sXZ_o.2.2] <;>
      simp [fmpm]
  · intro hz
    have hcasi : z = o3 ∨ z = o1 ∨ z = o5 := by
      simpa [fmpm] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o0, by simp [facciaOtta], sXZ_o.1⟩
    · exact ⟨o1, by simp [facciaOtta], sXZ_o.2.1⟩
    · exact ⟨o2, by simp [facciaOtta], sXZ_o.2.2⟩

theorem sYZ_T₀ : (⇑(segnoY.trans segnoZ).toAffineIsometryEquiv) '' T₀
    = convexHull ℝ (fpmm : Set E3) := by
  show (⇑(segnoY.trans segnoZ).toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3)) = _
  have haff : (⇑(segnoY.trans segnoZ).toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3))
      = convexHull ℝ ((⇑(segnoY.trans segnoZ).toAffineIsometryEquiv) '' (facciaOtta : Set E3)) :=
    AffineMap.image_convexHull (segnoY.trans segnoZ).toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑(segnoY.trans segnoZ).toAffineIsometryEquiv) u = (segnoY.trans segnoZ) u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
      simpa [facciaOtta] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [sYZ_o.1, sYZ_o.2.1, sYZ_o.2.2] <;>
      simp [fpmm]
  · intro hz
    have hcasi : z = o0 ∨ z = o4 ∨ z = o5 := by
      simpa [fpmm] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o0, by simp [facciaOtta], sYZ_o.1⟩
    · exact ⟨o1, by simp [facciaOtta], sYZ_o.2.1⟩
    · exact ⟨o2, by simp [facciaOtta], sYZ_o.2.2⟩

theorem sXYZ_T₀ : (⇑((segnoX.trans segnoY).trans segnoZ).toAffineIsometryEquiv) '' T₀
    = convexHull ℝ (fmmm : Set E3) := by
  show (⇑((segnoX.trans segnoY).trans segnoZ).toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3)) = _
  have haff : (⇑((segnoX.trans segnoY).trans segnoZ).toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3))
      = convexHull ℝ ((⇑((segnoX.trans segnoY).trans segnoZ).toAffineIsometryEquiv) '' (facciaOtta : Set E3)) :=
    AffineMap.image_convexHull ((segnoX.trans segnoY).trans segnoZ).toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑((segnoX.trans segnoY).trans segnoZ).toAffineIsometryEquiv) u = ((segnoX.trans segnoY).trans segnoZ) u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
      simpa [facciaOtta] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [sXYZ_o.1, sXYZ_o.2.1, sXYZ_o.2.2] <;>
      simp [fmmm]
  · intro hz
    have hcasi : z = o3 ∨ z = o4 ∨ z = o5 := by
      simpa [fmmm] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o0, by simp [facciaOtta], sXYZ_o.1⟩
    · exact ⟨o1, by simp [facciaOtta], sXYZ_o.2.1⟩
    · exact ⟨o2, by simp [facciaOtta], sXYZ_o.2.2⟩

/-! ## LA CLASSIFICAZIONE DELLE FACCETTE DELL'OTTAEDRO -/

set_option maxHeartbeats 3200000 in
/-- Ogni faccetta dell'ottaedro è una delle otto facce triangolari. -/
theorem facet_classification_otta {F : Set E3} (hF : ottaedro.IsFacet F) :
    F = convexHull ℝ (facciaOtta : Set E3)
    ∨ F = convexHull ℝ (fmpp : Set E3) ∨ F = convexHull ℝ (fpmp : Set E3)
    ∨ F = convexHull ℝ (fppm : Set E3) ∨ F = convexHull ℝ (fmmp : Set E3)
    ∨ F = convexHull ℝ (fmpm : Set E3) ∨ F = convexHull ℝ (fpmm : Set E3)
    ∨ F = convexHull ℝ (fmmm : Set E3) := by
  classical
  obtain ⟨l, hl⟩ := hF.1.1 hF.1.2
  have hFS := exposedFace_eq_convexHull_vertices_otta hF.1
  set S : Finset E3 := ottaedro.vertices.filter (· ∈ F) with hSdef
  have hspanS : vectorSpan ℝ (S : Set E3)
      = vectorSpan ℝ (convexHull ℝ (S : Set E3)) := by
    rw [← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]
  have hd : Module.finrank ℝ (vectorSpan ℝ (S : Set E3)) = 2 := by
    have hdF := hF.2
    rw [hFS, ← hspanS] at hdF
    exact hdF
  have hSsub : (S : Set E3) ⊆ (ottaedro.vertices : Set E3) := by
    intro u hu
    have : u ∈ ottaedro.vertices.filter (· ∈ F) := by exact_mod_cast hu
    exact_mod_cast Finset.filter_subset _ _ this
  have hcrit : ∀ u ∈ (ottaedro.vertices : Set E3),
      (u ∈ (S : Set E3) ↔ ∀ w ∈ (ottaedro.vertices : Set E3), l w ≤ l u) := by
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
      show u ∈ ((ottaedro.vertices.filter (· ∈ F) : Finset E3) : Set E3)
      exact_mod_cast Finset.mem_filter.mpr ⟨by exact_mod_cast hu, huF⟩
  rcases lt_trichotomy (compL l 0) 0 with hx | hx | hx
  · -- a0 N
    rcases lt_trichotomy (compL l 1) 0 with hy | hy | hy
    · -- a1 N
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (N,N,N)
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_)))))))
        rw [hFS]
        congr 1
        have hsub3 : (S : Set E3) ⊆ {o3, o4, o5} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o0] at h
            linarith
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o1] at h
            linarith
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o2] at h
            linarith
          · simp
          · simp
          · simp
        have hm_o3 : o3 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o4, o5} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · exact absurd (h ▸ hu) hno
            · simp [h]
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o4 : o4 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o3, o5} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · exact absurd (h ▸ hu) hno
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o5 : o5 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o3, o4} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd (h ▸ hu) hno
          have := span_coppia_le hp
          omega
        apply Set.Subset.antisymm
        · intro u hu
          have hc := hsub3 hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          rcases hc with h | h | h <;> subst h <;> simp [fmmm]
        · intro u hu
          have hcasi : u = o3 ∨ u = o4 ∨ u = o5 := by
            simpa [fmmm] using hu
          rcases hcasi with h | h | h <;> subst h
          · exact hm_o3
          · exact hm_o4
          · exact hm_o5
      · -- (N,N,Z)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o3, o4} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o0] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o1] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o2] at h
              linarith
            · simp
            · simp
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
      · -- (N,N,P)
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        rw [hFS]
        congr 1
        have hsub3 : (S : Set E3) ⊆ {o3, o4, o2} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o0] at h
            linarith
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o1] at h
            linarith
          · simp
          · simp
          · simp
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o5] at h
            linarith
        have hm_o3 : o3 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o4, o2} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · exact absurd (h ▸ hu) hno
            · simp [h]
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o4 : o4 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o3, o2} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · exact absurd (h ▸ hu) hno
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o2 : o2 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o3, o4} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd (h ▸ hu) hno
          have := span_coppia_le hp
          omega
        apply Set.Subset.antisymm
        · intro u hu
          have hc := hsub3 hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          rcases hc with h | h | h <;> subst h <;> simp [fmmp]
        · intro u hu
          have hcasi : u = o3 ∨ u = o4 ∨ u = o2 := by
            simpa [fmmp] using hu
          rcases hcasi with h | h | h <;> subst h
          · exact hm_o3
          · exact hm_o4
          · exact hm_o2
    · -- a1 Z
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (N,Z,N)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o3, o5} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o0] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o1] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o2] at h
              linarith
            · simp
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o4] at h
              linarith
            · simp
          have := span_coppia_le hsub
          omega)
      · -- (N,Z,Z)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o3, o3} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o0] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o1] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o2] at h
              linarith
            · simp
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o4] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
      · -- (N,Z,P)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o3, o2} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o0] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o1] at h
              linarith
            · simp
            · simp
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o4] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
    · -- a1 P
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (N,P,N)
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
        rw [hFS]
        congr 1
        have hsub3 : (S : Set E3) ⊆ {o3, o1, o5} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o0] at h
            linarith
          · simp
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o2] at h
            linarith
          · simp
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o4] at h
            linarith
          · simp
        have hm_o3 : o3 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o1, o5} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · exact absurd (h ▸ hu) hno
            · simp [h]
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o1 : o1 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o3, o5} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · exact absurd (h ▸ hu) hno
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o5 : o5 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o3, o1} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd (h ▸ hu) hno
          have := span_coppia_le hp
          omega
        apply Set.Subset.antisymm
        · intro u hu
          have hc := hsub3 hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          rcases hc with h | h | h <;> subst h <;> simp [fmpm]
        · intro u hu
          have hcasi : u = o3 ∨ u = o1 ∨ u = o5 := by
            simpa [fmpm] using hu
          rcases hcasi with h | h | h <;> subst h
          · exact hm_o3
          · exact hm_o1
          · exact hm_o5
      · -- (N,P,Z)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o3, o1} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o0] at h
              linarith
            · simp
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o2] at h
              linarith
            · simp
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o4] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
      · -- (N,P,P)
        refine Or.inr (Or.inl ?_)
        rw [hFS]
        congr 1
        have hsub3 : (S : Set E3) ⊆ {o3, o1, o2} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o0] at h
            linarith
          · simp
          · simp
          · simp
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o4] at h
            linarith
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o5] at h
            linarith
        have hm_o3 : o3 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o1, o2} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · exact absurd (h ▸ hu) hno
            · simp [h]
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o1 : o1 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o3, o2} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · exact absurd (h ▸ hu) hno
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o2 : o2 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o3, o1} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd (h ▸ hu) hno
          have := span_coppia_le hp
          omega
        apply Set.Subset.antisymm
        · intro u hu
          have hc := hsub3 hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          rcases hc with h | h | h <;> subst h <;> simp [fmpp]
        · intro u hu
          have hcasi : u = o3 ∨ u = o1 ∨ u = o2 := by
            simpa [fmpp] using hu
          rcases hcasi with h | h | h <;> subst h
          · exact hm_o3
          · exact hm_o1
          · exact hm_o2
  · -- a0 Z
    rcases lt_trichotomy (compL l 1) 0 with hy | hy | hy
    · -- a1 N
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (Z,N,N)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o4, o5} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o0] at h
              linarith
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o1] at h
              linarith
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o2] at h
              linarith
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o3] at h
              linarith
            · simp
            · simp
          have := span_coppia_le hsub
          omega)
      · -- (Z,N,Z)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o4, o4} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o0] at h
              linarith
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o1] at h
              linarith
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o2] at h
              linarith
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o3] at h
              linarith
            · simp
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
      · -- (Z,N,P)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o4, o2} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o0] at h
              linarith
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o1] at h
              linarith
            · simp
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o3] at h
              linarith
            · simp
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
    · -- a1 Z
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (Z,Z,N)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o5, o5} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o5 (by simp [ottaedro, verticiOtta])
              rw [l_o5, l_o0] at h
              linarith
            · exfalso
              have h := hmax o5 (by simp [ottaedro, verticiOtta])
              rw [l_o5, l_o1] at h
              linarith
            · exfalso
              have h := hmax o5 (by simp [ottaedro, verticiOtta])
              rw [l_o5, l_o2] at h
              linarith
            · exfalso
              have h := hmax o5 (by simp [ottaedro, verticiOtta])
              rw [l_o5, l_o3] at h
              linarith
            · exfalso
              have h := hmax o5 (by simp [ottaedro, verticiOtta])
              rw [l_o5, l_o4] at h
              linarith
            · simp
          have := span_coppia_le hsub
          omega)
      · -- (Z,Z,Z)
        exfalso
        have hSall : (S : Set E3) = (ottaedro.vertices : Set E3) := by
          apply Set.Subset.antisymm hSsub
          intro u hu
          refine (hcrit u hu).mpr ?_
          intro w hw
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hw) with
            h | h | h | h | h | h <;> subst h <;>
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h <;>
            simp only [l_o0, l_o1, l_o2, l_o3, l_o4, l_o5] <;>
            linarith
        rw [hSall, ottaedro_finrank] at hd
        omega
      · -- (Z,Z,P)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o2, o2} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o2 (by simp [ottaedro, verticiOtta])
              rw [l_o2, l_o0] at h
              linarith
            · exfalso
              have h := hmax o2 (by simp [ottaedro, verticiOtta])
              rw [l_o2, l_o1] at h
              linarith
            · simp
            · exfalso
              have h := hmax o2 (by simp [ottaedro, verticiOtta])
              rw [l_o2, l_o3] at h
              linarith
            · exfalso
              have h := hmax o2 (by simp [ottaedro, verticiOtta])
              rw [l_o2, l_o4] at h
              linarith
            · exfalso
              have h := hmax o2 (by simp [ottaedro, verticiOtta])
              rw [l_o2, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
    · -- a1 P
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (Z,P,N)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o1, o5} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o0] at h
              linarith
            · simp
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o2] at h
              linarith
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o3] at h
              linarith
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o4] at h
              linarith
            · simp
          have := span_coppia_le hsub
          omega)
      · -- (Z,P,Z)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o1, o1} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o0] at h
              linarith
            · simp
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o2] at h
              linarith
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o3] at h
              linarith
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o4] at h
              linarith
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
      · -- (Z,P,P)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o1, o2} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o0] at h
              linarith
            · simp
            · simp
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o3] at h
              linarith
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o4] at h
              linarith
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
  · -- a0 P
    rcases lt_trichotomy (compL l 1) 0 with hy | hy | hy
    · -- a1 N
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (P,N,N)
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
        rw [hFS]
        congr 1
        have hsub3 : (S : Set E3) ⊆ {o0, o4, o5} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h
          · simp
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o1] at h
            linarith
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o2] at h
            linarith
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o3] at h
            linarith
          · simp
          · simp
        have hm_o0 : o0 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o4, o5} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · exact absurd (h ▸ hu) hno
            · simp [h]
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o4 : o4 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o0, o5} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · exact absurd (h ▸ hu) hno
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o5 : o5 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o0, o4} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd (h ▸ hu) hno
          have := span_coppia_le hp
          omega
        apply Set.Subset.antisymm
        · intro u hu
          have hc := hsub3 hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          rcases hc with h | h | h <;> subst h <;> simp [fpmm]
        · intro u hu
          have hcasi : u = o0 ∨ u = o4 ∨ u = o5 := by
            simpa [fpmm] using hu
          rcases hcasi with h | h | h <;> subst h
          · exact hm_o0
          · exact hm_o4
          · exact hm_o5
      · -- (P,N,Z)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o0, o4} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · simp
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o1] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o2] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o3] at h
              linarith
            · simp
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
      · -- (P,N,P)
        refine Or.inr (Or.inr (Or.inl ?_))
        rw [hFS]
        congr 1
        have hsub3 : (S : Set E3) ⊆ {o0, o4, o2} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h
          · simp
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o1] at h
            linarith
          · simp
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o3] at h
            linarith
          · simp
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o5] at h
            linarith
        have hm_o0 : o0 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o4, o2} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · exact absurd (h ▸ hu) hno
            · simp [h]
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o4 : o4 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o0, o2} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · exact absurd (h ▸ hu) hno
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o2 : o2 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o0, o4} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd (h ▸ hu) hno
          have := span_coppia_le hp
          omega
        apply Set.Subset.antisymm
        · intro u hu
          have hc := hsub3 hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          rcases hc with h | h | h <;> subst h <;> simp [fpmp]
        · intro u hu
          have hcasi : u = o0 ∨ u = o4 ∨ u = o2 := by
            simpa [fpmp] using hu
          rcases hcasi with h | h | h <;> subst h
          · exact hm_o0
          · exact hm_o4
          · exact hm_o2
    · -- a1 Z
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (P,Z,N)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o0, o5} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · simp
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o1] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o2] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o3] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o4] at h
              linarith
            · simp
          have := span_coppia_le hsub
          omega)
      · -- (P,Z,Z)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o0, o0} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · simp
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o1] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o2] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o3] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o4] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
      · -- (P,Z,P)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o0, o2} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · simp
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o1] at h
              linarith
            · simp
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o3] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o4] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
    · -- a1 P
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (P,P,N)
        refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        rw [hFS]
        congr 1
        have hsub3 : (S : Set E3) ⊆ {o0, o1, o5} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h
          · simp
          · simp
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o2] at h
            linarith
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o3] at h
            linarith
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o4] at h
            linarith
          · simp
        have hm_o0 : o0 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o1, o5} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · exact absurd (h ▸ hu) hno
            · simp [h]
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o1 : o1 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o0, o5} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · exact absurd (h ▸ hu) hno
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o5 : o5 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o0, o1} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd (h ▸ hu) hno
          have := span_coppia_le hp
          omega
        apply Set.Subset.antisymm
        · intro u hu
          have hc := hsub3 hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          rcases hc with h | h | h <;> subst h <;> simp [fppm]
        · intro u hu
          have hcasi : u = o0 ∨ u = o1 ∨ u = o5 := by
            simpa [fppm] using hu
          rcases hcasi with h | h | h <;> subst h
          · exact hm_o0
          · exact hm_o1
          · exact hm_o5
      · -- (P,P,Z)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o0, o1} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · simp
            · simp
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o2] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o3] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o4] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
      · -- (P,P,P)
        refine Or.inl ?_
        rw [hFS]
        congr 1
        have hsub3 : (S : Set E3) ⊆ {o0, o1, o2} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h
          · simp
          · simp
          · simp
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o3] at h
            linarith
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o4] at h
            linarith
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o5] at h
            linarith
        have hm_o0 : o0 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o1, o2} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · exact absurd (h ▸ hu) hno
            · simp [h]
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o1 : o1 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o0, o2} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · exact absurd (h ▸ hu) hno
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o2 : o2 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o0, o1} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd (h ▸ hu) hno
          have := span_coppia_le hp
          omega
        apply Set.Subset.antisymm
        · intro u hu
          have hc := hsub3 hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          rcases hc with h | h | h <;> subst h <;> simp [facciaOtta]
        · intro u hu
          have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
            simpa [facciaOtta] using hu
          rcases hcasi with h | h | h <;> subst h
          · exact hm_o0
          · exact hm_o1
          · exact hm_o2

/-- TUTTE le faccette dell'ottaedro sono triangoli regolari di lato √2. -/
theorem otta_faccette_regolari :
    ∀ F, ottaedro.IsFacet F → ottaedro.IsRegularFacet F 3 (Real.sqrt 2) := by
  intro F hF
  rcases facet_classification_otta hF with h | h | h | h | h | h | h | h <;>
    subst h
  · exact facciaOtta_regolare
  · rw [← segnoX_T₀]
    exact isRegularFacet_image ottaedro _
      (preserva_toSet_otta segnoX segnoX_overtset) facciaOtta_regolare
  · rw [← segnoY_T₀]
    exact isRegularFacet_image ottaedro _
      (preserva_toSet_otta segnoY segnoY_overtset) facciaOtta_regolare
  · rw [← segnoZ_T₀]
    exact isRegularFacet_image ottaedro _
      (preserva_toSet_otta segnoZ segnoZ_overtset) facciaOtta_regolare
  · rw [← sXY_T₀]
    exact isRegularFacet_image ottaedro _
      (preserva_toSet_otta _ (overtset_trans segnoX segnoY
        segnoX_overtset segnoY_overtset)) facciaOtta_regolare
  · rw [← sXZ_T₀]
    exact isRegularFacet_image ottaedro _
      (preserva_toSet_otta _ (overtset_trans segnoX segnoZ
        segnoX_overtset segnoZ_overtset)) facciaOtta_regolare
  · rw [← sYZ_T₀]
    exact isRegularFacet_image ottaedro _
      (preserva_toSet_otta _ (overtset_trans segnoY segnoZ
        segnoY_overtset segnoZ_overtset)) facciaOtta_regolare
  · rw [← sXYZ_T₀]
    exact isRegularFacet_image ottaedro _
      (preserva_toSet_otta _ (overtset_trans _ segnoZ
        (overtset_trans segnoX segnoY segnoX_overtset segnoY_overtset)
        segnoZ_overtset)) facciaOtta_regolare

/-! ## I funzionali delle facce, i loro semispazi e il polo nord -/

theorem lX_o : lX o0 = 1 ∧ lX o1 = 0 ∧ lX o2 = 0 ∧ lX o3 = -1 ∧ lX o4 = 0
    ∧ lX o5 = 0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem lY_o : lY o0 = 0 ∧ lY o1 = 1 ∧ lY o2 = 0 ∧ lY o3 = 0 ∧ lY o4 = -1
    ∧ lY o5 = 0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem lZ_o : lZ o0 = 0 ∧ lZ o1 = 0 ∧ lZ o2 = 1 ∧ lZ o3 = 0 ∧ lZ o4 = 0
    ∧ lZ o5 = -1 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- lZ non supera 1 sul corpo dell'ottaedro. -/
theorem toSet_otta_lZ_le : ∀ z ∈ ottaedro.toSet, lZ z ≤ 1 := by
  intro z hz
  have hsub : (verticiOtta : Set E3) ⊆ {w : E3 | lZ w ≤ 1} := by
    intro w hw
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hw) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq] <;>
      first
        | (rw [lZ_o.1]; norm_num)
        | (rw [lZ_o.2.1]; norm_num)
        | (rw [lZ_o.2.2.1])
        | (rw [lZ_o.2.2.2.1]; norm_num)
        | (rw [lZ_o.2.2.2.2.1]; norm_num)
        | (rw [lZ_o.2.2.2.2.2]; norm_num)
  exact convexHull_min hsub
    (convex_halfSpace_le (LinearMap.isLinear lZ.toLinearMap) 1) hz

/-- IL POLO NORD: l'unico punto del corpo con lZ = 1 è o2. -/
theorem polo_nord : ∀ z ∈ ottaedro.toSet, lZ z = 1 → z = o2 := by
  intro z hz h1
  have hmax : ∀ w ∈ ottaedro.toSet, lZ w ≤ lZ z := by
    intro w hw
    rw [h1]
    exact toSet_otta_lZ_le w hw
  have hL3 := faccia_argmax verticiOtta lZ hz hmax
  have hset : {x ∈ (verticiOtta : Set E3) | lZ x = lZ z} = {o2} := by
    rw [h1]
    ext u
    constructor
    · rintro ⟨hu, hu1⟩
      rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
        h | h | h | h | h | h <;> subst h
      · exfalso; rw [lZ_o.1] at hu1; norm_num at hu1
      · exfalso; rw [lZ_o.2.1] at hu1; norm_num at hu1
      · rfl
      · exfalso; rw [lZ_o.2.2.2.1] at hu1; norm_num at hu1
      · exfalso; rw [lZ_o.2.2.2.2.1] at hu1; norm_num at hu1
      · exfalso; rw [lZ_o.2.2.2.2.2] at hu1; norm_num at hu1
    · intro hu
      have : u = o2 := hu
      subst this
      exact ⟨by simp [verticiOtta], lZ_o.2.2.1⟩
  rw [hset] at hL3
  simpa using hL3

def fN1 : E3 →L[ℝ] ℝ := (lY + lZ) - lX
theorem fN1_o : fN1 o0 = -1 ∧ fN1 o1 = 1 ∧ fN1 o2 = 1 ∧ fN1 o3 = 1 ∧ fN1 o4 = -1 ∧ fN1 o5 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [fN1, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply]
     norm_num [lX_o.1, lX_o.2.1, lX_o.2.2.1, lX_o.2.2.2.1,
       lX_o.2.2.2.2.1, lX_o.2.2.2.2.2, lY_o.1, lY_o.2.1,
       lY_o.2.2.1, lY_o.2.2.2.1, lY_o.2.2.2.2.1, lY_o.2.2.2.2.2,
       lZ_o.1, lZ_o.2.1, lZ_o.2.2.1, lZ_o.2.2.2.1,
       lZ_o.2.2.2.2.1, lZ_o.2.2.2.2.2])
theorem toSet_fN1_le : ∀ z ∈ ottaedro.toSet, fN1 z ≤ 1 := by
  intro z hz
  have hsub : (verticiOtta : Set E3) ⊆ {w : E3 | fN1 w ≤ 1} := by
    intro w hw
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hw) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq] <;>
      first
        | (rw [fN1_o.1]; norm_num)
        | (rw [fN1_o.2.1])
        | (rw [fN1_o.2.2.1])
        | (rw [fN1_o.2.2.2.1])
        | (rw [fN1_o.2.2.2.2.1]; norm_num)
        | (rw [fN1_o.2.2.2.2.2]; norm_num)
  exact convexHull_min hsub
    (convex_halfSpace_le (LinearMap.isLinear fN1.toLinearMap) 1) hz
theorem hull_fmpp_ge : ∀ z ∈ convexHull ℝ ((fmpp : Finset E3) : Set E3), 1 ≤ fN1 z := by
  intro z hz
  have hsub : ((fmpp : Finset E3) : Set E3) ⊆ {w : E3 | 1 ≤ fN1 w} := by
    intro w hw
    have hcasi : w = o3 ∨ w = o1 ∨ w = o2 := by
      simpa [fmpp] using hw
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq]
    · rw [fN1_o.2.2.2.1]
    · rw [fN1_o.2.1]
    · rw [fN1_o.2.2.1]
  exact convexHull_min hsub
    (convex_halfSpace_ge (LinearMap.isLinear fN1.toLinearMap) 1) hz

def fN2 : E3 →L[ℝ] ℝ := lZ - (lX + lY)
theorem fN2_o : fN2 o0 = -1 ∧ fN2 o1 = -1 ∧ fN2 o2 = 1 ∧ fN2 o3 = 1 ∧ fN2 o4 = 1 ∧ fN2 o5 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [fN2, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply]
     norm_num [lX_o.1, lX_o.2.1, lX_o.2.2.1, lX_o.2.2.2.1,
       lX_o.2.2.2.2.1, lX_o.2.2.2.2.2, lY_o.1, lY_o.2.1,
       lY_o.2.2.1, lY_o.2.2.2.1, lY_o.2.2.2.2.1, lY_o.2.2.2.2.2,
       lZ_o.1, lZ_o.2.1, lZ_o.2.2.1, lZ_o.2.2.2.1,
       lZ_o.2.2.2.2.1, lZ_o.2.2.2.2.2])
theorem toSet_fN2_le : ∀ z ∈ ottaedro.toSet, fN2 z ≤ 1 := by
  intro z hz
  have hsub : (verticiOtta : Set E3) ⊆ {w : E3 | fN2 w ≤ 1} := by
    intro w hw
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hw) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq] <;>
      first
        | (rw [fN2_o.1]; norm_num)
        | (rw [fN2_o.2.1]; norm_num)
        | (rw [fN2_o.2.2.1])
        | (rw [fN2_o.2.2.2.1])
        | (rw [fN2_o.2.2.2.2.1])
        | (rw [fN2_o.2.2.2.2.2]; norm_num)
  exact convexHull_min hsub
    (convex_halfSpace_le (LinearMap.isLinear fN2.toLinearMap) 1) hz
theorem hull_fmmp_ge : ∀ z ∈ convexHull ℝ ((fmmp : Finset E3) : Set E3), 1 ≤ fN2 z := by
  intro z hz
  have hsub : ((fmmp : Finset E3) : Set E3) ⊆ {w : E3 | 1 ≤ fN2 w} := by
    intro w hw
    have hcasi : w = o3 ∨ w = o4 ∨ w = o2 := by
      simpa [fmmp] using hw
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq]
    · rw [fN2_o.2.2.2.1]
    · rw [fN2_o.2.2.2.2.1]
    · rw [fN2_o.2.2.1]
  exact convexHull_min hsub
    (convex_halfSpace_ge (LinearMap.isLinear fN2.toLinearMap) 1) hz

def fN3 : E3 →L[ℝ] ℝ := (lX + lZ) - lY
theorem fN3_o : fN3 o0 = 1 ∧ fN3 o1 = -1 ∧ fN3 o2 = 1 ∧ fN3 o3 = -1 ∧ fN3 o4 = 1 ∧ fN3 o5 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [fN3, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply]
     norm_num [lX_o.1, lX_o.2.1, lX_o.2.2.1, lX_o.2.2.2.1,
       lX_o.2.2.2.2.1, lX_o.2.2.2.2.2, lY_o.1, lY_o.2.1,
       lY_o.2.2.1, lY_o.2.2.2.1, lY_o.2.2.2.2.1, lY_o.2.2.2.2.2,
       lZ_o.1, lZ_o.2.1, lZ_o.2.2.1, lZ_o.2.2.2.1,
       lZ_o.2.2.2.2.1, lZ_o.2.2.2.2.2])
theorem toSet_fN3_le : ∀ z ∈ ottaedro.toSet, fN3 z ≤ 1 := by
  intro z hz
  have hsub : (verticiOtta : Set E3) ⊆ {w : E3 | fN3 w ≤ 1} := by
    intro w hw
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hw) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq] <;>
      first
        | (rw [fN3_o.1])
        | (rw [fN3_o.2.1]; norm_num)
        | (rw [fN3_o.2.2.1])
        | (rw [fN3_o.2.2.2.1]; norm_num)
        | (rw [fN3_o.2.2.2.2.1])
        | (rw [fN3_o.2.2.2.2.2]; norm_num)
  exact convexHull_min hsub
    (convex_halfSpace_le (LinearMap.isLinear fN3.toLinearMap) 1) hz
theorem hull_fpmp_ge : ∀ z ∈ convexHull ℝ ((fpmp : Finset E3) : Set E3), 1 ≤ fN3 z := by
  intro z hz
  have hsub : ((fpmp : Finset E3) : Set E3) ⊆ {w : E3 | 1 ≤ fN3 w} := by
    intro w hw
    have hcasi : w = o0 ∨ w = o4 ∨ w = o2 := by
      simpa [fpmp] using hw
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq]
    · rw [fN3_o.1]
    · rw [fN3_o.2.2.2.2.1]
    · rw [fN3_o.2.2.1]
  exact convexHull_min hsub
    (convex_halfSpace_ge (LinearMap.isLinear fN3.toLinearMap) 1) hz

def fS0 : E3 →L[ℝ] ℝ := (lX + lY) - lZ
theorem fS0_o : fS0 o0 = 1 ∧ fS0 o1 = 1 ∧ fS0 o2 = -1 ∧ fS0 o3 = -1 ∧ fS0 o4 = -1 ∧ fS0 o5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [fS0, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply]
     norm_num [lX_o.1, lX_o.2.1, lX_o.2.2.1, lX_o.2.2.2.1,
       lX_o.2.2.2.2.1, lX_o.2.2.2.2.2, lY_o.1, lY_o.2.1,
       lY_o.2.2.1, lY_o.2.2.2.1, lY_o.2.2.2.2.1, lY_o.2.2.2.2.2,
       lZ_o.1, lZ_o.2.1, lZ_o.2.2.1, lZ_o.2.2.2.1,
       lZ_o.2.2.2.2.1, lZ_o.2.2.2.2.2])
theorem toSet_fS0_le : ∀ z ∈ ottaedro.toSet, fS0 z ≤ 1 := by
  intro z hz
  have hsub : (verticiOtta : Set E3) ⊆ {w : E3 | fS0 w ≤ 1} := by
    intro w hw
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hw) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq] <;>
      first
        | (rw [fS0_o.1])
        | (rw [fS0_o.2.1])
        | (rw [fS0_o.2.2.1]; norm_num)
        | (rw [fS0_o.2.2.2.1]; norm_num)
        | (rw [fS0_o.2.2.2.2.1]; norm_num)
        | (rw [fS0_o.2.2.2.2.2])
  exact convexHull_min hsub
    (convex_halfSpace_le (LinearMap.isLinear fS0.toLinearMap) 1) hz
theorem hull_fppm_ge : ∀ z ∈ convexHull ℝ ((fppm : Finset E3) : Set E3), 1 ≤ fS0 z := by
  intro z hz
  have hsub : ((fppm : Finset E3) : Set E3) ⊆ {w : E3 | 1 ≤ fS0 w} := by
    intro w hw
    have hcasi : w = o0 ∨ w = o1 ∨ w = o5 := by
      simpa [fppm] using hw
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq]
    · rw [fS0_o.1]
    · rw [fS0_o.2.1]
    · rw [fS0_o.2.2.2.2.2]
  exact convexHull_min hsub
    (convex_halfSpace_ge (LinearMap.isLinear fS0.toLinearMap) 1) hz

def fS1 : E3 →L[ℝ] ℝ := lY - (lX + lZ)
theorem fS1_o : fS1 o0 = -1 ∧ fS1 o1 = 1 ∧ fS1 o2 = -1 ∧ fS1 o3 = 1 ∧ fS1 o4 = -1 ∧ fS1 o5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [fS1, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply]
     norm_num [lX_o.1, lX_o.2.1, lX_o.2.2.1, lX_o.2.2.2.1,
       lX_o.2.2.2.2.1, lX_o.2.2.2.2.2, lY_o.1, lY_o.2.1,
       lY_o.2.2.1, lY_o.2.2.2.1, lY_o.2.2.2.2.1, lY_o.2.2.2.2.2,
       lZ_o.1, lZ_o.2.1, lZ_o.2.2.1, lZ_o.2.2.2.1,
       lZ_o.2.2.2.2.1, lZ_o.2.2.2.2.2])
theorem toSet_fS1_le : ∀ z ∈ ottaedro.toSet, fS1 z ≤ 1 := by
  intro z hz
  have hsub : (verticiOtta : Set E3) ⊆ {w : E3 | fS1 w ≤ 1} := by
    intro w hw
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hw) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq] <;>
      first
        | (rw [fS1_o.1]; norm_num)
        | (rw [fS1_o.2.1])
        | (rw [fS1_o.2.2.1]; norm_num)
        | (rw [fS1_o.2.2.2.1])
        | (rw [fS1_o.2.2.2.2.1]; norm_num)
        | (rw [fS1_o.2.2.2.2.2])
  exact convexHull_min hsub
    (convex_halfSpace_le (LinearMap.isLinear fS1.toLinearMap) 1) hz
theorem hull_fmpm_ge : ∀ z ∈ convexHull ℝ ((fmpm : Finset E3) : Set E3), 1 ≤ fS1 z := by
  intro z hz
  have hsub : ((fmpm : Finset E3) : Set E3) ⊆ {w : E3 | 1 ≤ fS1 w} := by
    intro w hw
    have hcasi : w = o3 ∨ w = o1 ∨ w = o5 := by
      simpa [fmpm] using hw
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq]
    · rw [fS1_o.2.2.2.1]
    · rw [fS1_o.2.1]
    · rw [fS1_o.2.2.2.2.2]
  exact convexHull_min hsub
    (convex_halfSpace_ge (LinearMap.isLinear fS1.toLinearMap) 1) hz

def fS2 : E3 →L[ℝ] ℝ := lX - (lY + lZ)
theorem fS2_o : fS2 o0 = 1 ∧ fS2 o1 = -1 ∧ fS2 o2 = -1 ∧ fS2 o3 = -1 ∧ fS2 o4 = 1 ∧ fS2 o5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [fS2, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply]
     norm_num [lX_o.1, lX_o.2.1, lX_o.2.2.1, lX_o.2.2.2.1,
       lX_o.2.2.2.2.1, lX_o.2.2.2.2.2, lY_o.1, lY_o.2.1,
       lY_o.2.2.1, lY_o.2.2.2.1, lY_o.2.2.2.2.1, lY_o.2.2.2.2.2,
       lZ_o.1, lZ_o.2.1, lZ_o.2.2.1, lZ_o.2.2.2.1,
       lZ_o.2.2.2.2.1, lZ_o.2.2.2.2.2])
theorem toSet_fS2_le : ∀ z ∈ ottaedro.toSet, fS2 z ≤ 1 := by
  intro z hz
  have hsub : (verticiOtta : Set E3) ⊆ {w : E3 | fS2 w ≤ 1} := by
    intro w hw
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hw) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq] <;>
      first
        | (rw [fS2_o.1])
        | (rw [fS2_o.2.1]; norm_num)
        | (rw [fS2_o.2.2.1]; norm_num)
        | (rw [fS2_o.2.2.2.1]; norm_num)
        | (rw [fS2_o.2.2.2.2.1])
        | (rw [fS2_o.2.2.2.2.2])
  exact convexHull_min hsub
    (convex_halfSpace_le (LinearMap.isLinear fS2.toLinearMap) 1) hz
theorem hull_fpmm_ge : ∀ z ∈ convexHull ℝ ((fpmm : Finset E3) : Set E3), 1 ≤ fS2 z := by
  intro z hz
  have hsub : ((fpmm : Finset E3) : Set E3) ⊆ {w : E3 | 1 ≤ fS2 w} := by
    intro w hw
    have hcasi : w = o0 ∨ w = o4 ∨ w = o5 := by
      simpa [fpmm] using hw
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq]
    · rw [fS2_o.1]
    · rw [fS2_o.2.2.2.2.1]
    · rw [fS2_o.2.2.2.2.2]
  exact convexHull_min hsub
    (convex_halfSpace_ge (LinearMap.isLinear fS2.toLinearMap) 1) hz

def fS7 : E3 →L[ℝ] ℝ := (0 : E3 →L[ℝ] ℝ) - ((lX + lY) + lZ)

theorem fS7_o : fS7 o0 = -1 ∧ fS7 o1 = -1 ∧ fS7 o2 = -1 ∧ fS7 o3 = 1
    ∧ fS7 o4 = 1 ∧ fS7 o5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [fS7, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply]
     norm_num [lX_o.1, lX_o.2.1, lX_o.2.2.1, lX_o.2.2.2.1,
       lX_o.2.2.2.2.1, lX_o.2.2.2.2.2, lY_o.1, lY_o.2.1,
       lY_o.2.2.1, lY_o.2.2.2.1, lY_o.2.2.2.2.1, lY_o.2.2.2.2.2,
       lZ_o.1, lZ_o.2.1, lZ_o.2.2.1, lZ_o.2.2.2.1,
       lZ_o.2.2.2.2.1, lZ_o.2.2.2.2.2])

theorem hull_fmmm_ge : ∀ z ∈ convexHull ℝ ((fmmm : Finset E3) : Set E3),
    1 ≤ fS7 z := by
  intro z hz
  have hsub : ((fmmm : Finset E3) : Set E3) ⊆ {w : E3 | 1 ≤ fS7 w} := by
    intro w hw
    have hcasi : w = o3 ∨ w = o4 ∨ w = o5 := by
      simpa [fmmm] using hw
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [Set.mem_setOf_eq]
    · rw [fS7_o.2.2.2.1]
    · rw [fS7_o.2.2.2.2.1]
    · rw [fS7_o.2.2.2.2.2]
  exact convexHull_min hsub
    (convex_halfSpace_ge (LinearMap.isLinear fS7.toLinearMap) 1) hz

/-! ## Il fan del polo nord: σ4 e le quattro facce attorno a o2 -/

/-- La rotazione di π/2 attorno all'asse z: (x,y,z) ↦ (−y,x,z). -/
def sigma4 : E3 ≃ₗᵢ[ℝ] E3 := scambioXY.trans segnoX

theorem sigma4_o : sigma4 o0 = o1 ∧ sigma4 o1 = o3 ∧ sigma4 o2 = o2 ∧
    sigma4 o3 = o4 ∧ sigma4 o4 = o0 ∧ sigma4 o5 = o5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [sigma4, scambioXY, segnoX, o0, o1, o2, o3, o4, o5,
        Equiv.swap_apply_def, LinearIsometryEquiv.piLpCongrLeft,
        LinearIsometryEquiv.piLpCongrRight])

theorem sigma4_overtset :
    (⇑sigma4) '' (verticiOtta : Set E3) = (verticiOtta : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [sigma4_o.1, sigma4_o.2.1, sigma4_o.2.2.1, sigma4_o.2.2.2.1,
        sigma4_o.2.2.2.2.1, sigma4_o.2.2.2.2.2] <;>
      simp [verticiOtta]
  · intro hz
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h <;> subst h
    · exact ⟨o4, by simp [verticiOtta], sigma4_o.2.2.2.2.1⟩
    · exact ⟨o0, by simp [verticiOtta], sigma4_o.1⟩
    · exact ⟨o2, by simp [verticiOtta], sigma4_o.2.2.1⟩
    · exact ⟨o1, by simp [verticiOtta], sigma4_o.2.1⟩
    · exact ⟨o3, by simp [verticiOtta], sigma4_o.2.2.2.1⟩
    · exact ⟨o5, by simp [verticiOtta], sigma4_o.2.2.2.2.2⟩

theorem o3_ne_o2 : o3 ≠ o2 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 0) h
  simp [o3, o2] at this

theorem o4_ne_o2 : o4 ≠ o2 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 1) h
  simp [o4, o2] at this

theorem sigma4_N0 : (⇑sigma4.toAffineIsometryEquiv) '' (convexHull ℝ ((facciaOtta : Finset E3) : Set E3))
    = convexHull ℝ ((fmpp : Finset E3) : Set E3) := by
  have haff : (⇑sigma4.toAffineIsometryEquiv) '' (convexHull ℝ ((facciaOtta : Finset E3) : Set E3))
      = convexHull ℝ ((⇑sigma4.toAffineIsometryEquiv) '' ((facciaOtta : Finset E3) : Set E3)) :=
    AffineMap.image_convexHull sigma4.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑sigma4.toAffineIsometryEquiv) u = sigma4 u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
      simpa [facciaOtta] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [sigma4_o.1, sigma4_o.2.1, sigma4_o.2.2.1] <;>
      simp [fmpp]
  · intro hz
    have hcasi : z = o3 ∨ z = o1 ∨ z = o2 := by
      simpa [fmpp] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o1, by simp [facciaOtta], sigma4_o.2.1⟩
    · exact ⟨o0, by simp [facciaOtta], sigma4_o.1⟩
    · exact ⟨o2, by simp [facciaOtta], sigma4_o.2.2.1⟩

theorem sigma4_N1 : (⇑sigma4.toAffineIsometryEquiv) '' (convexHull ℝ ((fmpp : Finset E3) : Set E3))
    = convexHull ℝ ((fmmp : Finset E3) : Set E3) := by
  have haff : (⇑sigma4.toAffineIsometryEquiv) '' (convexHull ℝ ((fmpp : Finset E3) : Set E3))
      = convexHull ℝ ((⇑sigma4.toAffineIsometryEquiv) '' ((fmpp : Finset E3) : Set E3)) :=
    AffineMap.image_convexHull sigma4.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑sigma4.toAffineIsometryEquiv) u = sigma4 u := rfl
    rw [hcv]
    have hcasi : u = o3 ∨ u = o1 ∨ u = o2 := by
      simpa [fmpp] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [sigma4_o.2.2.2.1, sigma4_o.2.1, sigma4_o.2.2.1] <;>
      simp [fmmp]
  · intro hz
    have hcasi : z = o3 ∨ z = o4 ∨ z = o2 := by
      simpa [fmmp] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o1, by simp [fmpp], sigma4_o.2.1⟩
    · exact ⟨o3, by simp [fmpp], sigma4_o.2.2.2.1⟩
    · exact ⟨o2, by simp [fmpp], sigma4_o.2.2.1⟩

theorem sigma4_N2 : (⇑sigma4.toAffineIsometryEquiv) '' (convexHull ℝ ((fmmp : Finset E3) : Set E3))
    = convexHull ℝ ((fpmp : Finset E3) : Set E3) := by
  have haff : (⇑sigma4.toAffineIsometryEquiv) '' (convexHull ℝ ((fmmp : Finset E3) : Set E3))
      = convexHull ℝ ((⇑sigma4.toAffineIsometryEquiv) '' ((fmmp : Finset E3) : Set E3)) :=
    AffineMap.image_convexHull sigma4.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑sigma4.toAffineIsometryEquiv) u = sigma4 u := rfl
    rw [hcv]
    have hcasi : u = o3 ∨ u = o4 ∨ u = o2 := by
      simpa [fmmp] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [sigma4_o.2.2.2.1, sigma4_o.2.2.2.2.1, sigma4_o.2.2.1] <;>
      simp [fpmp]
  · intro hz
    have hcasi : z = o0 ∨ z = o4 ∨ z = o2 := by
      simpa [fpmp] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o4, by simp [fmmp], sigma4_o.2.2.2.2.1⟩
    · exact ⟨o3, by simp [fmmp], sigma4_o.2.2.2.1⟩
    · exact ⟨o2, by simp [fmmp], sigma4_o.2.2.1⟩

theorem sigma4_N3 : (⇑sigma4.toAffineIsometryEquiv) '' (convexHull ℝ ((fpmp : Finset E3) : Set E3))
    = convexHull ℝ ((facciaOtta : Finset E3) : Set E3) := by
  have haff : (⇑sigma4.toAffineIsometryEquiv) '' (convexHull ℝ ((fpmp : Finset E3) : Set E3))
      = convexHull ℝ ((⇑sigma4.toAffineIsometryEquiv) '' ((fpmp : Finset E3) : Set E3)) :=
    AffineMap.image_convexHull sigma4.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑sigma4.toAffineIsometryEquiv) u = sigma4 u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o4 ∨ u = o2 := by
      simpa [fpmp] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [sigma4_o.1, sigma4_o.2.2.2.2.1, sigma4_o.2.2.1] <;>
      simp [facciaOtta]
  · intro hz
    have hcasi : z = o0 ∨ z = o1 ∨ z = o2 := by
      simpa [facciaOtta] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o4, by simp [fpmp], sigma4_o.2.2.2.2.1⟩
    · exact ⟨o0, by simp [fpmp], sigma4_o.1⟩
    · exact ⟨o2, by simp [fpmp], sigma4_o.2.2.1⟩

theorem hull_fmpp_sub : convexHull ℝ ((fmpp : Finset E3) : Set E3)
    ⊆ ottaedro.toSet := by
  apply convexHull_mono
  intro z hz
  have hcasi : z = o3 ∨ z = o1 ∨ z = o2 := by
    simpa [fmpp] using hz
  rcases hcasi with h | h | h <;> subst h <;> simp [ottaedro, verticiOtta]

theorem hull_fmmp_sub : convexHull ℝ ((fmmp : Finset E3) : Set E3)
    ⊆ ottaedro.toSet := by
  apply convexHull_mono
  intro z hz
  have hcasi : z = o3 ∨ z = o4 ∨ z = o2 := by
    simpa [fmmp] using hz
  rcases hcasi with h | h | h <;> subst h <;> simp [ottaedro, verticiOtta]

theorem hull_fpmp_sub : convexHull ℝ ((fpmp : Finset E3) : Set E3)
    ⊆ ottaedro.toSet := by
  apply convexHull_mono
  intro z hz
  have hcasi : z = o0 ∨ z = o4 ∨ z = o2 := by
    simpa [fpmp] using hz
  rcases hcasi with h | h | h <;> subst h <;> simp [ottaedro, verticiOtta]

theorem hull_facciaOtta_ne_fmpp : convexHull ℝ ((facciaOtta : Finset E3) : Set E3)
    ≠ convexHull ℝ ((fmpp : Finset E3) : Set E3) := by
  intro h
  have hw : o0 ∈ convexHull ℝ ((facciaOtta : Finset E3) : Set E3) :=
    subset_convexHull ℝ _ (by simp [facciaOtta])
  rw [h] at hw
  have := hull_fmpp_ge o0 hw
  rw [fN1_o.1] at this
  norm_num at this

theorem hull_facciaOtta_ne_fmmp : convexHull ℝ ((facciaOtta : Finset E3) : Set E3)
    ≠ convexHull ℝ ((fmmp : Finset E3) : Set E3) := by
  intro h
  have hw : o0 ∈ convexHull ℝ ((facciaOtta : Finset E3) : Set E3) :=
    subset_convexHull ℝ _ (by simp [facciaOtta])
  rw [h] at hw
  have := hull_fmmp_ge o0 hw
  rw [fN2_o.1] at this
  norm_num at this

theorem hull_facciaOtta_ne_fpmp : convexHull ℝ ((facciaOtta : Finset E3) : Set E3)
    ≠ convexHull ℝ ((fpmp : Finset E3) : Set E3) := by
  intro h
  have hw : o1 ∈ convexHull ℝ ((facciaOtta : Finset E3) : Set E3) :=
    subset_convexHull ℝ _ (by simp [facciaOtta])
  rw [h] at hw
  have := hull_fpmp_ge o1 hw
  rw [fN3_o.2.1] at this
  norm_num at this

theorem hull_fmpp_ne_fmmp : convexHull ℝ ((fmpp : Finset E3) : Set E3)
    ≠ convexHull ℝ ((fmmp : Finset E3) : Set E3) := by
  intro h
  have hw : o1 ∈ convexHull ℝ ((fmpp : Finset E3) : Set E3) :=
    subset_convexHull ℝ _ (by simp [fmpp])
  rw [h] at hw
  have := hull_fmmp_ge o1 hw
  rw [fN2_o.2.1] at this
  norm_num at this

theorem hull_fmpp_ne_fpmp : convexHull ℝ ((fmpp : Finset E3) : Set E3)
    ≠ convexHull ℝ ((fpmp : Finset E3) : Set E3) := by
  intro h
  have hw : o3 ∈ convexHull ℝ ((fmpp : Finset E3) : Set E3) :=
    subset_convexHull ℝ _ (by simp [fmpp])
  rw [h] at hw
  have := hull_fpmp_ge o3 hw
  rw [fN3_o.2.2.2.1] at this
  norm_num at this

theorem hull_fmmp_ne_fpmp : convexHull ℝ ((fmmp : Finset E3) : Set E3)
    ≠ convexHull ℝ ((fpmp : Finset E3) : Set E3) := by
  intro h
  have hw : o3 ∈ convexHull ℝ ((fmmp : Finset E3) : Set E3) :=
    subset_convexHull ℝ _ (by simp [fmmp])
  rw [h] at hw
  have := hull_fpmp_ge o3 hw
  rw [fN3_o.2.2.2.1] at this
  norm_num at this


/-! ## IL FAN DEL POLO NORD: o2 è 4-ciclico -/

set_option maxHeartbeats 1600000 in
theorem o2_ciclico : ottaedro.IsCyclicVertex o2 4 := by
  refine ⟨⟨![convexHull ℝ ((facciaOtta : Finset E3) : Set E3), convexHull ℝ ((fmpp : Finset E3) : Set E3), convexHull ℝ ((fmmp : Finset E3) : Set E3), convexHull ℝ ((fpmp : Finset E3) : Set E3)], ?_, ?_, ?_, ?_,
    sigma4.toAffineIsometryEquiv, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- isFacet
    intro i
    fin_cases i
    · exact facciaOtta_isFacet
    · show ottaedro.IsFacet (convexHull ℝ ((fmpp : Finset E3) : Set E3))
      rw [← segnoX_T₀]
      exact isFacet_image ottaedro _
        (preserva_toSet_otta segnoX segnoX_overtset) facciaOtta_isFacet
    · show ottaedro.IsFacet (convexHull ℝ ((fmmp : Finset E3) : Set E3))
      rw [← sXY_T₀]
      exact isFacet_image ottaedro _
        (preserva_toSet_otta _ (overtset_trans segnoX segnoY
          segnoX_overtset segnoY_overtset)) facciaOtta_isFacet
    · show ottaedro.IsFacet (convexHull ℝ ((fpmp : Finset E3) : Set E3))
      rw [← segnoY_T₀]
      exact isFacet_image ottaedro _
        (preserva_toSet_otta segnoY segnoY_overtset) facciaOtta_isFacet
  · -- mem_v
    intro i
    fin_cases i
    · exact subset_convexHull ℝ _ (by simp [facciaOtta])
    · exact subset_convexHull ℝ _ (by simp [fmpp])
    · exact subset_convexHull ℝ _ (by simp [fmmp])
    · exact subset_convexHull ℝ _ (by simp [fpmp])
  · -- distinte
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hull_facciaOtta_ne_fmpp
    · exact absurd hij hull_facciaOtta_ne_fmmp
    · exact absurd hij hull_facciaOtta_ne_fpmp
    · exact absurd hij.symm hull_facciaOtta_ne_fmpp
    · rfl
    · exact absurd hij hull_fmpp_ne_fmmp
    · exact absurd hij hull_fmpp_ne_fpmp
    · exact absurd hij.symm hull_facciaOtta_ne_fmmp
    · exact absurd hij.symm hull_fmpp_ne_fmmp
    · rfl
    · exact absurd hij hull_fmmp_ne_fpmp
    · exact absurd hij.symm hull_facciaOtta_ne_fpmp
    · exact absurd hij.symm hull_fmpp_ne_fpmp
    · exact absurd hij.symm hull_fmmp_ne_fpmp
    · rfl
  · -- complete
    intro F hF ho2F
    rcases facet_classification_otta hF with h | h | h | h | h | h | h | h <;>
      subst h
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨3, rfl⟩
    · exfalso
      have := hull_fppm_ge o2 ho2F
      rw [fS0_o.2.2.1] at this
      norm_num at this
    · exact ⟨2, rfl⟩
    · exfalso
      have := hull_fmpm_ge o2 ho2F
      rw [fS1_o.2.2.1] at this
      norm_num at this
    · exfalso
      have := hull_fpmm_ge o2 ho2F
      rw [fS2_o.2.2.1] at this
      norm_num at this
    · exfalso
      have := hull_fmmm_ge o2 ho2F
      rw [fS7_o.2.2.1] at this
      norm_num at this
  · -- fissa_v
    exact sigma4_o.2.2.1
  · -- preserva
    exact preserva_toSet_otta sigma4 sigma4_overtset
  · -- ruota
    intro i
    fin_cases i
    · have h1 : finRotate 4 (0 : Fin 4) = 1 := by decide
      show (⇑sigma4.toAffineIsometryEquiv) '' (convexHull ℝ ((facciaOtta : Finset E3) : Set E3))
        = ![convexHull ℝ ((facciaOtta : Finset E3) : Set E3), convexHull ℝ ((fmpp : Finset E3) : Set E3), convexHull ℝ ((fmmp : Finset E3) : Set E3), convexHull ℝ ((fpmp : Finset E3) : Set E3)] (finRotate 4 0)
      rw [h1]
      exact sigma4_N0
    · have h1 : finRotate 4 (1 : Fin 4) = 2 := by decide
      show (⇑sigma4.toAffineIsometryEquiv) '' (convexHull ℝ ((fmpp : Finset E3) : Set E3))
        = ![convexHull ℝ ((facciaOtta : Finset E3) : Set E3), convexHull ℝ ((fmpp : Finset E3) : Set E3), convexHull ℝ ((fmmp : Finset E3) : Set E3), convexHull ℝ ((fpmp : Finset E3) : Set E3)] (finRotate 4 1)
      rw [h1]
      exact sigma4_N1
    · have h1 : finRotate 4 (2 : Fin 4) = 3 := by decide
      show (⇑sigma4.toAffineIsometryEquiv) '' (convexHull ℝ ((fmmp : Finset E3) : Set E3))
        = ![convexHull ℝ ((facciaOtta : Finset E3) : Set E3), convexHull ℝ ((fmpp : Finset E3) : Set E3), convexHull ℝ ((fmmp : Finset E3) : Set E3), convexHull ℝ ((fpmp : Finset E3) : Set E3)] (finRotate 4 2)
      rw [h1]
      exact sigma4_N2
    · have h1 : finRotate 4 (3 : Fin 4) = 0 := by decide
      show (⇑sigma4.toAffineIsometryEquiv) '' (convexHull ℝ ((fpmp : Finset E3) : Set E3))
        = ![convexHull ℝ ((facciaOtta : Finset E3) : Set E3), convexHull ℝ ((fmpp : Finset E3) : Set E3), convexHull ℝ ((fmmp : Finset E3) : Set E3), convexHull ℝ ((fpmp : Finset E3) : Set E3)] (finRotate 4 3)
      rw [h1]
      exact sigma4_N3
  · -- spigolo
    intro i
    fin_cases i
    · refine ⟨o1, o1_ne_o2, ?_⟩
      constructor
      · show o1 ∈ convexHull ℝ ((facciaOtta : Finset E3) : Set E3)
        exact subset_convexHull ℝ _ (by simp [facciaOtta])
      · show o1 ∈ convexHull ℝ ((fmpp : Finset E3) : Set E3)
        exact subset_convexHull ℝ _ (by simp [fmpp])
    · refine ⟨o3, o3_ne_o2, ?_⟩
      constructor
      · show o3 ∈ convexHull ℝ ((fmpp : Finset E3) : Set E3)
        exact subset_convexHull ℝ _ (by simp [fmpp])
      · show o3 ∈ convexHull ℝ ((fmmp : Finset E3) : Set E3)
        exact subset_convexHull ℝ _ (by simp [fmmp])
    · refine ⟨o4, o4_ne_o2, ?_⟩
      constructor
      · show o4 ∈ convexHull ℝ ((fmmp : Finset E3) : Set E3)
        exact subset_convexHull ℝ _ (by simp [fmmp])
      · show o4 ∈ convexHull ℝ ((fpmp : Finset E3) : Set E3)
        exact subset_convexHull ℝ _ (by simp [fpmp])
    · refine ⟨o0, o0_ne_o2, ?_⟩
      constructor
      · show o0 ∈ convexHull ℝ ((fpmp : Finset E3) : Set E3)
        exact subset_convexHull ℝ _ (by simp [fpmp])
      · show o0 ∈ convexHull ℝ ((facciaOtta : Finset E3) : Set E3)
        exact subset_convexHull ℝ _ (by simp [facciaOtta])
  · -- spigolo_due
    intro i j x hx hxv hxj
    fin_cases i <;> fin_cases j
    · exact Or.inl rfl
    · exact Or.inr (by decide)
    · exfalso
      have hx1 : x ∈ convexHull ℝ ((facciaOtta : Finset E3) : Set E3) := hx.1
      have hx2 : x ∈ convexHull ℝ ((fmpp : Finset E3) : Set E3) := hx.2
      have hxj3 : x ∈ convexHull ℝ ((fmmp : Finset E3) : Set E3) := hxj
      have ea : (lX + lY + lZ) x = 1 :=
      le_antisymm (toSet_otta_le x (T₀_sub_toSet hx1)) (T₀_ge_uno x hx1)
      have eb : fN2 x = 1 :=
      le_antisymm (toSet_fN2_le x (hull_fmmp_sub hxj3)) (hull_fmmp_ge x hxj3)
      have hlz : lZ x = 1 := by
        simp only [fN1, fN2, fN3, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.sub_apply] at ea eb
        linarith
      exact hxv (polo_nord x (T₀_sub_toSet hx.1) hlz)
    · exfalso
      have hx1 : x ∈ convexHull ℝ ((facciaOtta : Finset E3) : Set E3) := hx.1
      have hx2 : x ∈ convexHull ℝ ((fmpp : Finset E3) : Set E3) := hx.2
      have hxj3 : x ∈ convexHull ℝ ((fpmp : Finset E3) : Set E3) := hxj
      have ea : fN1 x = 1 :=
      le_antisymm (toSet_fN1_le x (hull_fmpp_sub hx2)) (hull_fmpp_ge x hx2)
      have eb : fN3 x = 1 :=
      le_antisymm (toSet_fN3_le x (hull_fpmp_sub hxj3)) (hull_fpmp_ge x hxj3)
      have hlz : lZ x = 1 := by
        simp only [fN1, fN2, fN3, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.sub_apply] at ea eb
        linarith
      exact hxv (polo_nord x (T₀_sub_toSet hx.1) hlz)
    · exfalso
      have hx1 : x ∈ convexHull ℝ ((fmpp : Finset E3) : Set E3) := hx.1
      have hx2 : x ∈ convexHull ℝ ((fmmp : Finset E3) : Set E3) := hx.2
      have hxj3 : x ∈ convexHull ℝ ((facciaOtta : Finset E3) : Set E3) := hxj
      have ea : (lX + lY + lZ) x = 1 :=
      le_antisymm (toSet_otta_le x (T₀_sub_toSet hxj3)) (T₀_ge_uno x hxj3)
      have eb : fN2 x = 1 :=
      le_antisymm (toSet_fN2_le x (hull_fmmp_sub hx2)) (hull_fmmp_ge x hx2)
      have hlz : lZ x = 1 := by
        simp only [fN1, fN2, fN3, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.sub_apply] at ea eb
        linarith
      exact hxv (polo_nord x (hull_fmpp_sub hx.1) hlz)
    · exact Or.inl rfl
    · exact Or.inr (by decide)
    · exfalso
      have hx1 : x ∈ convexHull ℝ ((fmpp : Finset E3) : Set E3) := hx.1
      have hx2 : x ∈ convexHull ℝ ((fmmp : Finset E3) : Set E3) := hx.2
      have hxj3 : x ∈ convexHull ℝ ((fpmp : Finset E3) : Set E3) := hxj
      have ea : fN1 x = 1 :=
      le_antisymm (toSet_fN1_le x (hull_fmpp_sub hx1)) (hull_fmpp_ge x hx1)
      have eb : fN3 x = 1 :=
      le_antisymm (toSet_fN3_le x (hull_fpmp_sub hxj3)) (hull_fpmp_ge x hxj3)
      have hlz : lZ x = 1 := by
        simp only [fN1, fN2, fN3, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.sub_apply] at ea eb
        linarith
      exact hxv (polo_nord x (hull_fmpp_sub hx.1) hlz)
    · exfalso
      have hx1 : x ∈ convexHull ℝ ((fmmp : Finset E3) : Set E3) := hx.1
      have hx2 : x ∈ convexHull ℝ ((fpmp : Finset E3) : Set E3) := hx.2
      have hxj3 : x ∈ convexHull ℝ ((facciaOtta : Finset E3) : Set E3) := hxj
      have ea : (lX + lY + lZ) x = 1 :=
      le_antisymm (toSet_otta_le x (T₀_sub_toSet hxj3)) (T₀_ge_uno x hxj3)
      have eb : fN2 x = 1 :=
      le_antisymm (toSet_fN2_le x (hull_fmmp_sub hx1)) (hull_fmmp_ge x hx1)
      have hlz : lZ x = 1 := by
        simp only [fN1, fN2, fN3, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.sub_apply] at ea eb
        linarith
      exact hxv (polo_nord x (hull_fmmp_sub hx.1) hlz)
    · exfalso
      have hx1 : x ∈ convexHull ℝ ((fmmp : Finset E3) : Set E3) := hx.1
      have hx2 : x ∈ convexHull ℝ ((fpmp : Finset E3) : Set E3) := hx.2
      have hxj3 : x ∈ convexHull ℝ ((fmpp : Finset E3) : Set E3) := hxj
      have ea : fN1 x = 1 :=
      le_antisymm (toSet_fN1_le x (hull_fmpp_sub hxj3)) (hull_fmpp_ge x hxj3)
      have eb : fN3 x = 1 :=
      le_antisymm (toSet_fN3_le x (hull_fpmp_sub hx2)) (hull_fpmp_ge x hx2)
      have hlz : lZ x = 1 := by
        simp only [fN1, fN2, fN3, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.sub_apply] at ea eb
        linarith
      exact hxv (polo_nord x (hull_fmmp_sub hx.1) hlz)
    · exact Or.inl rfl
    · exact Or.inr (by decide)
    · exact Or.inr (by decide)
    · exfalso
      have hx1 : x ∈ convexHull ℝ ((fpmp : Finset E3) : Set E3) := hx.1
      have hx2 : x ∈ convexHull ℝ ((facciaOtta : Finset E3) : Set E3) := hx.2
      have hxj3 : x ∈ convexHull ℝ ((fmpp : Finset E3) : Set E3) := hxj
      have ea : fN1 x = 1 :=
      le_antisymm (toSet_fN1_le x (hull_fmpp_sub hxj3)) (hull_fmpp_ge x hxj3)
      have eb : fN3 x = 1 :=
      le_antisymm (toSet_fN3_le x (hull_fpmp_sub hx1)) (hull_fpmp_ge x hx1)
      have hlz : lZ x = 1 := by
        simp only [fN1, fN2, fN3, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.sub_apply] at ea eb
        linarith
      exact hxv (polo_nord x (hull_fpmp_sub hx.1) hlz)
    · exfalso
      have hx1 : x ∈ convexHull ℝ ((fpmp : Finset E3) : Set E3) := hx.1
      have hx2 : x ∈ convexHull ℝ ((facciaOtta : Finset E3) : Set E3) := hx.2
      have hxj3 : x ∈ convexHull ℝ ((fmmp : Finset E3) : Set E3) := hxj
      have ea : (lX + lY + lZ) x = 1 :=
      le_antisymm (toSet_otta_le x (T₀_sub_toSet hx2)) (T₀_ge_uno x hx2)
      have eb : fN2 x = 1 :=
      le_antisymm (toSet_fN2_le x (hull_fmmp_sub hxj3)) (hull_fmmp_ge x hxj3)
      have hlz : lZ x = 1 := by
        simp only [fN1, fN2, fN3, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.sub_apply] at ea eb
        linarith
      exact hxv (polo_nord x (hull_fpmp_sub hx.1) hlz)
    · exact Or.inl rfl

/-! ## Tutti i vertici sono 4-ciclici e IL TESTIMONE -/

theorem rotDiag_overtset :
    (⇑rotDiag) '' (verticiOtta : Set E3) = (verticiOtta : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [rotDiag_o.1, rotDiag_o.2.1, rotDiag_o.2.2.1,
        rotDiag_o.2.2.2.1, rotDiag_o.2.2.2.2.1, rotDiag_o.2.2.2.2.2] <;>
      simp [verticiOtta]
  · intro hz
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h <;> subst h
    · exact ⟨o2, by simp [verticiOtta], rotDiag_o.2.2.1⟩
    · exact ⟨o0, by simp [verticiOtta], rotDiag_o.1⟩
    · exact ⟨o1, by simp [verticiOtta], rotDiag_o.2.1⟩
    · exact ⟨o5, by simp [verticiOtta], rotDiag_o.2.2.2.2.2⟩
    · exact ⟨o3, by simp [verticiOtta], rotDiag_o.2.2.2.1⟩
    · exact ⟨o4, by simp [verticiOtta], rotDiag_o.2.2.2.2.1⟩

theorem ottaedro_vertici_ciclici :
    ∀ v ∈ ottaedro.vertices, ottaedro.IsCyclicVertex v 4 := by
  intro v hv
  rcases mem_verticiOtta_iff.mp (by exact_mod_cast hv) with
    h | h | h | h | h | h <;> subst h
  · -- o0 = rotDiag o2
    have h1 : (rotDiag.toAffineIsometryEquiv) o2 = o0 := rotDiag_o.2.2.1
    rw [← h1]
    exact isCyclicVertex_image ottaedro _
      (preserva_toSet_otta rotDiag rotDiag_overtset) o2_ciclico
  · -- o1 = (rotDiag.trans rotDiag) o2
    have h1 : ((rotDiag.trans rotDiag).toAffineIsometryEquiv) o2 = o1 := by
      show rotDiag (rotDiag o2) = o1
      rw [rotDiag_o.2.2.1, rotDiag_o.1]
    rw [← h1]
    exact isCyclicVertex_image ottaedro _
      (preserva_toSet_otta _ (overtset_trans rotDiag rotDiag
        rotDiag_overtset rotDiag_overtset)) o2_ciclico
  · exact o2_ciclico
  · -- o3 = (rotDiag.trans segnoX) o2
    have h1 : ((rotDiag.trans segnoX).toAffineIsometryEquiv) o2 = o3 := by
      show segnoX (rotDiag o2) = o3
      rw [rotDiag_o.2.2.1, segnoX_o.1]
    rw [← h1]
    exact isCyclicVertex_image ottaedro _
      (preserva_toSet_otta _ (overtset_trans rotDiag segnoX
        rotDiag_overtset segnoX_overtset)) o2_ciclico
  · -- o4 = ((rotDiag.trans rotDiag).trans segnoY) o2
    have h1 : (((rotDiag.trans rotDiag).trans segnoY).toAffineIsometryEquiv) o2
        = o4 := by
      show segnoY (rotDiag (rotDiag o2)) = o4
      rw [rotDiag_o.2.2.1, rotDiag_o.1, segnoY_o.2.1]
    rw [← h1]
    exact isCyclicVertex_image ottaedro _
      (preserva_toSet_otta _ (overtset_trans _ segnoY
        (overtset_trans rotDiag rotDiag rotDiag_overtset rotDiag_overtset)
        segnoY_overtset)) o2_ciclico
  · -- o5 = segnoZ o2
    have h1 : (segnoZ.toAffineIsometryEquiv) o2 = o5 := segnoZ_o.2.2.1
    rw [← h1]
    exact isCyclicVertex_image ottaedro _
      (preserva_toSet_otta segnoZ segnoZ_overtset) o2_ciclico

/-- L'OTTAEDRO È CICLICAMENTE REGOLARE DI TIPO (3,4): terzo testimone. -/
theorem ottaedro_cyclicallyRegular : ottaedro.IsCyclicallyRegularOfType 3 4 :=
  ⟨ottaedro_finrank, by norm_num, by norm_num, Real.sqrt 2, by positivity,
    otta_faccette_regolari, ottaedro_vertici_ciclici⟩

