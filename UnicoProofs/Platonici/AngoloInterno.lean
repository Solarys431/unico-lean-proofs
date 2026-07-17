import Mathlib

noncomputable section

open Real Set Metric
open scoped EuclideanGeometry RealInnerProductSpace

namespace AngoloInterno

/-!
The file uses oriented angles only to remember on which side of a chord the
third point lies.  The final statement is about Mathlib's ordinary (unoriented)
Euclidean angle.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] [Module.Oriented ℝ E (Fin 2)]

/-- The numerical interior angle of a regular `p`-gon. -/
def regularInteriorAngle (p : ℕ) : ℝ := ((p : ℝ) - 2) * π / p

/--
The inscribed-angle calculation needed for a regular polygon.  Here `x` is
the point of the circle lying on the short arc from `y` to `z`; the last
hypothesis is the orientation-only certificate selecting that arc.  In a
regular `p`-gon, `y` and `z` are the angular predecessor and successor of `x`,
so their oriented central separation is `4π/p`.
-/
theorem angle_eq_regularInteriorAngle_of_center_oangle
    (p : ℕ) (hp : 3 ≤ p) (s : EuclideanGeometry.Sphere E) {y x z : E}
    (hy : y ∈ s) (hx : x ∈ s) (hz : z ∈ s)
    (hxy : x ≠ y) (hxz : x ≠ z)
    (hcentral : ∡ y s.center z =
      (((4 : ℝ) * π / p : ℝ) : Real.Angle))
    (hside : (∡ y x z).sign = -1) :
    ∠ y x z = regularInteriorAngle p := by
  have hpR : (0 : ℝ) < p := by positivity
  let a : ℝ := 2 * π / p
  let α : Real.Angle := (a : Real.Angle)
  have ha0 : 0 < a := by
    dsimp [a]
    positivity
  have haπ : a < π := by
    dsimp [a]
    rw [div_lt_iff₀ hpR]
    have hpR3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith [Real.pi_pos]
  have hαsign : α.sign = 1 := by
    rw [← Real.Angle.toReal_mem_Ioo_iff_sign_pos]
    have hto : α.toReal = a :=
      Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith [Real.pi_pos], haπ.le⟩
    rw [hto]
    exact ⟨ha0, haπ⟩
  have hdouble := EuclideanGeometry.Sphere.oangle_center_eq_two_zsmul_oangle
    hy hx hz hxy hxz
  have htwo : (2 : ℤ) • (∡ y x z) = (2 : ℤ) • α := by
    rw [← hdouble, hcentral]
    rw [← Real.Angle.coe_zsmul]
    congr 1
    dsimp [α, a]
    ring
  have hbranch : ∡ y x z = α + π := by
    rcases Real.Angle.two_zsmul_eq_iff.mp htwo with hfirst | hsecond
    · exfalso
      rw [hfirst, hαsign] at hside
      norm_num at hside
    · exact hsecond
  let β : ℝ := regularInteriorAngle p
  have hβ0 : 0 ≤ β := by
    dsimp [β, regularInteriorAngle]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (show 2 ≤ p by omega)
    positivity
  have hβπ : β ≤ π := by
    dsimp [β, regularInteriorAngle]
    rw [div_le_iff₀ hpR]
    nlinarith [Real.pi_pos]
  have hbranch' : ∡ y x z = ((-β : ℝ) : Real.Angle) := by
    rw [hbranch]
    dsimp [α]
    rw [← Real.Angle.coe_add, ← Real.Angle.coe_neg,
      Real.Angle.angle_eq_iff_two_pi_dvd_sub]
    refine ⟨1, ?_⟩
    dsimp [a, β, regularInteriorAngle]
    push_cast
    field_simp
    ring
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal hxy.symm hxz.symm,
    hbranch']
  exact Real.Angle.abs_toReal_neg_coe_eq_self_iff.mpr ⟨hβ0, hβπ⟩

/-- The `j`-th point of the orbit of an affine isometry. -/
def orbitPoint (rho : E ≃ᵃⁱ[ℝ] E) (x0 : E) (j : ℕ) : E :=
  ((⇑rho)^[j]) x0

/--
`y` and `z` are the two angularly consecutive points around `x`, independently
of the numbering of the orbit.  The two equalities say that the open sectors
from `y` to `x` and from `x` to `z` are the elementary sectors `2π/p`; the
sign fixes the cyclic order.  Thus a step `2πk/p` in the supplied orbit
parametrisation cannot turn diagonals into neighbours.
-/
def AngularNeighbors (p : ℕ) (c y x z : E) : Prop :=
  y ≠ c ∧ x ≠ c ∧ z ≠ c ∧
    ∡ y c x = (((2 : ℝ) * π / p : ℝ) : Real.Angle) ∧
    ∡ x c z = (((2 : ℝ) * π / p : ℝ) : Real.Angle) ∧
    (∡ y x z).sign = -1

/-- An affine isometry fixing `c` keeps its whole orbit on the circle about `c`. -/
theorem orbitPoint_mem_sphere (rho : E ≃ᵃⁱ[ℝ] E) (x0 c : E)
    (hc : rho c = c) (j : ℕ) :
    orbitPoint rho x0 j ∈
      (EuclideanGeometry.Sphere.mk c (dist x0 c) : EuclideanGeometry.Sphere E) := by
  rw [EuclideanGeometry.mem_sphere]
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [orbitPoint, Function.iterate_succ_apply']
      change dist (rho (orbitPoint rho x0 j)) c = dist x0 c
      calc
        dist (rho (orbitPoint rho x0 j)) c =
            dist (rho (orbitPoint rho x0 j)) (rho c) := by rw [hc]
        _ = dist (orbitPoint rho x0 j) c := rho.dist_map _ _
        _ = dist x0 c := ih

/--
The internal angle at an orbit vertex, stated with angular (hence hull)
neighbours rather than with predecessor/successor indices.  `hclosed` and
`hinj` certify that the displayed `Fin p` family is exactly a closed orbit of
`p` distinct points; `AngularNeighbors` is geometric and therefore immune to
a star parametrisation.
-/
theorem angle_at_orbit_vertex
    (p : ℕ) (hp : 3 ≤ p) (rho : E ≃ᵃⁱ[ℝ] E) (x0 c : E)
    (_hclosed : orbitPoint rho x0 p = x0) (hc : rho c = c)
    (hinj : Function.Injective (fun j : Fin p ↦ orbitPoint rho x0 (j : ℕ)))
    (iy ix iz : Fin p) (hiyx : iy ≠ ix) (hizx : iz ≠ ix)
    (hneighbors : AngularNeighbors p c
      (orbitPoint rho x0 iy) (orbitPoint rho x0 ix) (orbitPoint rho x0 iz)) :
    ∠ (orbitPoint rho x0 iy) (orbitPoint rho x0 ix) (orbitPoint rho x0 iz) =
      regularInteriorAngle p := by
  let s : EuclideanGeometry.Sphere E := ⟨c, dist x0 c⟩
  have hy : orbitPoint rho x0 iy ∈ s := orbitPoint_mem_sphere rho x0 c hc iy
  have hx : orbitPoint rho x0 ix ∈ s := orbitPoint_mem_sphere rho x0 c hc ix
  have hz : orbitPoint rho x0 iz ∈ s := orbitPoint_mem_sphere rho x0 c hc iz
  have hxy : orbitPoint rho x0 ix ≠ orbitPoint rho x0 iy := by
    exact fun h ↦ hiyx (hinj h.symm)
  have hxz : orbitPoint rho x0 ix ≠ orbitPoint rho x0 iz := by
    exact fun h ↦ hizx (hinj h.symm)
  rcases hneighbors with ⟨hyc, hxc, hzc, hyxC, hxzC, hside⟩
  have hcentral :
      ∡ (orbitPoint rho x0 iy) s.center (orbitPoint rho x0 iz) =
        (((4 : ℝ) * π / p : ℝ) : Real.Angle) := by
    rw [← EuclideanGeometry.oangle_add hyc hxc hzc, hyxC, hxzC]
    rw [← Real.Angle.coe_add]
    congr 1
    ring
  exact angle_eq_regularInteriorAngle_of_center_oangle p hp s hy hx hz hxy hxz
    hcentral hside

/--
The model pair of angular neighbours.  This lemma proves, rather than assumes,
the orientation sign that selects the convex angle.  It is the local geometric
reason the other solution of the doubled oriented angle is rejected.
-/
theorem rotation_pair_angularNeighbors
    (p : ℕ) (hp : 3 ≤ p) {u : E} (hu : u ≠ 0) :
    let a : Real.Angle := (((2 : ℝ) * π / p : ℝ) : Real.Angle)
    AngularNeighbors p 0 (EuclideanGeometry.o.rotation (-a) u) u
      (EuclideanGeometry.o.rotation a u) := by
  let ar : ℝ := 2 * π / p
  let a : Real.Angle := (ar : Real.Angle)
  dsimp only
  change AngularNeighbors p 0 (EuclideanGeometry.o.rotation (-a) u) u
    (EuclideanGeometry.o.rotation a u)
  have hpR : (0 : ℝ) < p := by positivity
  have har0 : 0 < ar := by
    dsimp [ar]
    positivity
  have harπ : ar < π := by
    dsimp [ar]
    rw [div_lt_iff₀ hpR]
    have hpR3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.Angle.sin a := by
    rw [Real.Angle.sin_coe]
    exact Real.sin_pos_of_pos_of_lt_pi har0 harπ
  have hcos : Real.Angle.cos a < 1 := by
    have hsq := a.cos_sq_add_sin_sq
    have hsne : Real.Angle.sin a ≠ 0 := ne_of_gt hsin
    have hcle : Real.Angle.cos a ≤ 1 := by
      simpa [a] using Real.cos_le_one ar
    nlinarith
  have hy0 : EuclideanGeometry.o.rotation (-a) u ≠ 0 := by simpa using hu
  have hz0 : EuclideanGeometry.o.rotation a u ≠ 0 := by simpa using hu
  refine ⟨hy0, hu, hz0, ?_, ?_, ?_⟩
  · simpa [EuclideanGeometry.oangle, a, ar] using
      EuclideanGeometry.o.oangle_rotation_self_left hu (-a)
  · simpa [EuclideanGeometry.oangle, a, ar] using
      EuclideanGeometry.o.oangle_rotation_self_right hu a
  · change (EuclideanGeometry.o.oangle
      (EuclideanGeometry.o.rotation (-a) u - u)
      (EuclideanGeometry.o.rotation a u - u)).sign = -1
    let J : E ≃ₗᵢ[ℝ] E := EuclideanGeometry.o.rightAngleRotation
    let co := Real.Angle.cos a
    let si := Real.Angle.sin a
    have hyvec : EuclideanGeometry.o.rotation (-a) u - u =
        (co - 1) • u + (-si) • J u := by
      dsimp [co, si, J]
      rw [EuclideanGeometry.o.rotation_apply]
      simp only [Real.Angle.cos_neg, Real.Angle.sin_neg]
      module
    have hzvec : EuclideanGeometry.o.rotation a u - u =
        (co - 1) • u + si • J u := by
      dsimp [co, si, J]
      rw [EuclideanGeometry.o.rotation_apply]
      module
    have hdet : (co - 1) * si - (-si) * (co - 1) < 0 := by
      dsimp [co, si]
      nlinarith
    have hright : (EuclideanGeometry.o.oangle u (J u)).sign = 1 := by
      have hangle : EuclideanGeometry.o.oangle u (J u) =
          ((π / 2 : ℝ) : Real.Angle) := by
        dsimp [J]
        rw [← EuclideanGeometry.o.rotation_pi_div_two,
          EuclideanGeometry.o.oangle_rotation_self_right hu]
      rw [hangle, Real.Angle.sign_coe_pi_div_two]
    rw [hyvec, hzvec,
      EuclideanGeometry.o.oangle_sign_smul_add_smul_smul_add_smul u (J u)
        (co - 1) (-si) (co - 1) si]
    rw [show SignType.sign ((co - 1) * si - (-si) * (co - 1)) = -1 by
      exact sign_eq_neg_one_iff.mpr hdet, hright]
    norm_num

/-- The ordinary angle between the model angular neighbours. -/
theorem angle_rotation_pair
    (p : ℕ) (hp : 3 ≤ p) {u : E} (hu : u ≠ 0) :
    ∠ (EuclideanGeometry.o.rotation
          (-(((2 : ℝ) * π / p : ℝ) : Real.Angle)) u) u
        (EuclideanGeometry.o.rotation
          ((((2 : ℝ) * π / p : ℝ) : Real.Angle)) u) =
      regularInteriorAngle p := by
  let a : Real.Angle := (((2 : ℝ) * π / p : ℝ) : Real.Angle)
  let s : EuclideanGeometry.Sphere E := ⟨0, ‖u‖⟩
  have hneigh : AngularNeighbors p 0 (EuclideanGeometry.o.rotation (-a) u) u
      (EuclideanGeometry.o.rotation a u) := by
    simpa [a] using rotation_pair_angularNeighbors p hp hu
  have hy : EuclideanGeometry.o.rotation (-a) u ∈ s := by
    rw [EuclideanGeometry.mem_sphere, EuclideanGeometry.Sphere.mk_center,
      EuclideanGeometry.Sphere.mk_radius, dist_zero_right]
    exact (EuclideanGeometry.o.rotation (-a)).norm_map u
  have hx : u ∈ s := by
    rw [EuclideanGeometry.mem_sphere, EuclideanGeometry.Sphere.mk_center,
      EuclideanGeometry.Sphere.mk_radius, dist_zero_right]
  have hz : EuclideanGeometry.o.rotation a u ∈ s := by
    rw [EuclideanGeometry.mem_sphere, EuclideanGeometry.Sphere.mk_center,
      EuclideanGeometry.Sphere.mk_radius, dist_zero_right]
    exact (EuclideanGeometry.o.rotation a).norm_map u
  have hpR : (0 : ℝ) < p := by positivity
  have har0 : 0 < (2 * π / (p : ℝ)) := by positivity
  have harπ : 2 * π / (p : ℝ) < π := by
    rw [div_lt_iff₀ hpR]
    have hpR3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith [Real.pi_pos]
  have hasign : a.sign = 1 := by
    rw [← Real.Angle.toReal_mem_Ioo_iff_sign_pos]
    have hto : a.toReal = 2 * π / (p : ℝ) := by
      dsimp [a]
      exact Real.Angle.toReal_coe_eq_self_iff.mpr
        ⟨by nlinarith [Real.pi_pos], harπ.le⟩
    rw [hto]
    exact ⟨har0, harπ⟩
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at hasign
    norm_num at hasign
  have hxy : u ≠ EuclideanGeometry.o.rotation (-a) u := by
    intro h
    have := (EuclideanGeometry.o.rotation_eq_self_iff_angle_eq_zero hu (-a)).mp h.symm
    exact ha0 (neg_eq_zero.mp this)
  have hxz : u ≠ EuclideanGeometry.o.rotation a u := by
    intro h
    have := (EuclideanGeometry.o.rotation_eq_self_iff_angle_eq_zero hu a).mp h.symm
    exact ha0 this
  rcases hneigh with ⟨hy0, hu0, hz0, hyx, hxz', hside⟩
  have hcentral : ∡ (EuclideanGeometry.o.rotation (-a) u) s.center
      (EuclideanGeometry.o.rotation a u) =
      (((4 : ℝ) * π / p : ℝ) : Real.Angle) := by
    rw [← EuclideanGeometry.oangle_add hy0 hu0 hz0, hyx, hxz']
    rw [← Real.Angle.coe_add]
    congr 1
    ring
  exact angle_eq_regularInteriorAngle_of_center_oangle p hp s hy hx hz hxy hxz
    hcentral hside

/-- Modular arithmetic for a torsion angle, in the form used to undo a star step. -/
theorem nsmul_rational_angle_of_mul_mod (p m j r : ℕ) (hp : 0 < p)
    (hmod : (j * m) % p = r % p) :
    j • ((((m : ℝ) / p * (2 * π) : ℝ)) : Real.Angle) =
      (((r : ℝ) / p * (2 * π) : ℝ) : Real.Angle) := by
  rw [← Real.Angle.coe_nsmul, Real.Angle.angle_eq_iff_two_pi_dvd_sub]
  obtain ⟨q, hq⟩ : (p : ℤ) ∣ (((j * m : ℕ) : ℤ) - (r : ℕ)) :=
    dvd_sub_comm.mp (Nat.ModEq.dvd hmod)
  refine ⟨q, ?_⟩
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqr : ((j * m : ℕ) : ℝ) - r = p * q := by exact_mod_cast hq
  rw [nsmul_eq_mul]
  have key : (j : ℝ) * ((m / p) * (2 * π)) - (r / p) * (2 * π) =
      (((j * m : ℕ) : ℝ) - r) / p * (2 * π) := by
    push_cast
    ring
  rw [key, hqr, mul_div_cancel_left₀ _ hp0]
  ring

/-- The orbit of a vector under the rotation with angle `theta`. -/
def rotationPoint (theta : Real.Angle) (u : E) (j : ℕ) : E :=
  EuclideanGeometry.o.rotation (j • theta) u

/--
An angle of additive order `p` has, around every one of its orbit points, two
orbit points at the genuine angular steps `-2π/p` and `2π/p`.  The indices
are obtained with the inverse of the possibly nontrivial star step modulo `p`.
-/
theorem exists_angularNeighbors_of_addOrderOf
    (p : ℕ) (hp : 3 ≤ p) (theta : Real.Angle) (horder : addOrderOf theta = p)
    {u : E} (hu : u ≠ 0) (ix : Fin p) :
    ∃ iy iz : Fin p,
      iy ≠ ix ∧ iz ≠ ix ∧
      AngularNeighbors p 0 (rotationPoint theta u iy) (rotationPoint theta u ix)
        (rotationPoint theta u iz) ∧
      ∠ (rotationPoint theta u iy) (rotationPoint theta u ix)
          (rotationPoint theta u iz) = regularInteriorAngle p := by
  haveI : NeZero p := ⟨by omega⟩
  letI : Fact (0 < 2 * π) := ⟨by positivity⟩
  have hp0 : 0 < p := by omega
  obtain ⟨m, hmp, hcop, htheta⟩ :=
    (AddCircle.addOrderOf_eq_pos_iff hp0).mp horder
  have hcop' : Nat.Coprime m p := hcop
  let unit : (ZMod p)ˣ := ZMod.unitOfCoprime m hcop'
  let jP : ℕ := ((unit⁻¹ : (ZMod p)ˣ) : ZMod p).val
  have hjPlt : jP < p := ZMod.val_lt _
  have hmUnit : ((m : ℕ) : ZMod p) = (unit : ZMod p) :=
    (ZMod.coe_unitOfCoprime m hcop').symm
  have hjmZ : ((jP * m : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    dsimp [jP]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id, hmUnit]
    exact unit.inv_mul
  have hmod1 : (jP * m) % p = 1 % p :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mp hjmZ
  have h1p : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  have hjP0 : jP ≠ 0 := by
    intro h
    rw [h, zero_mul, Nat.zero_mod, h1p] at hmod1
    omega
  let a : Real.Angle := (((2 : ℝ) * π / p : ℝ) : Real.Angle)
  have hjPtheta : jP • theta = a := by
    calc
      jP • theta = jP •
          ((((m : ℝ) / p * (2 * π) : ℝ)) : Real.Angle) := by
            rw [← htheta]
            rfl
      _ = (((1 : ℝ) / p * (2 * π) : ℝ) : Real.Angle) :=
        by simpa only [Nat.cast_one] using
          nsmul_rational_angle_of_mul_mod p m jP 1 hp0 hmod1
      _ = a := by
        dsimp [a]
        congr 1
        ring
  let jM : ℕ := p - jP
  have hjMlt : jM < p := by
    dsimp [jM]
    omega
  have hpTheta : p • theta = 0 := by
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero theta
  have hjMtheta : jM • theta = -a := by
    have hsum : jM • theta + jP • theta = 0 := by
      rw [← add_nsmul]
      dsimp [jM]
      rw [Nat.sub_add_cancel hjPlt.le, hpTheta]
    rw [hjPtheta] at hsum
    exact eq_neg_of_add_eq_zero_left hsum
  let iy : Fin p :=
    ⟨((ix : ℕ) + jM) % p, Nat.mod_lt _ hp0⟩
  let iz : Fin p :=
    ⟨((ix : ℕ) + jP) % p, Nat.mod_lt _ hp0⟩
  let x : E := rotationPoint theta u ix
  have hx0 : x ≠ 0 := by
    dsimp [x, rotationPoint]
    simpa using hu
  have hiytheta : (iy : ℕ) • theta = (ix : ℕ) • theta + (-a) := by
    calc
      (iy : ℕ) • theta = (((ix : ℕ) + jM) % p) • theta := rfl
      _ = (((ix : ℕ) + jM) % addOrderOf theta) • theta := by rw [horder]
      _ = ((ix : ℕ) + jM) • theta := mod_addOrderOf_nsmul theta _
      _ = (ix : ℕ) • theta + jM • theta := add_nsmul _ _ _
      _ = (ix : ℕ) • theta + (-a) := by rw [hjMtheta]
  have hiztheta : (iz : ℕ) • theta = (ix : ℕ) • theta + a := by
    calc
      (iz : ℕ) • theta = (((ix : ℕ) + jP) % p) • theta := rfl
      _ = (((ix : ℕ) + jP) % addOrderOf theta) • theta := by rw [horder]
      _ = ((ix : ℕ) + jP) • theta := mod_addOrderOf_nsmul theta _
      _ = (ix : ℕ) • theta + jP • theta := add_nsmul _ _ _
      _ = (ix : ℕ) • theta + a := by rw [hjPtheta]
  have hiyPoint : rotationPoint theta u iy =
      EuclideanGeometry.o.rotation (-a) x := by
    dsimp [rotationPoint, x]
    rw [hiytheta, EuclideanGeometry.o.rotation_rotation, add_comm]
  have hizPoint : rotationPoint theta u iz =
      EuclideanGeometry.o.rotation a x := by
    dsimp [rotationPoint, x]
    rw [hiztheta, EuclideanGeometry.o.rotation_rotation, add_comm]
  have hiyne : iy ≠ ix := by
    intro h
    have hfix : EuclideanGeometry.o.rotation (-a) x = x := by
      rw [← hiyPoint, h]
    have ha0 : a ≠ 0 := by
      intro ha
      have : jP • theta = 0 := by simpa [ha] using hjPtheta
      have hdvd : addOrderOf theta ∣ jP :=
        addOrderOf_dvd_iff_nsmul_eq_zero.mpr this
      rw [horder] at hdvd
      exact (Nat.not_dvd_of_pos_of_lt (by omega) hjPlt) hdvd
    have := (EuclideanGeometry.o.rotation_eq_self_iff_angle_eq_zero hx0 (-a)).mp hfix
    exact ha0 (neg_eq_zero.mp this)
  have hizne : iz ≠ ix := by
    intro h
    have hfix : EuclideanGeometry.o.rotation a x = x := by
      rw [← hizPoint, h]
    have ha0 : a ≠ 0 := by
      intro ha
      have : jP • theta = 0 := by simpa [ha] using hjPtheta
      have hdvd : addOrderOf theta ∣ jP :=
        addOrderOf_dvd_iff_nsmul_eq_zero.mpr this
      rw [horder] at hdvd
      exact (Nat.not_dvd_of_pos_of_lt (by omega) hjPlt) hdvd
    exact ha0 ((EuclideanGeometry.o.rotation_eq_self_iff_angle_eq_zero hx0 a).mp hfix)
  refine ⟨iy, iz, hiyne, hizne, ?_, ?_⟩
  · rw [hiyPoint, hizPoint]
    simpa [x] using rotation_pair_angularNeighbors p hp hx0
  · rw [hiyPoint, hizPoint]
    simpa [x] using angle_rotation_pair p hp hx0

/-- Translation of an affine orbit fixing `c` to the linear rotation orbit. -/
theorem rotationPoint_eq_orbitPoint_sub
    (rho : E ≃ᵃⁱ[ℝ] E) (x0 c : E) (hc : rho c = c) (theta : Real.Angle)
    (hlinear : rho.linearIsometryEquiv = EuclideanGeometry.o.rotation theta) (j : ℕ) :
    rotationPoint theta (x0 - c) j = orbitPoint rho x0 j - c := by
  induction j with
  | zero => simp [rotationPoint, orbitPoint]
  | succ j ih =>
      calc
        rotationPoint theta (x0 - c) (j + 1) =
            EuclideanGeometry.o.rotation theta
              (rotationPoint theta (x0 - c) j) := by
          dsimp [rotationPoint]
          rw [succ_nsmul, EuclideanGeometry.o.rotation_rotation, add_comm]
        _ = rho.linearIsometryEquiv (orbitPoint rho x0 j - c) := by
          rw [ih, hlinear]
        _ = rho (orbitPoint rho x0 j) - rho c := rho.map_vsub _ _
        _ = rho (orbitPoint rho x0 j) - c := by rw [hc]
        _ = orbitPoint rho x0 (j + 1) - c := by
          simp only [orbitPoint, Function.iterate_succ_apply']

/--
Affine version of `exists_angularNeighbors_of_addOrderOf`.  The witnesses are
actual members of the original `Fin p` orbit, while angular consecutiveness is
measured geometrically after translation to the fixed center.
-/
theorem exists_angularNeighbors_of_linear_rotation
    (p : ℕ) (hp : 3 ≤ p) (rho : E ≃ᵃⁱ[ℝ] E) (x0 c : E) (hc : rho c = c)
    (theta : Real.Angle)
    (hlinear : rho.linearIsometryEquiv = EuclideanGeometry.o.rotation theta)
    (horder : addOrderOf theta = p) (hx0c : x0 ≠ c) (ix : Fin p) :
    ∃ iy iz : Fin p,
      iy ≠ ix ∧ iz ≠ ix ∧
      AngularNeighbors p c (orbitPoint rho x0 iy) (orbitPoint rho x0 ix)
        (orbitPoint rho x0 iz) ∧
      ∠ (orbitPoint rho x0 iy) (orbitPoint rho x0 ix) (orbitPoint rho x0 iz) =
        regularInteriorAngle p := by
  have hu : x0 - c ≠ 0 := sub_ne_zero.mpr hx0c
  obtain ⟨iy, iz, hiy, hiz, hneigh, hangle⟩ :=
    exists_angularNeighbors_of_addOrderOf p hp theta horder hu ix
  have hv (j : Fin p) : rotationPoint theta (x0 - c) j =
      orbitPoint rho x0 j - c :=
    rotationPoint_eq_orbitPoint_sub rho x0 c hc theta hlinear j
  have hviy := hv iy
  have hvix := hv ix
  have hviz := hv iz
  rw [hviy, hvix, hviz] at hneigh hangle
  refine ⟨iy, iz, hiy, hiz, ?_, ?_⟩
  · simpa [AngularNeighbors, EuclideanGeometry.oangle, sub_ne_zero] using hneigh
  · simpa only [EuclideanGeometry.angle_sub_const] using hangle

/-- A closed injective rotation orbit of `p` points gives angle order exactly `p`. -/
theorem addOrderOf_eq_of_closed_injective_affine_rotation
    (p : ℕ) (hp : 3 ≤ p) (rho : E ≃ᵃⁱ[ℝ] E) (x0 c : E) (hc : rho c = c)
    (theta : Real.Angle)
    (hlinear : rho.linearIsometryEquiv = EuclideanGeometry.o.rotation theta)
    (hclosed : orbitPoint rho x0 p = x0)
    (hinj : Function.Injective (fun j : Fin p ↦ orbitPoint rho x0 (j : ℕ))) :
    addOrderOf theta = p := by
  have hp0 : 0 < p := by omega
  let i0 : Fin p := ⟨0, hp0⟩
  let i1 : Fin p := ⟨1, by omega⟩
  have hx0c : x0 ≠ c := by
    intro h
    have heq : orbitPoint rho x0 i0 = orbitPoint rho x0 i1 := by
      simp [i0, i1, orbitPoint, h, hc]
    have hi := hinj heq
    have hv := congrArg Fin.val hi
    dsimp [i0, i1] at hv
    omega
  have hu : x0 - c ≠ 0 := sub_ne_zero.mpr hx0c
  apply (addOrderOf_eq_iff hp0).mpr
  constructor
  · have hrot : rotationPoint theta (x0 - c) p = x0 - c := by
      rw [rotationPoint_eq_orbitPoint_sub rho x0 c hc theta hlinear p, hclosed]
    exact (EuclideanGeometry.o.rotation_eq_self_iff_angle_eq_zero hu (p • theta)).mp hrot
  · intro n hnp hn0 hnsmul
    have hrot : rotationPoint theta (x0 - c) n = x0 - c := by
      dsimp [rotationPoint]
      rw [hnsmul]
      simp
    have heqSub : orbitPoint rho x0 n - c = x0 - c := by
      rw [← rotationPoint_eq_orbitPoint_sub rho x0 c hc theta hlinear n]
      exact hrot
    have heq : orbitPoint rho x0 n = x0 := sub_left_injective heqSub
    let iN : Fin p := ⟨n, hnp⟩
    have hi : iN = i0 := by
      apply hinj
      simpa [iN, i0, orbitPoint] using heq
    have hv := congrArg Fin.val hi
    dsimp [iN, i0] at hv
    omega

/--
Complete result for an affine rotation: closure and distinctness alone recover
the order, then modular inversion chooses hull/angular neighbours rather than
the neighbours of the supplied (possibly star-shaped) indexing.
-/
theorem affine_rotation_orbit_internal_angle
    (p : ℕ) (hp : 3 ≤ p) (rho : E ≃ᵃⁱ[ℝ] E) (x0 c : E) (hc : rho c = c)
    (theta : Real.Angle)
    (hlinear : rho.linearIsometryEquiv = EuclideanGeometry.o.rotation theta)
    (hclosed : orbitPoint rho x0 p = x0)
    (hinj : Function.Injective (fun j : Fin p ↦ orbitPoint rho x0 (j : ℕ)))
    (ix : Fin p) :
    ∃ iy iz : Fin p,
      iy ≠ ix ∧ iz ≠ ix ∧
      AngularNeighbors p c (orbitPoint rho x0 iy) (orbitPoint rho x0 ix)
        (orbitPoint rho x0 iz) ∧
      ∠ (orbitPoint rho x0 iy) (orbitPoint rho x0 ix) (orbitPoint rho x0 iz) =
        regularInteriorAngle p := by
  have hp0 : 0 < p := by omega
  let i0 : Fin p := ⟨0, hp0⟩
  let i1 : Fin p := ⟨1, by omega⟩
  have hx0c : x0 ≠ c := by
    intro h
    have heq : orbitPoint rho x0 i0 = orbitPoint rho x0 i1 := by
      simp [i0, i1, orbitPoint, h, hc]
    have hi := hinj heq
    have hv := congrArg Fin.val hi
    dsimp [i0, i1] at hv
    omega
  have horder := addOrderOf_eq_of_closed_injective_affine_rotation
    p hp rho x0 c hc theta hlinear hclosed hinj
  exact exists_angularNeighbors_of_linear_rotation
    p hp rho x0 c hc theta hlinear horder hx0c ix

/-! The short two-dimensional classification step used to remove `hlinear`. -/

/-- A plane linear isometry with negative determinant is an involution. -/
theorem linearIsometry_involutive_of_det_neg
    (orient : Orientation ℝ E (Fin 2)) (f : E ≃ₗᵢ[ℝ] E)
    (hdet : LinearMap.det (f.toLinearEquiv : E →ₗ[ℝ] E) < 0) :
    ∀ x : E, f (f x) = x := by
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ E := by
    rw [Fintype.card_fin]
    exact (@Fact.out (Module.finrank ℝ E = 2) _).symm
  have hmap : Orientation.map (Fin 2) f.toLinearEquiv orient = -orient :=
    (orient.map_eq_neg_iff_det_neg f.toLinearEquiv hcard).2 hdet
  have hanti : ∀ z : E,
      f (orient.rightAngleRotation z) = -orient.rightAngleRotation (f z) := by
    intro z
    calc
      f (orient.rightAngleRotation z) =
          (Orientation.map (Fin 2) f.toLinearEquiv orient).rightAngleRotation (f z) := by
        symm
        simpa using orient.rightAngleRotation_map f (f z)
      _ = (-orient).rightAngleRotation (f z) := by rw [hmap]
      _ = -orient.rightAngleRotation (f z) :=
        orient.rightAngleRotation_neg_orientation (f z)
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · let B := orient.basisRightAngleRotation x hx
    let a : ℝ := B.repr (f x) 0
    let b : ℝ := B.repr (f x) 1
    have hdecomp : f x = a • x + b • orient.rightAngleRotation x := by
      rw [← B.sum_repr (f x)]
      simp [B, a, b, Fin.sum_univ_succ]
    have hab : a ^ 2 + b ^ 2 = 1 := by
      have horth : ⟪a • x, b • orient.rightAngleRotation x⟫ = 0 := by
        rw [real_inner_smul_left, real_inner_smul_right,
          orient.inner_rightAngleRotation_right]
        simp
      have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (a • x) (b • orient.rightAngleRotation x) horth
      rw [← hdecomp, f.norm_map] at hpyth
      simp only [norm_smul, orient.rightAngleRotation.norm_map, Real.norm_eq_abs] at hpyth
      have hnorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
      nlinarith [sq_abs a, sq_abs b]
    rw [hdecomp, map_add, map_smul, map_smul, hanti, hdecomp]
    simp only [map_add, map_smul, orient.rightAngleRotation_rightAngleRotation,
      smul_add, smul_neg, smul_smul]
    calc
      _ = (a ^ 2 + b ^ 2) • x := by module
      _ = x := by rw [hab, one_smul]

/-- The determinant of a linear isometric equivalence is nonzero. -/
theorem det_ne_zero_linearIsometryEquiv (f : E ≃ₗᵢ[ℝ] E) :
    LinearMap.det (f.toLinearEquiv : E →ₗ[ℝ] E) ≠ 0 := by
  intro hzero
  have hprod := f.toLinearEquiv.det_mul_det_symm
  rw [hzero, zero_mul] at hprod
  exact zero_ne_one hprod

/-- A plane isometry which is not an involution is a rotation. -/
theorem exists_rotation_of_sq_ne
    (orient : Orientation ℝ E (Fin 2)) (f : E ≃ₗᵢ[ℝ] E)
    (h : ∃ x : E, f (f x) ≠ x) :
    ∃ theta : Real.Angle, f = orient.rotation theta := by
  apply orient.exists_linearIsometryEquiv_eq_of_det_pos
  let d : ℝ := LinearMap.det (f.toLinearEquiv : E →ₗ[ℝ] E)
  have hdne : d ≠ 0 := det_ne_zero_linearIsometryEquiv f
  rcases lt_trichotomy d 0 with hneg | hzero | hpos
  · obtain ⟨x, hx⟩ := h
    exact (hx (linearIsometry_involutive_of_det_neg orient f hneg x)).elim
  · exact (hdne hzero).elim
  · simpa [d] using hpos

/--
The linear part of an affine isometry with a closed orbit of at least three
distinct points is a rotation about any fixed center.
-/
theorem exists_linear_rotation_of_closed_injective_orbit
    (p : ℕ) (hp : 3 ≤ p) (rho : E ≃ᵃⁱ[ℝ] E) (x0 c : E) (hc : rho c = c)
    (hinj : Function.Injective (fun j : Fin p ↦ orbitPoint rho x0 (j : ℕ))) :
    ∃ theta : Real.Angle,
      rho.linearIsometryEquiv = EuclideanGeometry.o.rotation theta := by
  have hp0 : 0 < p := by omega
  let i0 : Fin p := ⟨0, hp0⟩
  let i2 : Fin p := ⟨2, by omega⟩
  let u : E := x0 - c
  have hsquare : rho.linearIsometryEquiv (rho.linearIsometryEquiv u) ≠ u := by
    intro h
    have htwo : orbitPoint rho x0 2 - c = x0 - c := by
      calc
        orbitPoint rho x0 2 - c = rho (rho x0) - rho (rho c) := by
          simp [orbitPoint, hc]
        _ = rho.linearIsometryEquiv (rho x0 - rho c) := by
          exact (rho.map_vsub (rho x0) (rho c)).symm
        _ = rho.linearIsometryEquiv
            (rho.linearIsometryEquiv (x0 - c)) := by
          exact congrArg rho.linearIsometryEquiv (rho.map_vsub x0 c).symm
        _ = x0 - c := by simpa [u] using h
    have heq : orbitPoint rho x0 2 = x0 := sub_left_injective htwo
    have hi : i2 = i0 := by
      apply hinj
      simpa [i2, i0, orbitPoint] using heq
    have hv := congrArg Fin.val hi
    dsimp [i2, i0] at hv
    omega
  exact exists_rotation_of_sq_ne EuclideanGeometry.o rho.linearIsometryEquiv
    ⟨u, hsquare⟩

/--
Main theorem: every vertex of a closed orbit of `p ≥ 3` distinct points has
two geometrically consecutive orbit neighbours, and their internal (hull)
angle is `(p-2)π/p`.  No relation between those neighbours and the indices
`ix±1` is assumed or concluded.
-/
theorem affine_isometry_orbit_internal_angle
    (p : ℕ) (hp : 3 ≤ p) (rho : E ≃ᵃⁱ[ℝ] E) (x0 c : E)
    (hc : rho c = c) (hclosed : orbitPoint rho x0 p = x0)
    (hinj : Function.Injective (fun j : Fin p ↦ orbitPoint rho x0 (j : ℕ)))
    (ix : Fin p) :
    ∃ iy iz : Fin p,
      iy ≠ ix ∧ iz ≠ ix ∧ iy ≠ iz ∧
      AngularNeighbors p c (orbitPoint rho x0 iy) (orbitPoint rho x0 ix)
        (orbitPoint rho x0 iz) ∧
      ∠ (orbitPoint rho x0 iy) (orbitPoint rho x0 ix) (orbitPoint rho x0 iz) =
        ((p : ℝ) - 2) * π / p := by
  obtain ⟨theta, hlinear⟩ :=
    exists_linear_rotation_of_closed_injective_orbit p hp rho x0 c hc hinj
  obtain ⟨iy, iz, hiy, hiz, hneigh, hangle⟩ :=
    affine_rotation_orbit_internal_angle
      p hp rho x0 c hc theta hlinear hclosed hinj ix
  have hyz : iy ≠ iz := by
    intro h
    subst iz
    have hsign := hneigh.2.2.2.2.2
    simp at hsign
  exact ⟨iy, iz, hiy, hiz, hyz, hneigh, by
    simpa [regularInteriorAngle] using hangle⟩

/-- The finite set underlying the first `p` points of an affine orbit. -/
def orbitVertexSet (p : ℕ) (rho : E ≃ᵃⁱ[ℝ] E) (x0 : E) : Set E :=
  Set.range (fun j : Fin p ↦ orbitPoint rho x0 (j : ℕ))

/-- Points lying on one Euclidean sphere are precisely the extreme points of their hull. -/
theorem extremePoints_convexHull_eq_of_subset_sphere
    (center : E) (radius : ℝ) (vertices : Set E)
    (hvertices : vertices ⊆ Metric.sphere center radius) :
    (convexHull ℝ vertices).extremePoints ℝ = vertices := by
  letI : Nontrivial E :=
    Module.nontrivial_of_finrank_eq_succ
      (show Module.finrank ℝ E = 1 + 1 from Fact.out)
  refine le_antisymm extremePoints_convexHull_subset ?_
  have hball : convexHull ℝ vertices ⊆ Metric.closedBall center radius :=
    convexHull_min (hvertices.trans sphere_subset_closedBall)
      (convex_closedBall center radius)
  intro v hv
  have hsphere : v ∈ (Metric.closedBall center radius).extremePoints ℝ := by
    rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
    exact hvertices hv
  exact inter_extremePoints_subset_extremePoints_of_subset hball
    ⟨subset_convexHull ℝ vertices hv, hsphere⟩

/-- The orbit set is exactly the vertex set of its convex hull. -/
theorem orbitVertexSet_eq_extremePoints
    (p : ℕ) (rho : E ≃ᵃⁱ[ℝ] E) (x0 c : E) (hc : rho c = c) :
    (convexHull ℝ (orbitVertexSet p rho x0)).extremePoints ℝ =
      orbitVertexSet p rho x0 := by
  apply extremePoints_convexHull_eq_of_subset_sphere c (dist x0 c)
  rintro v ⟨j, rfl⟩
  rw [Metric.mem_sphere]
  exact EuclideanGeometry.mem_sphere.mp (orbitPoint_mem_sphere rho x0 c hc j)

/--
Hull-aware form of angular consecutiveness: the three points belong to the
orbit, the orbit is the extreme-point set of its convex hull, and `y,z` are
the two elementary angular neighbours of `x`.
-/
def HullAngularNeighbors (p : ℕ) (rho : E ≃ᵃⁱ[ℝ] E) (x0 c y x z : E) : Prop :=
  AngularNeighbors p c y x z ∧
    y ∈ orbitVertexSet p rho x0 ∧
    x ∈ orbitVertexSet p rho x0 ∧
    z ∈ orbitVertexSet p rho x0 ∧
    (convexHull ℝ (orbitVertexSet p rho x0)).extremePoints ℝ =
      orbitVertexSet p rho x0

/--
Hull-explicit final form.  The returned `y,z` are not index neighbours: they
are vertices of the convex hull and are consecutive in the geometric angular
order about `c`.  Therefore diagonal steps in a star parametrisation are
discarded by construction.
-/
theorem affine_isometry_orbit_hull_internal_angle
    (p : ℕ) (hp : 3 ≤ p) (rho : E ≃ᵃⁱ[ℝ] E) (x0 c : E)
    (hc : rho c = c) (hclosed : orbitPoint rho x0 p = x0)
    (hinj : Function.Injective (fun j : Fin p ↦ orbitPoint rho x0 (j : ℕ)))
    (ix : Fin p) :
    ∃ iy iz : Fin p,
      iy ≠ ix ∧ iz ≠ ix ∧ iy ≠ iz ∧
      HullAngularNeighbors p rho x0 c
        (orbitPoint rho x0 iy) (orbitPoint rho x0 ix) (orbitPoint rho x0 iz) ∧
      ∠ (orbitPoint rho x0 iy) (orbitPoint rho x0 ix) (orbitPoint rho x0 iz) =
        ((p : ℝ) - 2) * π / p := by
  obtain ⟨iy, iz, hiy, hiz, hyz, hneigh, hangle⟩ :=
    affine_isometry_orbit_internal_angle p hp rho x0 c hc hclosed hinj ix
  have hyMem : orbitPoint rho x0 iy ∈ orbitVertexSet p rho x0 := ⟨iy, rfl⟩
  have hxMem : orbitPoint rho x0 ix ∈ orbitVertexSet p rho x0 := ⟨ix, rfl⟩
  have hzMem : orbitPoint rho x0 iz ∈ orbitVertexSet p rho x0 := ⟨iz, rfl⟩
  have hextreme := orbitVertexSet_eq_extremePoints p rho x0 c hc
  exact ⟨iy, iz, hiy, hiz, hyz,
    ⟨hneigh, hyMem, hxMem, hzMem, hextreme⟩, hangle⟩

end AngoloInterno
