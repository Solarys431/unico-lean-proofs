import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.Carta
import UnicoProofs.Platonici.R2Base
import UnicoProofs.Platonici.RotazionePoligono
import UnicoProofs.Platonici.SpigoloVicino
import UnicoProofs.Platonici.AngoloInterno
import UnicoProofs.Platonici.OrbitaTraslata

open Set Real
open scoped RealInnerProductSpace
open PlatoniciA7 PlatoniciA8 PlatoniciA10 PlatoniciA14 PlatoniciL1

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- The common supporting half-plane, with the common side as its exact
intersection with the supporting line.  This is the form supplied by an
exposing functional at a polygonal side. -/
def SemipianoComune (A B : Set (E 3)) (x y : E 3) : Prop :=
  ∃ h : E 3 →L[ℝ] ℝ,
    h x = h y ∧
    (∀ z ∈ A, h x ≤ h z) ∧
    (∀ z ∈ B, h x ≤ h z) ∧
    {z ∈ A | h z = h x} = segment ℝ x y ∧
    {z ∈ B | h z = h x} = segment ℝ x y

/-- Equal nondegenerate segments have the same unordered pair of endpoints. -/
theorem endpoints_of_segment_eq_of_dist_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {x y u v : V} (hseg : segment ℝ x y = segment ℝ u v)
    (hne : x ≠ y) (hd : dist x y = dist u v) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  have hxypos : 0 < dist x y := dist_pos.mpr hne
  have huvpos : 0 < dist u v := by rw [← hd]; exact hxypos
  have hxmem : x ∈ segment ℝ u v := by
    rw [← hseg]
    exact left_mem_segment ℝ x y
  have hymem : y ∈ segment ℝ u v := by
    rw [← hseg]
    exact right_mem_segment ℝ x y
  rw [segment_eq_image_lineMap] at hxmem hymem
  obtain ⟨a, ha, hxa⟩ := hxmem
  obtain ⟨b, hb, hyb⟩ := hymem
  have habs : |a - b| = 1 := by
    have hdist := dist_lineMap_lineMap u v a b
    rw [hxa, hyb, hd, Real.dist_eq] at hdist
    have huvne : dist u v ≠ 0 := ne_of_gt huvpos
    apply mul_right_cancel₀ huvne
    simpa [abs_sub_comm] using hdist.symm
  have hab : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
    rcases ha with ⟨ha0, ha1⟩
    rcases hb with ⟨hb0, hb1⟩
    rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at habs
    rcases habs with habs | habs
    · right
      constructor <;> linarith
    · left
      constructor <;> linarith
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    have hx : x = u := by simpa [AffineMap.lineMap_apply] using hxa.symm
    have hy : y = v := by simpa [AffineMap.lineMap_apply] using hyb.symm
    exact ⟨hx, hy⟩
  · right
    have hx : x = v := by simpa [AffineMap.lineMap_apply] using hxa.symm
    have hy : y = u := by simpa [AffineMap.lineMap_apply] using hyb.symm
    exact ⟨hx, hy⟩

/-- A closed orbit remains closed when the generator is replaced by its
inverse. -/
theorem inverse_cycle_closed {alpha : Type*} {f g : alpha → alpha}
    (hgf : Function.LeftInverse g f) (hfg : Function.LeftInverse f g)
    {x : alpha} {p : ℕ} (hcl : f^[p] x = x) : g^[p] x = x := by
  apply (hgf.iterate p).injective
  rw [hcl]
  exact (hfg.iterate p) x

/-- In a closed cycle, `k` inverse steps equal `p-k` forward steps. -/
theorem inverse_iterate_eq_sub {alpha : Type*} {f g : alpha → alpha}
    (hgf : Function.LeftInverse g f) (hfg : Function.LeftInverse f g)
    {x : alpha} {p k : ℕ} (hcl : f^[p] x = x) (hk : k ≤ p) :
    g^[k] x = f^[p - k] x := by
  apply (hgf.iterate k).injective
  have hleft : f^[k] (g^[k] x) = x := (hfg.iterate k) x
  have hright : f^[k] (f^[p - k] x) = x := by
    calc
      f^[k] (f^[p - k] x) = f^[k + (p - k)] x :=
        (Function.iterate_add_apply f k (p - k) x).symm
      _ = f^[p] x := by congr 1; omega
      _ = x := hcl
  exact hleft.trans hright.symm

/-- Reversing a finite closed cycle does not change its underlying set. -/
theorem inverse_cycle_range {alpha : Type*} {f g : alpha → alpha}
    (hgf : Function.LeftInverse g f) (hfg : Function.LeftInverse f g)
    {x : alpha} {p : ℕ} (hp : 0 < p) (hcl : f^[p] x = x) :
    Set.range (fun i : Fin p => g^[(i : ℕ)] x) =
      Set.range (fun i : Fin p => f^[(i : ℕ)] x) := by
  have hgcl : g^[p] x = x := inverse_cycle_closed hgf hfg hcl
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    let j : Fin p := ⟨(p - (i : ℕ)) % p, Nat.mod_lt _ hp⟩
    refine ⟨j, ?_⟩
    have hsub := inverse_iterate_eq_sub hgf hfg hcl (Nat.le_of_lt i.isLt)
    have hmod := iterate_mod f x p hcl (p - (i : ℕ))
    exact (hsub.trans hmod).symm
  · rintro ⟨i, rfl⟩
    let j : Fin p := ⟨(p - (i : ℕ)) % p, Nat.mod_lt _ hp⟩
    refine ⟨j, ?_⟩
    have hsub := inverse_iterate_eq_sub hfg hgf hgcl (Nat.le_of_lt i.isLt)
    have hmod := iterate_mod g x p hgcl (p - (i : ℕ))
    exact (hsub.trans hmod).symm

/-- Distinctness of a closed cycle is preserved when its direction is
reversed. -/
theorem inverse_cycle_injective {alpha : Type*} {f g : alpha → alpha}
    (hgf : Function.LeftInverse g f) (hfg : Function.LeftInverse f g)
    {x : alpha} {p : ℕ} (hp : 0 < p) (hcl : f^[p] x = x)
    (hinj : Function.Injective (fun i : Fin p => f^[(i : ℕ)] x)) :
    Function.Injective (fun i : Fin p => g^[(i : ℕ)] x) := by
  intro i j hij
  have hiSub := inverse_iterate_eq_sub hgf hfg hcl (Nat.le_of_lt i.isLt)
  have hjSub := inverse_iterate_eq_sub hgf hfg hcl (Nat.le_of_lt j.isLt)
  have heq : f^[p - (i : ℕ)] x = f^[p - (j : ℕ)] x :=
    hiSub.symm.trans (hij.trans hjSub)
  by_cases hi0 : (i : ℕ) = 0
  · have hj0 : (j : ℕ) = 0 := by
      by_contra hj0
      have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hj0
      have hjsub_lt : p - (j : ℕ) < p := by omega
      let iZero : Fin p := ⟨0, hp⟩
      let jRev : Fin p := ⟨p - (j : ℕ), hjsub_lt⟩
      have horbit : (fun q : Fin p => f^[(q : ℕ)] x) iZero =
          (fun q : Fin p => f^[(q : ℕ)] x) jRev := by
        simpa [iZero, jRev, hi0, hcl] using heq
      have hindex := hinj horbit
      have hval : 0 = p - (j : ℕ) := congrArg Fin.val hindex
      omega
    exact Fin.ext (hi0.trans hj0.symm)
  · by_cases hj0 : (j : ℕ) = 0
    · have hipos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi0
      have hisub_lt : p - (i : ℕ) < p := by omega
      let iRev : Fin p := ⟨p - (i : ℕ), hisub_lt⟩
      let jZero : Fin p := ⟨0, hp⟩
      have horbit : (fun q : Fin p => f^[(q : ℕ)] x) iRev =
          (fun q : Fin p => f^[(q : ℕ)] x) jZero := by
        simpa [iRev, jZero, hj0, hcl] using heq
      have hindex := hinj horbit
      have hval : p - (i : ℕ) = 0 := congrArg Fin.val hindex
      omega
    · have hipos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi0
      have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hj0
      have hisub_lt : p - (i : ℕ) < p := by omega
      have hjsub_lt : p - (j : ℕ) < p := by omega
      let iRev : Fin p := ⟨p - (i : ℕ), hisub_lt⟩
      let jRev : Fin p := ⟨p - (j : ℕ), hjsub_lt⟩
      have horbit : (fun q : Fin p => f^[(q : ℕ)] x) iRev =
          (fun q : Fin p => f^[(q : ℕ)] x) jRev := by
        simpa [iRev, jRev] using heq
      have hindex := hinj horbit
      have hval : p - (i : ℕ) = p - (j : ℕ) := congrArg Fin.val hindex
      apply Fin.ext
      omega

/-- Reversing the cycle and starting at the next forward vertex gives the
same finite orbit, now with the first side traversed backwards. -/
theorem reverse_cycle_at_next {alpha : Type*} {f g : alpha → alpha}
    (hgf : Function.LeftInverse g f) (hfg : Function.LeftInverse f g)
    {x : alpha} {p : ℕ} (hp : 0 < p) (hcl : f^[p] x = x)
    (hinj : Function.Injective (fun i : Fin p => f^[(i : ℕ)] x)) :
    g^[p] (f x) = f x ∧
      Function.Injective (fun i : Fin p => g^[(i : ℕ)] (f x)) ∧
      Set.range (fun i : Fin p => g^[(i : ℕ)] (f x)) =
        Set.range (fun i : Fin p => f^[(i : ℕ)] x) := by
  have hgcl : g^[p] x = x := inverse_cycle_closed hgf hfg hcl
  have hginj : Function.Injective (fun i : Fin p => g^[(i : ℕ)] x) :=
    inverse_cycle_injective hgf hfg hp hcl hinj
  have hbase : g^[p - 1] x = f x := by
    have hsub := inverse_iterate_eq_sub hgf hfg hcl
      (k := p - 1) (by omega)
    have hnum : p - (p - 1) = 1 := by omega
    simpa [hnum] using hsub
  have hshiftCl := orbita_traslata_chiusa g x p hgcl (p - 1)
  have hshiftInj := orbita_traslata_iniettiva g x p hp hgcl hginj (p - 1)
  have hshiftRange := orbita_traslata_range g x p hp hgcl (p - 1)
  rw [hbase] at hshiftCl hshiftInj hshiftRange
  exact ⟨hshiftCl, hshiftInj,
    hshiftRange.trans (inverse_cycle_range hgf hfg hp hcl)⟩

/-- If an equivalence preserves a set, its inverse preserves it as well. -/
theorem symm_image_eq_of_image_eq {alpha : Type*} (e : alpha ≃ alpha)
    {S : Set alpha} (hS : e '' S = S) : e.symm '' S = S := by
  apply Set.Subset.antisymm
  · rintro z ⟨w, hw, rfl⟩
    rw [← hS] at hw
    rcases hw with ⟨u, hu, rfl⟩
    simpa using hu
  · intro z hz
    refine ⟨e z, ?_, e.symm_apply_apply z⟩
    rw [← hS]
    exact ⟨z, hz, rfl⟩

/-- On a circle through the origin, a positive multiple of a second point of
the circle can lie on the circle only at that second point. -/
theorem positive_smul_eq_of_dist_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {c n y : V} {t : ℝ} (ht : 0 < t) (hy : y = t • n) (hy0 : y ≠ 0)
    (hyn : dist y c = dist 0 c) (hn : dist n c = dist 0 c) : y = n := by
  have hn0 : n ≠ 0 := by
    intro hnz
    apply hy0
    rw [hy, hnz, smul_zero]
  have hnn : 0 < ‖n‖ := norm_pos_iff.mpr hn0
  have e1 := congrArg (fun r : ℝ => r ^ 2) hyn
  have e2 := congrArg (fun r : ℝ => r ^ 2) hn
  rw [hy, dist_eq_norm, dist_eq_norm, norm_sub_sq_real,
    norm_smul, Real.norm_of_nonneg ht.le, real_inner_smul_left,
    zero_sub, norm_neg] at e1
  rw [dist_eq_norm, dist_eq_norm, norm_sub_sq_real,
    zero_sub, norm_neg] at e2
  have hinner : 2 * ⟪n, c⟫ = ‖n‖ ^ 2 := by nlinarith [e2]
  have hprod : t * (t - 1) * ‖n‖ ^ 2 = 0 := by
    calc
      t * (t - 1) * ‖n‖ ^ 2 =
          (t * ‖n‖) ^ 2 - t * ‖n‖ ^ 2 := by ring
      _ = (t * ‖n‖) ^ 2 - t * (2 * ⟪n, c⟫) := by rw [hinner]
      _ = (t * ‖n‖) ^ 2 - 2 * (t * ⟪n, c⟫) := by ring
      _ = 0 := by nlinarith [e1]
  have ht1 : t = 1 := by
    rcases mul_eq_zero.mp hprod with h | h
    · rcases mul_eq_zero.mp h with ht0 | ht1
      · exact absurd ht0 (ne_of_gt ht)
      · linarith
    · exact absurd (sq_eq_zero_iff.mp h) (norm_ne_zero_iff.mpr hn0)
  rw [hy, ht1, one_smul]

/-- In an oriented Euclidean plane, two intersections of the same two
circles are exchanged by reflection in the line of their centers.  A linear
functional vanishing on that line distinguishes the two open half-planes. -/
theorem eq_of_two_dist_eq_of_functional_pos
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)]
    (o : Orientation ℝ V (Fin 2)) (L : V →L[ℝ] ℝ)
    {d z w : V} (hd0 : d ≠ 0) (hLd : L d = 0)
    (hLz : 0 < L z) (hLw : 0 < L w)
    (hnorm : ‖z‖ = ‖w‖) (hdist : dist d z = dist d w) : z = w := by
  have enorm := congrArg (fun r : ℝ => r ^ 2) hnorm
  have edist := congrArg (fun r : ℝ => r ^ 2) hdist
  rw [dist_eq_norm, dist_eq_norm, norm_sub_sq_real, norm_sub_sq_real] at edist
  have horth1 : ⟪d, z - w⟫ = 0 := by
    rw [inner_sub_right]
    nlinarith [edist, enorm]
  by_contra hzw
  have hq0 : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have horth2 : ⟪z - w, z + w⟫ = 0 := by
    rw [inner_sub_left, inner_add_right, inner_add_right,
      real_inner_comm w z, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq]
    nlinarith [enorm]
  obtain ⟨r, hr⟩ :=
    ((o.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two).mp horth1).resolve_left hd0
  obtain ⟨s, hs⟩ :=
    ((o.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two).mp horth2).resolve_left hq0
  have hsum : L (z + w) = 0 := by
    rw [← hs, ← hr, map_smul, map_smul]
    rw [o.rotation_pi_div_two]
    simp [hLd]
  rw [map_add] at hsum
  linarith

/-- Every point of a finite isometric orbit is extreme in the convex hull of
that orbit: all orbit points lie on one Euclidean sphere. -/
theorem orbit_point_mem_extremePoints
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nontrivial V]
    {p : ℕ} (rho : V ≃ᵃⁱ[ℝ] V) (x c : V) (hc : rho c = c) (j : Fin p) :
    (rho : V → V)^[(j : ℕ)] x ∈
      (convexHull ℝ (Set.range fun i : Fin p =>
        (rho : V → V)^[(i : ℕ)] x)).extremePoints ℝ := by
  let S : Set V := Set.range fun i : Fin p => (rho : V → V)^[(i : ℕ)] x
  have hS : S ⊆ Metric.sphere c (dist x c) := by
    rintro z ⟨i, rfl⟩
    exact orbita_cocircolare rho x c hc (i : ℕ)
  have hball : convexHull ℝ S ⊆ Metric.closedBall c (dist x c) :=
    convexHull_min (hS.trans Metric.sphere_subset_closedBall)
      (convex_closedBall c (dist x c))
  have hjS : (rho : V → V)^[(j : ℕ)] x ∈ S := ⟨j, rfl⟩
  have hjext : (rho : V → V)^[(j : ℕ)] x ∈
      (Metric.closedBall c (dist x c)).extremePoints ℝ := by
    rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
    exact hS hjS
  exact inter_extremePoints_subset_extremePoints_of_subset hball
    ⟨subset_convexHull ℝ S hjS, hjext⟩

/-- A closed finite affine-isometry orbit has a fixed centroid. -/
theorem exists_fixed_point_of_closed_orbit
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {p : ℕ} (rho : V ≃ᵃⁱ[ℝ] V) (x : V)
    (hp0 : 0 < p) (hcl : (rho : V → V)^[p] x = x) :
    ∃ c : V, rho c = c := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  exact ⟨Finset.univ.centroid ℝ
      (fun i : Fin (m + 1) => (rho : V → V)^[(i : ℕ)] x),
    orbita_centroid_fisso rho x hcl⟩

/-- The third point of a closed injective orbit of length at least three is
not on the segment formed by its first two points. -/
theorem orbit_two_not_mem_first_segment
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nontrivial V]
    {p : ℕ} (hp : 3 ≤ p) (rho : V ≃ᵃⁱ[ℝ] V) (x c : V) (hc : rho c = c)
    (hinj : Function.Injective (fun i : Fin p =>
      (rho : V → V)^[(i : ℕ)] x)) :
    (rho : V → V)^[2] x ∉ segment ℝ x (rho x) := by
  intro hseg
  let i0 : Fin p := ⟨0, by omega⟩
  let i1 : Fin p := ⟨1, by omega⟩
  let i2 : Fin p := ⟨2, by omega⟩
  have hext := orbit_point_mem_extremePoints rho x c hc i2
  have hxHull : x ∈ convexHull ℝ (Set.range fun i : Fin p =>
      (rho : V → V)^[(i : ℕ)] x) := by
    exact subset_convexHull ℝ _ ⟨i0, rfl⟩
  have hrhoHull : rho x ∈ convexHull ℝ (Set.range fun i : Fin p =>
      (rho : V → V)^[(i : ℕ)] x) := by
    exact subset_convexHull ℝ _ ⟨i1, by simp [i1]⟩
  have hend := (mem_extremePoints_iff_forall_segment.mp hext).2
    x hxHull (rho x) hrhoHull hseg
  rcases hend with h20 | h21
  · have hi : i2 = i0 := by
      apply hinj
      simpa [i2, i0] using h20.symm
    have := congrArg Fin.val hi
    simp [i2, i0] at this
  · have hi : i2 = i1 := by
      apply hinj
      simpa [i2, i1] using h21.symm
    have := congrArg Fin.val hi
    simp [i2, i1] at this

/-- A rotation angle is determined by its value on one nonzero vector. -/
theorem rotation_angle_injective
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)]
    (o : Orientation ℝ V (Fin 2)) {d : V} (hd : d ≠ 0) :
    Function.Injective (fun theta : Real.Angle => o.rotation theta d) := by
  intro a b hab
  have h := congrArg (o.oangle d) hab
  simpa only [o.oangle_rotation_self_right hd] using h

/-- If the first orbit chord is the exact exposed face selected by `h`, then
the first three orbit points make the regular internal angle. -/
theorem supported_orbit_first_angle
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nontrivial V]
    {F : Set V} {p : ℕ} (rho : V ≃ᵃⁱ[ℝ] V) (x : V)
    (hgen : F = convexHull ℝ (Set.range fun i : Fin p =>
      (rho : V → V)^[(i : ℕ)] x))
    (hfix : (rho : V → V) '' F = F)
    (hinj : Function.Injective (fun i : Fin p =>
      (rho : V → V)^[(i : ℕ)] x))
    (hcl : (rho : V → V)^[p] x = x)
    (hp : 3 ≤ p) (hdim : Module.finrank ℝ (vectorSpan ℝ F) = 2)
    (h : V →L[ℝ] ℝ) (hxy : h x = h (rho x))
    (hlower : ∀ z ∈ F, h x ≤ h z)
    (hface : {z ∈ F | h z = h x} = segment ℝ x (rho x)) :
    EuclideanGeometry.angle x (rho x) ((rho : V → V)^[2] x) =
      AngoloInterno.regularInteriorAngle p := by
  classical
  let i0 : Fin p := ⟨0, by omega⟩
  let i1 : Fin p := ⟨1, by omega⟩
  let i2 : Fin p := ⟨2, by omega⟩
  have hxF : x ∈ F := by
    rw [hgen]
    exact subset_convexHull ℝ _ ⟨i0, by simp [i0]⟩
  have horbitF : ∀ i : Fin p, (rho : V → V)^[(i : ℕ)] x ∈ F := by
    intro i
    rw [hgen]
    exact subset_convexHull ℝ _ ⟨i, rfl⟩
  have hmemF : ∀ k : ℕ, (rho : V → V)^[k] x ∈ F := by
    intro k
    induction k with
    | zero => exact hxF
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact mem_of_invariante rho hfix ih
  let W : Submodule ℝ V := vectorSpan ℝ F
  have hW2 : Module.finrank ℝ W = 2 := hdim
  letI : FiniteDimensional ℝ W := by
    have hw : Module.finrank ℝ W = 1 + 1 := by omega
    exact Module.finite_of_finrank_eq_succ hw
  letI : Fact (Module.finrank ℝ W = 2) := ⟨hW2⟩
  let o : Orientation ℝ W (Fin 2) := orientazione2 W hW2
  letI : Module.Oriented ℝ W (Fin 2) := ⟨o⟩
  let chi : W ≃ᵃⁱ[ℝ] W := carta rho F hfix x hxF
  have hchicl : (chi : W → W)^[p] 0 = 0 :=
    carta_orbita_chiusa rho F hfix x hxF p hcl
  have hchiinj : Function.Injective (fun i : Fin p =>
      (chi : W → W)^[(i : ℕ)] (0 : W)) :=
    carta_orbita_iniettiva rho F hfix x hxF p hinj
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  let cc : W := Finset.univ.centroid ℝ
    (fun i : Fin (m + 1) => (chi : W → W)^[(i : ℕ)] 0)
  have hcc : chi cc = cc := by
    subst p
    exact orbita_centroid_fisso chi 0 hchicl
  have hcenter : rho (x + (cc : V)) = x + (cc : V) := by
    rw [← carta_apply rho F hfix x hxF cc, hcc]
  have htwo_not : (rho : V → V)^[2] x ∉ segment ℝ x (rho x) :=
    orbit_two_not_mem_first_segment hp rho x (x + (cc : V)) hcenter hinj
  have htwo_strict : h x < h ((rho : V → V)^[2] x) := by
    have hle := hlower _ (hmemF 2)
    exact lt_of_le_of_ne hle (fun heq => htwo_not (by
      rw [← hface]
      exact ⟨hmemF 2, heq.symm⟩))
  let L : W →L[ℝ] ℝ := (-h).comp W.subtypeL
  have hLapply : ∀ q : W, L q = -h (q : V) := fun q => rfl
  have hchart : ∀ k : ℕ,
      ((chi : W → W)^[k] (0 : W) : V) = (rho : V → V)^[k] x - x := by
    intro k
    have hc := carta_iterate rho F hfix x hxF k
    exact eq_sub_of_add_eq' hc
  have hL0 : ∀ i : Fin p, L ((chi : W → W)^[(i : ℕ)] 0) ≤ L 0 := by
    intro i
    rw [hLapply, hLapply, hchart, map_sub]
    simp only [map_zero, Submodule.coe_zero, neg_zero]
    have hi := hlower _ (horbitF i)
    linarith
  have hLnc : ∃ i : Fin p, L ((chi : W → W)^[(i : ℕ)] 0) < L 0 := by
    refine ⟨i2, ?_⟩
    rw [hLapply, hLapply, hchart, map_sub]
    simp only [map_zero, Submodule.coe_zero, neg_zero]
    simpa [i2] using (neg_lt_neg htwo_strict)
  let y : W := chi 0
  have hyhull : y ∈ convexHull ℝ (Set.range fun i : Fin p =>
      (chi : W → W)^[(i : ℕ)] (0 : W)) := by
    exact subset_convexHull ℝ _ ⟨i1, by simp [y, i1]⟩
  have hy0 : y ≠ 0 := by
    intro hyz
    have hi : i1 = i0 := by
      apply hchiinj
      simpa [y, i1, i0] using hyz
    have := congrArg Fin.val hi
    simp [i1, i0] at this
  have hLy : L y = L 0 := by
    rw [hLapply, hLapply, show (y : V) = rho x - x by
      simpa [y] using hchart 1, map_sub, hxy]
    simp only [map_zero, Submodule.coe_zero, neg_zero]
    ring
  obtain ⟨n, hnform, t, ht, hytn⟩ :=
    spigolo_verso_vicino o chi cc hcc hp hchicl hchiinj L hL0 hLnc
      hyhull hy0 hLy
  have hccoc := orbita_cocircolare chi 0 cc hcc
  have hyn_circle : dist y cc = dist 0 cc := by
    simpa [y] using hccoc 1
  have hn_circle : dist n cc = dist 0 cc := by
    rcases hnform with hn | hn
    · rw [hn]
      simpa [dist_eq_norm] using
        (o.rotation (((2 : ℝ) * π / p : ℝ) : Real.Angle)).norm_map ((0 : W) - cc)
    · rw [hn]
      simpa [dist_eq_norm] using
        (o.rotation ((-((2 : ℝ) * π / p) : ℝ) : Real.Angle)).norm_map ((0 : W) - cc)
  have hyn : y = n :=
    positive_smul_eq_of_dist_eq ht hytn hy0 hyn_circle hn_circle
  obtain ⟨theta, horder, horbit⟩ :=
    rotazione_del_poligono o chi cc hcc hp hchicl hchiinj
  let a : Real.Angle := (((2 : ℝ) * π / p : ℝ) : Real.Angle)
  let d : W := (0 : W) - cc
  have hd0 : d ≠ 0 := by
    intro hd
    have hcc0 : cc = 0 := by
      have := congrArg (fun q : W => q + cc) hd
      simpa [d] using this.symm
    have hyzero : y = 0 := by
      have h1 := hccoc 1
      rw [hcc0] at h1
      exact dist_eq_zero.mp (by simpa [y] using h1)
    exact hy0 hyzero
  have htheta : theta = a ∨ theta = -a := by
    have hrot1 := horbit 1
    have hleft : (chi : W → W)^[1] 0 - cc = y - cc := by simp [y]
    rw [hleft] at hrot1
    rcases hnform with hn | hn
    · left
      apply rotation_angle_injective o hd0
      have hyform : y - cc = o.rotation a d := by
        rw [hyn, hn]
        simp [a, d]
      rw [Function.iterate_one] at hrot1
      exact hrot1.symm.trans hyform
    · right
      apply rotation_angle_injective o hd0
      have hyform : y - cc = o.rotation (-a) d := by
        rw [hyn, hn]
        simp [a, d]
      rw [Function.iterate_one] at hrot1
      exact hrot1.symm.trans hyform
  let z : W := (chi : W → W)^[2] 0
  let u : W := y - cc
  have hu0 : u ≠ 0 := by
    have hu_norm : dist y cc = dist 0 cc := hyn_circle
    intro huz
    have hycc : y = cc := sub_eq_zero.mp huz
    rw [hycc] at hu_norm
    have hzero : dist (0 : W) cc = 0 := hu_norm.symm.trans (dist_self cc)
    have h0cc : (0 : W) = cc := dist_eq_zero.mp hzero
    exact hy0 (hycc.trans h0cc.symm)
  have htriple : EuclideanGeometry.angle (0 : W) y z =
      AngoloInterno.regularInteriorAngle p := by
    have hzrot : z - cc = o.rotation theta u := by
      have h2 := horbit 2
      have h1 := horbit 1
      rw [show (2 : ℕ) = Nat.succ 1 by omega,
        Function.iterate_succ_apply', Function.iterate_one] at h2
      rw [Function.iterate_one] at h1
      change y - cc = o.rotation theta d at h1
      change z - cc = o.rotation theta (y - cc)
      rw [h1]
      exact h2
    have hprev : (0 : W) - cc = o.rotation (-theta) u := by
      have h1 := horbit 1
      change u = o.rotation theta d at h1
      rw [h1, o.rotation_rotation]
      simp [d]
    rw [← EuclideanGeometry.angle_sub_const (0 : W) y z cc,
      hprev, hzrot]
    rcases htheta with rfl | rfl
    · have hmodel := AngoloInterno.angle_rotation_pair p hp hu0
      change EuclideanGeometry.angle (o.rotation (-a) u) u (o.rotation a u) =
        AngoloInterno.regularInteriorAngle p at hmodel
      simpa [u] using hmodel
    · rw [EuclideanGeometry.angle_comm]
      have hmodel := AngoloInterno.angle_rotation_pair p hp hu0
      change EuclideanGeometry.angle (o.rotation (-a) u) u (o.rotation a u) =
        AngoloInterno.regularInteriorAngle p at hmodel
      simpa [u] using hmodel
  have hamb := angolo_carta (W := W) x (y : W) (0 : W) z
  have hxrho : x + (y : V) = rho x := by
    simpa [y] using carta_iterate rho F hfix x hxF 1
  have hxz : x + (z : V) = (rho : V → V)^[2] x := by
    simpa [z] using carta_iterate rho F hfix x hxF 2
  rw [hxrho, hxz] at hamb
  simpa using hamb.trans htriple

/-- Two plane affine isometries with closed injective orbits of length at
least three coincide once their first three orbit points coincide. -/
theorem affine_isometry_eq_of_first_three
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)]
    {p : ℕ} (hp : 3 ≤ p) (f g : V ≃ᵃⁱ[ℝ] V)
    (hfcl : (f : V → V)^[p] 0 = 0)
    (hgcl : (g : V → V)^[p] 0 = 0)
    (hfinj : Function.Injective (fun i : Fin p =>
      (f : V → V)^[(i : ℕ)] (0 : V)))
    (hginj : Function.Injective (fun i : Fin p =>
      (g : V → V)^[(i : ℕ)] (0 : V)))
    (hfirst : f 0 = g 0) (hsecond : f (f 0) = g (g 0)) : f = g := by
  classical
  letI : FiniteDimensional ℝ V := by
    have hdim : Module.finrank ℝ V = 1 + 1 := by
      rw [show Module.finrank ℝ V = 2 from Fact.out]
    exact Module.finite_of_finrank_eq_succ hdim
  let orient : Orientation ℝ V (Fin 2) :=
    orientazione2 V (Fact.out : Module.finrank ℝ V = 2)
  letI : Module.Oriented ℝ V (Fin 2) := ⟨orient⟩
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  let cf : V := Finset.univ.centroid ℝ
    (fun i : Fin (m + 1) => (f : V → V)^[(i : ℕ)] 0)
  let cg : V := Finset.univ.centroid ℝ
    (fun i : Fin (m + 1) => (g : V → V)^[(i : ℕ)] 0)
  have hcf : f cf = cf := by
    subst p
    exact orbita_centroid_fisso f 0 hfcl
  have hcg : g cg = cg := by
    subst p
    exact orbita_centroid_fisso g 0 hgcl
  obtain ⟨thetaf, hthetaf⟩ :=
    AngoloInterno.exists_linear_rotation_of_closed_injective_orbit
      p hp f 0 cf hcf hfinj
  obtain ⟨thetag, hthetag⟩ :=
    AngoloInterno.exists_linear_rotation_of_closed_injective_orbit
      p hp g 0 cg hcg hginj
  let d : V := f 0
  have hd0 : d ≠ 0 := by
    intro hd
    let i0 : Fin p := ⟨0, by omega⟩
    let i1 : Fin p := ⟨1, by omega⟩
    have hi : i1 = i0 := by
      apply hfinj
      simpa [i1, i0, d] using hd
    have := congrArg Fin.val hi
    simp [i1, i0] at this
  have hlin_apply : f.linearIsometryEquiv d = g.linearIsometryEquiv d := by
    have hfmap := f.map_vsub (f 0) 0
    have hgmap := g.map_vsub (g 0) 0
    simp only [vsub_eq_sub, sub_zero] at hfmap hgmap
    calc
      f.linearIsometryEquiv d = f (f 0) - f 0 := by simpa [d] using hfmap
      _ = g (g 0) - g 0 := by rw [hsecond, hfirst]
      _ = g.linearIsometryEquiv (g 0) := hgmap.symm
      _ = g.linearIsometryEquiv d := by
        change g.linearIsometryEquiv (g 0) = g.linearIsometryEquiv (f 0)
        rw [hfirst]
  have htheta : thetaf = thetag := by
    apply rotation_angle_injective EuclideanGeometry.o hd0
    simpa only [hthetaf, hthetag] using hlin_apply
  have hlin : f.linearIsometryEquiv = g.linearIsometryEquiv := by
    rw [hthetaf, hthetag, htheta]
  apply AffineIsometryEquiv.ext
  intro q
  have hfmap := f.map_vsub q 0
  have hgmap := g.map_vsub q 0
  simp only [vsub_eq_sub, sub_zero] at hfmap hgmap
  calc
    f q = f.linearIsometryEquiv q + f 0 := by rw [hfmap]; abel
    _ = g.linearIsometryEquiv q + g 0 := by rw [hlin, hfirst]
    _ = g q := by rw [hgmap]; abel

/-- Oriented form of facet rigidity: the two orbit parametrisations start at
the same endpoint and take the common side in the same direction. -/
theorem faccetta_determinata_orientata
    {A B : Set (E 3)} {p : ℕ}
    {rhoA rhoB : Isom 3} {x : E 3}
    (hAgen : A = convexHull ℝ (Set.range fun i : Fin p =>
      (rhoA : E 3 → E 3)^[(i : ℕ)] x))
    (hAfix : (rhoA : E 3 → E 3) '' A = A)
    (hAinj : Function.Injective (fun i : Fin p =>
      (rhoA : E 3 → E 3)^[(i : ℕ)] x))
    (hAcl : (rhoA : E 3 → E 3)^[p] x = x)
    (hBgen : B = convexHull ℝ (Set.range fun i : Fin p =>
      (rhoB : E 3 → E 3)^[(i : ℕ)] x))
    (hBfix : (rhoB : E 3 → E 3) '' B = B)
    (hBinj : Function.Injective (fun i : Fin p =>
      (rhoB : E 3 → E 3)^[(i : ℕ)] x))
    (hBcl : (rhoB : E 3 → E 3)^[p] x = x)
    (hp : 3 ≤ p)
    (hdA : Module.finrank ℝ (vectorSpan ℝ A) = 2)
    (hdB : Module.finrank ℝ (vectorSpan ℝ B) = 2)
    (hpiano : affineSpan ℝ A = affineSpan ℝ B)
    (hstep : rhoA x = rhoB x)
    (h : E 3 →L[ℝ] ℝ)
    (hxy : h x = h (rhoA x))
    (hAlower : ∀ z ∈ A, h x ≤ h z)
    (hBlower : ∀ z ∈ B, h x ≤ h z)
    (hAface : {z ∈ A | h z = h x} = segment ℝ x (rhoA x))
    (hBface : {z ∈ B | h z = h x} = segment ℝ x (rhoA x)) :
    A = B := by
  classical
  let i0 : Fin p := ⟨0, by omega⟩
  have hxA : x ∈ A := by
    rw [hAgen]
    exact subset_convexHull ℝ _ ⟨i0, by simp [i0]⟩
  have hxB : x ∈ B := by
    rw [hBgen]
    exact subset_convexHull ℝ _ ⟨i0, by simp [i0]⟩
  have hspan : vectorSpan ℝ B = vectorSpan ℝ A := by
    have hpdir := congrArg AffineSubspace.direction hpiano
    simpa only [direction_affineSpan] using hpdir.symm
  have hangA := supported_orbit_first_angle rhoA x hAgen hAfix hAinj hAcl
    hp hdA h hxy hAlower hAface
  have hangB := supported_orbit_first_angle rhoB x hBgen hBfix hBinj hBcl
    hp hdB h (hxy.trans (congrArg h hstep)) hBlower (by simpa [hstep] using hBface)
  let y : E 3 := rhoA x
  let zA : E 3 := (rhoA : E 3 → E 3)^[2] x
  let zB : E 3 := (rhoB : E 3 → E 3)^[2] x
  have hyA : y ∈ A := by
    rw [hAgen]
    exact subset_convexHull ℝ _ ⟨⟨1, by omega⟩, by simp [y]⟩
  have hyB : y ∈ B := by
    rw [hBgen]
    exact subset_convexHull ℝ _ ⟨⟨1, by omega⟩, by simp [y, hstep]⟩
  have hzAA : zA ∈ A := by
    rw [hAgen]
    exact subset_convexHull ℝ _ ⟨⟨2, by omega⟩, by simp [zA]⟩
  have hzBB : zB ∈ B := by
    rw [hBgen]
    exact subset_convexHull ℝ _ ⟨⟨2, by omega⟩, by simp [zB]⟩
  have hxyne : x ≠ y := by
    intro heq
    have hi : (⟨1, by omega⟩ : Fin p) = ⟨0, by omega⟩ := by
      apply hAinj
      simpa [y] using heq.symm
    have := congrArg Fin.val hi
    simp at this
  have hdyA : dist y zA = dist x y := by
    simpa [y, zA, Function.iterate_succ_apply'] using rhoA.dist_map x (rhoA x)
  have hdyB : dist y zB = dist x y := by
    have hm := rhoB.dist_map x (rhoB x)
    simpa [y, zB, hstep, Function.iterate_succ_apply'] using hm
  have hdxz : dist x zA = dist x zB := by
    rw [← sq_eq_sq₀ dist_nonneg dist_nonneg]
    simp only [pow_two]
    rw [EuclideanGeometry.law_cos x y zA,
      EuclideanGeometry.law_cos x y zB]
    have ha : EuclideanGeometry.angle x y zA =
        AngoloInterno.regularInteriorAngle p := by simpa [y, zA] using hangA
    have hb : EuclideanGeometry.angle x y zB =
        AngoloInterno.regularInteriorAngle p := by simpa [y, zB, hstep] using hangB
    rw [ha, hb, dist_comm zA y, dist_comm zB y, hdyA, hdyB]
  obtain ⟨cA, hcA⟩ := exists_fixed_point_of_closed_orbit rhoA x (by omega) hAcl
  obtain ⟨cB, hcB⟩ := exists_fixed_point_of_closed_orbit rhoB x (by omega) hBcl
  have hzA_not : zA ∉ segment ℝ x y := by
    simpa [zA, y] using orbit_two_not_mem_first_segment hp rhoA x cA hcA hAinj
  have hzB_not : zB ∉ segment ℝ x y := by
    simpa [zB, y, hstep] using orbit_two_not_mem_first_segment hp rhoB x cB hcB hBinj
  have hzA_strict : h x < h zA := by
    have hle := hAlower zA hzAA
    exact lt_of_le_of_ne hle (fun heq => hzA_not (by
      rw [← hAface]
      exact ⟨hzAA, heq.symm⟩))
  have hzB_strict : h x < h zB := by
    have hle := hBlower zB hzBB
    exact lt_of_le_of_ne hle (fun heq => hzB_not (by
      rw [← hBface]
      exact ⟨hzBB, heq.symm⟩))
  let W : Submodule ℝ (E 3) := vectorSpan ℝ A
  have hW2 : Module.finrank ℝ W = 2 := hdA
  letI : FiniteDimensional ℝ W := by
    have hw : Module.finrank ℝ W = 1 + 1 := by omega
    exact Module.finite_of_finrank_eq_succ hw
  letI : Fact (Module.finrank ℝ W = 2) := ⟨hW2⟩
  let o : Orientation ℝ W (Fin 2) := orientazione2 W hW2
  have hyd : y - x ∈ W := by simpa [W] using vsub_mem_vectorSpan ℝ hyA hxA
  have hzAd : zA - x ∈ W := by simpa [W] using vsub_mem_vectorSpan ℝ hzAA hxA
  have hzBd : zB - x ∈ W := by
    have hbmem : zB - x ∈ vectorSpan ℝ B := vsub_mem_vectorSpan ℝ hzBB hxB
    simpa [W, hspan] using hbmem
  let d : W := ⟨y - x, hyd⟩
  let za : W := ⟨zA - x, hzAd⟩
  let zb : W := ⟨zB - x, hzBd⟩
  let L : W →L[ℝ] ℝ := h.comp W.subtypeL
  have hd0 : d ≠ 0 := by
    intro hd
    apply hxyne
    have := congrArg Subtype.val hd
    exact (sub_eq_zero.mp (by simpa [d] using this)).symm
  have hLd : L d = 0 := by
    change h (y - x) = 0
    rw [map_sub]
    simp [y, hxy]
  have hLza : 0 < L za := by
    change 0 < h (zA - x)
    rw [map_sub]
    linarith
  have hLzb : 0 < L zb := by
    change 0 < h (zB - x)
    rw [map_sub]
    linarith
  have hnza : ‖za‖ = ‖zb‖ := by
    simpa [za, zb, dist_eq_norm, norm_sub_rev] using hdxz
  have hdza : dist d za = dist d zb := by
    have hdistyz : dist y zA = dist y zB := hdyA.trans hdyB.symm
    simpa [d, za, zb, dist_eq_norm] using hdistyz
  have hz : zA = zB := by
    have hsub := eq_of_two_dist_eq_of_functional_pos o L hd0 hLd hLza hLzb hnza hdza
    have hval := congrArg Subtype.val hsub
    simpa [za, zb] using sub_left_injective hval
  let chiA : W ≃ᵃⁱ[ℝ] W := carta rhoA A hAfix x hxA
  let chiB0 : (vectorSpan ℝ B) ≃ᵃⁱ[ℝ] (vectorSpan ℝ B) :=
    carta rhoB B hBfix x hxB
  let e : (vectorSpan ℝ B) ≃ₗᵢ[ℝ] W :=
    LinearIsometryEquiv.ofEq (vectorSpan ℝ B) W hspan
  let chiB : W ≃ᵃⁱ[ℝ] W :=
    e.symm.toAffineIsometryEquiv.trans chiB0 |>.trans e.toAffineIsometryEquiv
  have hchiB_iterate : ∀ k : ℕ,
      (chiB : W → W)^[k] 0 = e ((chiB0 : vectorSpan ℝ B →
        vectorSpan ℝ B)^[k] 0) := by
    intro k
    induction k with
    | zero => simp [e]
    | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        simp [chiB]
  have hchiB_chart : ∀ k : ℕ,
      x + (((chiB : W → W)^[k] 0 : W) : E 3) =
        (rhoB : E 3 → E 3)^[k] x := by
    intro k
    rw [hchiB_iterate]
    simpa [e, chiB0] using carta_iterate rhoB B hBfix x hxB k
  have hchiAcl : (chiA : W → W)^[p] 0 = 0 :=
    carta_orbita_chiusa rhoA A hAfix x hxA p hAcl
  have hchiAinj : Function.Injective (fun i : Fin p =>
      (chiA : W → W)^[(i : ℕ)] (0 : W)) :=
    carta_orbita_iniettiva rhoA A hAfix x hxA p hAinj
  have hchiBcl : (chiB : W → W)^[p] 0 = 0 := by
    have hb := hchiB_chart p
    rw [hBcl] at hb
    apply Subtype.ext
    have := congrArg (fun q : E 3 => q - x) hb
    simpa using this
  have hchiBinj : Function.Injective (fun i : Fin p =>
      (chiB : W → W)^[(i : ℕ)] (0 : W)) := by
    intro i j hij
    apply hBinj
    change (rhoB : E 3 → E 3)^[(i : ℕ)] x =
      (rhoB : E 3 → E 3)^[(j : ℕ)] x
    calc
      (rhoB : E 3 → E 3)^[(i : ℕ)] x =
          x + (((chiB : W → W)^[(i : ℕ)] 0 : W) : E 3) :=
        (hchiB_chart (i : ℕ)).symm
      _ = x + (((chiB : W → W)^[(j : ℕ)] 0 : W) : E 3) :=
        congrArg (fun q : W => x + (q : E 3)) hij
      _ = (rhoB : E 3 → E 3)^[(j : ℕ)] x := hchiB_chart (j : ℕ)
  have hchi_first : chiA 0 = chiB 0 := by
    apply Subtype.ext
    have ha := carta_iterate rhoA A hAfix x hxA 1
    have hb := hchiB_chart 1
    simp only [Function.iterate_one] at ha hb
    have hav : ((chiA 0 : W) : E 3) = rhoA x - x :=
      eq_sub_of_add_eq' (by simpa [chiA] using ha)
    have hbv : ((chiB 0 : W) : E 3) = rhoB x - x := eq_sub_of_add_eq' hb
    rw [hav, hbv, hstep]
  have hchi_second : chiA (chiA 0) = chiB (chiB 0) := by
    apply Subtype.ext
    have ha := carta_iterate rhoA A hAfix x hxA 2
    have hb := hchiB_chart 2
    change ((chiA (chiA 0) : W) : E 3) = ((chiB (chiB 0) : W) : E 3)
    have hav : ((chiA (chiA 0) : W) : E 3) = zA - x := by
      exact eq_sub_of_add_eq' (by simpa [chiA, zA] using ha)
    have hbv : ((chiB (chiB 0) : W) : E 3) = zB - x := by
      exact eq_sub_of_add_eq' (by simpa [zB] using hb)
    rw [hav, hbv, hz]
  have hchi : chiA = chiB := affine_isometry_eq_of_first_three hp chiA chiB
    hchiAcl hchiBcl hchiAinj hchiBinj hchi_first hchi_second
  have hrange : (Set.range fun i : Fin p =>
      (rhoA : E 3 → E 3)^[(i : ℕ)] x) =
      Set.range fun i : Fin p => (rhoB : E 3 → E 3)^[(i : ℕ)] x := by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      have ha := carta_iterate rhoA A hAfix x hxA (i : ℕ)
      have hb := hchiB_chart (i : ℕ)
      have hab : x + (((chiA : W → W)^[(i : ℕ)] 0 : W) : E 3) =
          x + (((chiB : W → W)^[(i : ℕ)] 0 : W) : E 3) := by rw [hchi]
      exact (ha.symm.trans (hab.trans hb)).symm
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      have ha := carta_iterate rhoA A hAfix x hxA (i : ℕ)
      have hb := hchiB_chart (i : ℕ)
      have hab : x + (((chiB : W → W)^[(i : ℕ)] 0 : W) : E 3) =
          x + (((chiA : W → W)^[(i : ℕ)] 0 : W) : E 3) := by rw [hchi]
      exact (hb.symm.trans (hab.trans ha)).symm
  rw [hAgen, hBgen, hrange]

/-- A regular polygonal facet is determined by its plane, one (unordered)
side, and the supporting half-plane containing it. -/
theorem faccetta_determinata
    {A B : Set (E 3)} {p : ℕ} {ell : ℝ}
    {rhoA : Isom 3} {xA : E 3} {rhoB : Isom 3} {xB : E 3}
    (hAgen : A = convexHull ℝ (Set.range fun i : Fin p =>
      (rhoA : E 3 → E 3)^[(i : ℕ)] xA))
    (hAfix : (rhoA : E 3 → E 3) '' A = A)
    (hAinj : Function.Injective (fun i : Fin p =>
      (rhoA : E 3 → E 3)^[(i : ℕ)] xA))
    (hAcl : (rhoA : E 3 → E 3)^[p] xA = xA)
    (hAdist : dist xA (rhoA xA) = ell)
    (hBgen : B = convexHull ℝ (Set.range fun i : Fin p =>
      (rhoB : E 3 → E 3)^[(i : ℕ)] xB))
    (hBfix : (rhoB : E 3 → E 3) '' B = B)
    (hBinj : Function.Injective (fun i : Fin p =>
      (rhoB : E 3 → E 3)^[(i : ℕ)] xB))
    (hBcl : (rhoB : E 3 → E 3)^[p] xB = xB)
    (hBdist : dist xB (rhoB xB) = ell)
    (hp : 3 ≤ p) (hell : 0 < ell)
    (hdA : Module.finrank ℝ (vectorSpan ℝ A) = 2)
    (hdB : Module.finrank ℝ (vectorSpan ℝ B) = 2)
    (hpiano : affineSpan ℝ A = affineSpan ℝ B)
    (hlato : segment ℝ xA (rhoA xA) = segment ℝ xB (rhoB xB))
    (hsemi : SemipianoComune A B xA (rhoA xA)) :
    A = B := by
  classical
  rcases hsemi with ⟨h, hxy, hAlower, hBlower, hAface, hBface⟩
  have hne : xA ≠ rhoA xA := by
    intro heq
    have hz : dist xA (rhoA xA) = 0 := dist_eq_zero.mpr heq
    linarith
  have hend := endpoints_of_segment_eq_of_dist_eq hlato hne
    (hAdist.trans hBdist.symm)
  rcases hend with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · subst xB
    exact faccetta_determinata_orientata hAgen hAfix hAinj hAcl
      hBgen hBfix hBinj hBcl hp hdA hdB hpiano hy
      h hxy hAlower hBlower hAface hBface
  · have hp0 : 0 < p := by omega
    have hgf : Function.LeftInverse
        (rhoB.symm : E 3 → E 3) (rhoB : E 3 → E 3) :=
      rhoB.symm_apply_apply
    have hfg : Function.LeftInverse
        (rhoB : E 3 → E 3) (rhoB.symm : E 3 → E 3) :=
      rhoB.apply_symm_apply
    have hrev := reverse_cycle_at_next hgf hfg hp0 hBcl hBinj
    have hBclRev : (rhoB.symm : E 3 → E 3)^[p] xA = xA := by
      simpa [hx] using hrev.1
    have hBinjRev : Function.Injective (fun i : Fin p =>
        (rhoB.symm : E 3 → E 3)^[(i : ℕ)] xA) := by
      simpa [hx] using hrev.2.1
    have hBgenRev : B = convexHull ℝ (Set.range fun i : Fin p =>
        (rhoB.symm : E 3 → E 3)^[(i : ℕ)] xA) := by
      calc
        B = convexHull ℝ (Set.range fun i : Fin p =>
            (rhoB : E 3 → E 3)^[(i : ℕ)] xB) := hBgen
        _ = convexHull ℝ (Set.range fun i : Fin p =>
            (rhoB.symm : E 3 → E 3)^[(i : ℕ)] (rhoB xB)) :=
          congrArg (convexHull ℝ) hrev.2.2.symm
        _ = convexHull ℝ (Set.range fun i : Fin p =>
            (rhoB.symm : E 3 → E 3)^[(i : ℕ)] xA) := by rw [hx]
    have hBfixRev : (rhoB.symm : E 3 → E 3) '' B = B := by
      exact symm_image_eq_of_image_eq rhoB.toEquiv hBfix
    have hstep : rhoA xA = rhoB.symm xA := by
      calc
        rhoA xA = xB := hy
        _ = rhoB.symm (rhoB xB) := (rhoB.symm_apply_apply xB).symm
        _ = rhoB.symm xA := by rw [hx]
    exact faccetta_determinata_orientata hAgen hAfix hAinj hAcl
      hBgenRev hBfixRev hBinjRev hBclRev hp hdA hdB hpiano hstep
      h hxy hAlower hBlower hAface hBface

end LeanEval.Geometry.PlatonicClassification
