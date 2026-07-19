import Mathlib
import UnicoProofs.Platonici.RegolariBenchmark

open Set Metric

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

abbrev E2 := E 2

def poligonoAngolo (n : Nat) (k : Fin n) : Real :=
  2 * Real.pi * (k : Real) / (n : Real)

def poligonoVertice (n : Nat) (k : Fin n) : E2 :=
  WithLp.toLp 2 ![Real.cos (poligonoAngolo n k),
    Real.sin (poligonoAngolo n k)]

def poligonoBase : E2 := poligonoVertice 1 0

open Classical in
def verticiPoligono (n : Nat) : Finset E2 :=
  if n = 0 then {poligonoBase} else Finset.univ.image (poligonoVertice n)

theorem norma_poligonoVertice (n : Nat) (k : Fin n) :
    norm (poligonoVertice n k) = 1 := by
  rw [EuclideanSpace.norm_eq]
  rw [Fin.sum_univ_two]
  simp only [poligonoVertice, Matrix.cons_val_zero, Real.norm_eq_abs,
    sq_abs, Matrix.cons_val_one]
  have htrig := Real.sin_sq_add_cos_sq (poligonoAngolo n k)
  rw [show Real.cos (poligonoAngolo n k) ^ 2 +
    Real.sin (poligonoAngolo n k) ^ 2 = 1 by nlinarith]
  simp

theorem poligonoAngolo_nonneg {n : Nat} (k : Fin n) :
    0 <= poligonoAngolo n k := by
  unfold poligonoAngolo
  positivity

theorem poligonoAngolo_lt_two_pi {n : Nat} (hn : Not (n = 0)) (k : Fin n) :
    poligonoAngolo n k < 2 * Real.pi := by
  have hnR : (0 : Real) < (n : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hkR : (k : Real) < (n : Real) := by
    exact_mod_cast k.isLt
  unfold poligonoAngolo
  calc
    2 * Real.pi * (k : Real) / (n : Real) <
        (2 * Real.pi * (n : Real)) / (n : Real) :=
      (div_lt_div_iff_of_pos_right hnR).2 (by
        nlinarith [Real.pi_pos])
    _ = 2 * Real.pi := by field_simp

theorem poligonoVertice_injective {n : Nat} (hn : Not (n = 0)) :
    Function.Injective (poligonoVertice n) := by
  intro i j hij
  have hcos : Real.cos (poligonoAngolo n i) =
      Real.cos (poligonoAngolo n j) := by
    have h := congrArg (fun x : E2 => (WithLp.ofLp x) 0) hij
    simpa [poligonoVertice] using h
  have hsin : Real.sin (poligonoAngolo n i) =
      Real.sin (poligonoAngolo n j) := by
    have h := congrArg (fun x : E2 => (WithLp.ofLp x) 1) hij
    simpa [poligonoVertice] using h
  have hcosSub : Real.cos
      (poligonoAngolo n i - poligonoAngolo n j) = 1 := by
    rw [Real.cos_sub]
    rw [hcos, hsin]
    nlinarith [Real.sin_sq_add_cos_sq (poligonoAngolo n j)]
  have hlower : -(2 * Real.pi) <
      poligonoAngolo n i - poligonoAngolo n j := by
    have hi0 := poligonoAngolo_nonneg i
    have hjlt := poligonoAngolo_lt_two_pi hn j
    linarith
  have hupper : poligonoAngolo n i - poligonoAngolo n j <
      2 * Real.pi := by
    have hj0 := poligonoAngolo_nonneg j
    have hilt := poligonoAngolo_lt_two_pi hn i
    linarith
  have hangle : poligonoAngolo n i = poligonoAngolo n j := by
    have hz := (Real.cos_eq_one_iff_of_lt_of_lt hlower hupper).1 hcosSub
    linarith
  apply Fin.ext
  have hnR : (0 : Real) < (n : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero hn)
  unfold poligonoAngolo at hangle
  have hcast : (i : Real) = (j : Real) := by
    have hnum : 2 * Real.pi * (i : Real) =
        2 * Real.pi * (j : Real) :=
      (div_left_inj' (ne_of_gt hnR)).mp hangle
    nlinarith [Real.pi_pos]
  exact_mod_cast hcast

theorem verticiPoligono_nonempty (n : Nat) : (verticiPoligono n).Nonempty := by
  classical
  by_cases hn : n = 0
  case pos =>
    simp [verticiPoligono, hn]
  case neg =>
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let k : Fin n := Fin.mk 0 hnpos
    refine Exists.intro (poligonoVertice n k) ?_
    simp [verticiPoligono, hn]

theorem verticiPoligono_cosferici (n : Nat) :
    (verticiPoligono n : Set E2) <= sphere 0 1 := by
  classical
  intro x hx
  by_cases hn : n = 0
  case pos =>
    subst n
    have hx0 : x = poligonoBase := by
      simpa [verticiPoligono] using hx
    subst x
    rw [mem_sphere_zero_iff_norm]
    exact norma_poligonoVertice 1 0
  case neg =>
    rw [mem_sphere_zero_iff_norm]
    simp [verticiPoligono, hn] at hx
    cases hx with
    | intro k hk =>
      subst x
      exact norma_poligonoVertice n k

noncomputable def poligono (n : Nat) : ConvexPolytope 2 where
  vertices := verticiPoligono n
  vertices_nonempty := verticiPoligono_nonempty n
  vertices_eq_extremePoints := by
    exact (F10.cosferico_extremePoints 0 1 _
      (verticiPoligono_cosferici n)).symm

theorem poligono_card (n : Nat) (hn : 3 <= n) :
    (poligono n).vertices.card = n := by
  classical
  have hn0 : Not (n = 0) := by omega
  simp only [poligono, verticiPoligono, if_neg hn0]
  rw [Finset.card_image_of_injective Finset.univ
    (poligonoVertice_injective hn0)]
  simp

def primiTreVertici (n : Nat) (hn : 3 <= n) : Fin 3 -> E2 :=
  fun k => poligonoVertice n (Fin.castLE hn k)

theorem primiTreVertici_injective (n : Nat) (hn : 3 <= n) :
    Function.Injective (primiTreVertici n hn) := by
  have hn0 : Not (n = 0) := by omega
  exact (poligonoVertice_injective hn0).comp (Fin.castLE_injective hn)

theorem primiTreVertici_affineIndependent (n : Nat) (hn : 3 <= n) :
    AffineIndependent Real (primiTreVertici n hn) := by
  have hcos : EuclideanGeometry.Cospherical
      (Set.range (primiTreVertici n hn)) := by
    refine Exists.intro 0 (Exists.intro 1 ?_)
    intro x hx
    cases hx with
    | intro k hk =>
      subst x
      simpa [primiTreVertici, dist_zero_right] using
        norma_poligonoVertice n (Fin.castLE hn k)
  exact hcos.affineIndependent Set.Subset.rfl
    (primiTreVertici_injective n hn)

theorem affineSpan_verticiPoligono_eq_top (n : Nat) (hn : 3 <= n) :
    affineSpan Real (verticiPoligono n : Set E2) =
      affineSpan Real (Set.univ : Set E2) := by
  have hai := primiTreVertici_affineIndependent n hn
  have hspan :=
      (hai.affineSpan_eq_top_iff_card_eq_finrank_add_one).2 (by
    rw [Fintype.card_fin, finrank_euclideanSpace, Fintype.card_fin]
    )
  have hn0 : Not (n = 0) := by omega
  have hrange : Set.range (primiTreVertici n hn) <=
      (verticiPoligono n : Set E2) := by
    intro x hx
    cases hx with
    | intro k hk =>
      subst x
      simp [primiTreVertici, verticiPoligono, hn0]
  have hle := affineSpan_mono Real hrange
  rw [hspan] at hle
  simpa only [AffineSubspace.span_univ] using top_unique hle

theorem poligono_isFullDim (n : Nat) (hn : 3 <= n) :
    (poligono n).IsFullDim := by
  change Module.finrank Real (vectorSpan Real
    (convexHull Real (verticiPoligono n : Set E2))) = 2
  rw [(direction_affineSpan Real
      (convexHull Real (verticiPoligono n : Set E2))).symm,
    affineSpan_convexHull, affineSpan_verticiPoligono_eq_top n hn,
    AffineSubspace.span_univ, AffineSubspace.direction_top, finrank_top,
    finrank_euclideanSpace, Fintype.card_fin]

end LeanEval.Geometry.PlatonicClassification
