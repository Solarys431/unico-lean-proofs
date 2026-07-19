import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.FacciaIntermedia
import UnicoProofs.Platonici.DiamanteRelativo
import UnicoProofs.Platonici.SecondoIntermedio

/-!
MOTORE COXETER, PASSO 4 — L'ADIACENZA DI BANDIERE (19 lug 2026).

La bandiera adiacente in rango `i`: stessa catena ovunque, faccia diversa
al solo rango `i`. Qui il montaggio per i ranghi con un vicino sopra e
uno sotto dentro la catena (0 < i, con la faccia superiore che è
`F.face (i+1)` per i ranghi interni e `P.toSet` per il rango massimo):
il diamante ∃! fornisce la faccia sostitutiva, `Function.update` rimonta
la bandiera, e i tre campi (`isFace`, `dim_eq`, `strict_mono`) si
verificano per casi.

Il caso di bordo `i = 0` (due vertici per spigolo) arriva dal fascicolo
40 e si innesterà nello stesso schema.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Bandiere adiacenti al rango `i`: coincidono ovunque tranne che in `i`. -/
def FlagAdjacentAt (P : ConvexPolytope n) (F G : P.Flag) (i : Fin n) :
    Prop :=
  (∀ j : Fin n, j ≠ i → G.face j = F.face j) ∧ G.face i ≠ F.face i

/-- La bandiera ottenuta sostituendo la faccia al rango `i`. -/
noncomputable def sostituisci (P : ConvexPolytope n) (F : P.Flag)
    (i : Fin n) (C : Set (E n)) (hC : P.IsFace C)
    (hdim : faceDim C = (i : ℕ))
    (hsotto : ∀ j : Fin n, j < i → F.face j ⊂ C)
    (hsopra : ∀ j : Fin n, i < j → C ⊂ F.face j) : P.Flag where
  face := Function.update F.face i C
  isFace := by
    intro k
    by_cases hk : k = i
    · rw [hk, Function.update_self]
      exact hC
    · rw [Function.update_of_ne hk]
      exact F.isFace k
  dim_eq := by
    intro k
    by_cases hk : k = i
    · rw [hk, Function.update_self]
      exact hdim
    · rw [Function.update_of_ne hk]
      exact F.dim_eq k
  strict_mono := by
    intro j k hjk
    by_cases hj : j = i
    · subst hj
      have hk : j ≠ k := ne_of_lt hjk
      rw [Function.update_self, Function.update_of_ne (Ne.symm hk)]
      exact hsopra k hjk
    · by_cases hk : k = i
      · subst hk
        rw [Function.update_of_ne hj, Function.update_self]
        exact hsotto j hjk
      · rw [Function.update_of_ne hj, Function.update_of_ne hk]
        exact F.strict_mono j k hjk

@[simp] theorem sostituisci_face_self (P : ConvexPolytope n) (F : P.Flag)
    (i : Fin n) (C : Set (E n)) (hC hdim hsotto hsopra) :
    (sostituisci P F i C hC hdim hsotto hsopra).face i = C :=
  Function.update_self ..

@[simp] theorem sostituisci_face_ne (P : ConvexPolytope n) (F : P.Flag)
    (i : Fin n) (C : Set (E n)) (hC hdim hsotto hsopra)
    {j : Fin n} (hj : j ≠ i) :
    (sostituisci P F i C hC hdim hsotto hsopra).face j = F.face j :=
  Function.update_of_ne hj _ _

/-- Le facce sotto la sostituita restano dentro: la catena sotto `i` è
già dentro `F.face (i-1) ⊂ C` quando `C` viene dal diamante. -/
theorem catena_sotto (P : ConvexPolytope n) (F : P.Flag) {i : Fin n}
    {C : Set (E n)} {im : Fin n} (him : (im : ℕ) + 1 = (i : ℕ))
    (hAC : F.face im ⊂ C) :
    ∀ j : Fin n, j < i → F.face j ⊂ C := by
  intro j hj
  by_cases hjim : j = im
  · rw [hjim]; exact hAC
  · have hjlt : j < im := by
      rw [Fin.lt_def] at hj ⊢
      have hne : (j : ℕ) ≠ (im : ℕ) := fun h => hjim (Fin.ext h)
      omega
    exact (F.strict_mono j im hjlt).trans hAC

/-- Le facce sopra la sostituita restano fuori. -/
theorem catena_sopra (P : ConvexPolytope n) (F : P.Flag) {i : Fin n}
    {C : Set (E n)} {ip : Fin n} (hip : (i : ℕ) + 1 = (ip : ℕ))
    (hCB : C ⊂ F.face ip) :
    ∀ j : Fin n, i < j → C ⊂ F.face j := by
  intro j hj
  by_cases hjip : j = ip
  · rw [hjip]; exact hCB
  · have hjgt : ip < j := by
      rw [Fin.lt_def] at hj ⊢
      have hne : (j : ℕ) ≠ (ip : ℕ) := fun h => hjip (Fin.ext h)
      omega
    exact hCB.trans (F.strict_mono ip j hjgt)

end LeanEval.Geometry.PlatonicClassification
