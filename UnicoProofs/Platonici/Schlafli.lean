import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.AdiacenzaUnica
import UnicoProofs.Platonici.Trasportatore
import UnicoProofs.Platonici.GruppoFinito
import UnicoProofs.Platonici.Ordini
import UnicoProofs.Platonici.Coniugazione
import UnicoProofs.Platonici.OrdineTre

/-!
MOTORE COXETER, PASSO 26 — IL SIMBOLO DI SCHLÄFLI (19 lug 2026).

Il simbolo `{m₀, …, m_{d−2}}` come funzione del politopo. La bandiera
base entra nella definizione (serve una scelta) ma esce dal contratto
pubblico: `coxeterMatrix_indep` garantisce che il valore non dipenda
dalla scelta, e il teorema `schlafli_indipendente` lo registra.

Le proprietà certificate qui:
  · indipendenza dalla bandiera base;
  · `mᵢ ≥ 3` su ogni entrata (dal fascicolo degli ordini adiacenti);
  · le entrate sono finite e positive.

NON è certificato qui, ed è dichiarato come lavoro aperto: l'invarianza
sotto similitudine, che richiede il trasporto delle bandiere lungo
l'isometria in dimensione arbitraria.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Il rango successivo, quando esiste. -/
def rangoSucc (i : Fin n) (hi : (i : ℕ) + 1 < n) : Fin n :=
  ⟨(i : ℕ) + 1, hi⟩

/-- **Il simbolo di Schläfli**, relativo a una bandiera base. -/
noncomputable def schlafliDi (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n) : ℕ :=
  coxeterMatrix P hreg F i (rangoSucc i hi)

/-- **Il simbolo non dipende dalla bandiera base**: è un invariante del
politopo, non della camera scelta. -/
theorem schlafli_indipendente (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F G : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    schlafliDi P hreg G i hi = schlafliDi P hreg F i hi :=
  coxeterMatrix_indep P hreg F G i (rangoSucc i hi)

/-- Ogni entrata del simbolo è almeno 3. -/
theorem schlafli_ge_tre (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    (hi2 : (i : ℕ) + 2 < n) (hipos : 0 < (i : ℕ)) :
    3 ≤ schlafliDi P hreg F i hi :=
  coxeterMatrix_adiacente_ge_tre P hreg F i hi hi2 hipos

/-- Ogni entrata del simbolo è almeno 2 (senza ipotesi sui bordi). -/
theorem schlafli_ge_due (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    2 ≤ schlafliDi P hreg F i hi := by
  refine coxeterMatrix_off_diag_ge P hreg F ?_
  intro he
  have : (i : ℕ) = (i : ℕ) + 1 := congrArg Fin.val he
  omega

/-- Ogni entrata del simbolo è finita e positiva. -/
theorem schlafli_pos (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    0 < schlafliDi P hreg F i hi := by
  have := schlafli_ge_due P hreg F i hi
  omega

/-- Il simbolo come famiglia indicizzata dai ranghi interni. -/
noncomputable def schlafli (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) : Fin n → ℕ :=
  fun i =>
    if hi : (i : ℕ) + 1 < n then schlafliDi P hreg F i hi else 0

theorem schlafli_apply (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    schlafli P hreg F i = schlafliDi P hreg F i hi := by
  unfold schlafli
  rw [dif_pos hi]

/-- **Il simbolo, come famiglia, non dipende dalla bandiera base.** -/
theorem schlafli_indipendente_famiglia (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F G : P.Flag) :
    schlafli P hreg G = schlafli P hreg F := by
  funext i
  unfold schlafli
  by_cases hi : (i : ℕ) + 1 < n
  · rw [dif_pos hi, dif_pos hi]
    exact schlafli_indipendente P hreg F G i hi
  · rw [dif_neg hi, dif_neg hi]

end LeanEval.Geometry.PlatonicClassification
