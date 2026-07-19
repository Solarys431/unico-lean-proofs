import UnicoProofs.Platonici.Orientazione

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope FiniteConvexPolytope Module

theorem ventagli_uguali_al_vicino_esplicito
    (P Q : ConvexPolytope 3) {p q : Nat} [NeZero q]
    (hP : P.asFinite.IsCyclicallyRegularOfType p q)
    (hQ : Q.asFinite.IsCyclicallyRegularOfType p q)
    {v : E 3} (hvP : Membership.mem P.vertices v)
    (hvQ : Membership.mem Q.vertices v)
    (DP : P.asFinite.CyclicVertexData v q)
    (DQ : Q.asFinite.CyclicVertexData v q)
    (hdir : dir P.asFinite v DP = dir Q.asFinite v DQ)
    (hdiam : forall k, Metric.diam
        (Inter.inter (DP.faccetta k) (DP.faccetta (finRotate q k))) =
      Metric.diam (Inter.inter (DQ.faccetta k) (DQ.faccetta (finRotate q k))))
    (i : Fin q) :
    Exists fun (w : E 3) =>
      Exists fun (_hwP : Membership.mem P.vertices w) =>
        Exists fun (_hwQ : Membership.mem Q.vertices w) =>
          Exists fun (EP : P.asFinite.CyclicVertexData w q) =>
            Exists fun (EQ : Q.asFinite.CyclicVertexData w q) =>
              And (dir P.asFinite w EP = dir Q.asFinite w EQ)
                (And (Ne w v)
                  (Inter.inter (DP.faccetta i)
                    (DP.faccetta (finRotate q i)) = segment Real v w)) := by
  classical
  have hq : 3 <= q := hP.2.2.1
  have hvic :=
    vertice_adiacente_comune P Q hP hQ hvP hvQ DP DQ hdir hdiam i
  let w : E 3 := Classical.choose hvic
  have hwProps := Classical.choose_spec hvic
  have hwP : Membership.mem P.vertices w := by
    simpa only [w] using hwProps.1
  have hwQ : Membership.mem Q.vertices w := by
    simpa only [w] using hwProps.2.1
  have hwne : Ne w v := by
    simpa only [w] using hwProps.2.2.1
  have hwEdgeP : Membership.mem
      (Inter.inter (DP.faccetta i) (DP.faccetta (finRotate q i))) w := by
    simpa only [w] using hwProps.2.2.2.1
  have hsegP : Inter.inter (DP.faccetta i) (DP.faccetta (finRotate q i)) =
      segment Real v w := by
    simpa only [w] using hwProps.2.2.2.2.1
  have hedge := hwProps.2.2.2.2.2
  have hwEdgeQ : Membership.mem
      (Inter.inter (DQ.faccetta i) (DQ.faccetta (finRotate q i))) w := by
    rw [hedge.symm]
    exact hwEdgeP
  have hsegQ : Inter.inter (DQ.faccetta i) (DQ.faccetta (finRotate q i)) =
      segment Real v w := hedge.symm.trans hsegP
  have hfaceEdgeP := adiacenza_passo_uno_locale P hq DP i
  have hfaceEdgeQ := adiacenza_passo_uno_locale Q hQ.2.2.1 DQ i
  have hfacetNeP : Ne (DP.faccetta (finRotate q i)) (DP.faccetta i) := by
    intro h
    apply _root_.finRotate_ne_self (by omega : 2 <= q) i
    exact DP.distinte h
  have hfacetNeQ : Ne (DQ.faccetta (finRotate q i)) (DQ.faccetta i) := by
    intro h
    apply _root_.finRotate_ne_self (by omega : 2 <= q) i
    exact DQ.distinte h
  have hfanP := fan_allineato_su_faccette P hP hwP
    (Ne.symm hwne) (DP.isFacet (finRotate q i)) (DP.isFacet i) hfacetNeP
    hwEdgeP.2 hwEdgeP.1 (DP.mem_v (finRotate q i)) (DP.mem_v i)
    hfaceEdgeP.1 hfaceEdgeP.2.1 hwEdgeP
    (And.intro (DP.mem_v i) (DP.mem_v (finRotate q i)))
    Set.inter_subset_right Set.inter_subset_left
  let EP := Classical.choose hfanP
  have hEPProps := Classical.choose_spec hfanP
  have hEP0 : EP.faccetta 0 = DP.faccetta (finRotate q i) := by
    simpa only [EP] using hEPProps.1
  have hEP1 : EP.faccetta 1 = DP.faccetta i := by
    simpa only [EP] using hEPProps.2
  have hfanQ := fan_allineato_su_faccette Q hQ hwQ
    (Ne.symm hwne) (DQ.isFacet (finRotate q i)) (DQ.isFacet i) hfacetNeQ
    hwEdgeQ.2 hwEdgeQ.1 (DQ.mem_v (finRotate q i)) (DQ.mem_v i)
    hfaceEdgeQ.1 hfaceEdgeQ.2.1 hwEdgeQ
    (And.intro (DQ.mem_v i) (DQ.mem_v (finRotate q i)))
    Set.inter_subset_right Set.inter_subset_left
  let EQ := Classical.choose hfanQ
  have hEQProps := Classical.choose_spec hfanQ
  have hEQ0 : EQ.faccetta 0 = DQ.faccetta (finRotate q i) := by
    simpa only [EQ] using hEQProps.1
  have hEQ1 : EQ.faccetta 1 = DQ.faccetta i := by
    simpa only [EQ] using hEQProps.2
  have hrot01 : finRotate q (0 : Fin q) = 1 := by
    simp [finRotate_apply]
  have hedgeEP : Inter.inter (EP.faccetta 0) (EP.faccetta (finRotate q 0)) =
      segment Real v w := by
    simpa only [hrot01, hEP0, hEP1, Set.inter_comm] using hsegP
  have hedgeEQ : Inter.inter (EQ.faccetta 0) (EQ.faccetta (finRotate q 0)) =
      segment Real v w := by
    simpa only [hrot01, hEQ0, hEQ1, Set.inter_comm] using hsegQ
  have huPform := direzione_su_segmento_noto P hP hwP hvP
    (Ne.symm hwne) EP 0 hedgeEP
  have huQform := direzione_su_segmento_noto Q hQ hwQ hvQ
    (Ne.symm hwne) EQ 0 hedgeEQ
  have hzero : dir P.asFinite w EP 0 = dir Q.asFinite w EQ 0 := by
    rw [huPform, huQform]
  let j : Fin q := (finRotate q).symm i
  have hji : finRotate q j = i := (finRotate q).apply_symm_apply i
  let u : E 3 := dir P.asFinite w EP 0
  let r : E 3 := dir P.asFinite v DP j
  let z : E 3 := dir P.asFinite w EP 1
  let z' : E 3 := dir Q.asFinite w EQ 1
  have hOldForm := direzione_su_segmento_noto P hP hvP hwP hwne DP i
    (by simpa only [segment_symm] using hsegP)
  have huOld : u = -dir P.asFinite v DP i := by
    rw [show u = dir P.asFinite w EP 0 by rfl, huPform, hOldForm]
    have hsub : v - w = -(w - v) := by abel
    rw [hsub, norm_neg, smul_neg]
  have hcons : LinearIndependent Real
      ![r, dir P.asFinite v DP i] := by
    simpa only [r, hji] using raggi_consecutivi_indipendenti P hP hvP DP j
  have hconsSwap : LinearIndependent Real
      ![dir P.asFinite v DP i, r] := LinearIndependent.pair_symm_iff.mp hcons
  have hscaled := indipendenti_smul_separati
    (by norm_num : Ne (-1 : Real) 0) (by norm_num : Ne (1 : Real) 0) hconsSwap
  have hind : LinearIndependent Real ![u, r] := by
    have hminus : -dir P.asFinite v DP i = u := huOld.symm
    simpa only [neg_one_smul, hminus, one_smul] using hscaled
  have hdata :=
    dati_faccetta_adiacente P Q hP hQ hvP hvQ DP DQ hdir hdiam i
  let wData : E 3 := Classical.choose hdata
  have hdataProps := Classical.choose_spec hdata
  have hsegDataP : Inter.inter (DP.faccetta i) (DP.faccetta (finRotate q i)) =
      segment Real v wData := by
    simpa only [wData] using hdataProps.1
  have hpiano := hdataProps.2.2.1
  have hsemi : SemipianoComune (DP.faccetta i) (DQ.faccetta i) v wData := by
    simpa only [wData] using hdataProps.2.2.2
  have hwData : wData = w := by
    exact (secondo_estremo_segmento_unico (Ne.symm hwne)
      (hsegP.symm.trans hsegDataP)).symm
  rw [hwData] at hsemi
  let phi := Classical.choose hsemi
  have hsemiProps := Classical.choose_spec hsemi
  have hphiEdge : phi v = phi w := by
    simpa only [phi] using hsemiProps.1
  have hlowerP : forall z, Membership.mem (DP.faccetta i) z ->
      phi v <= phi z := by
    simpa only [phi] using hsemiProps.2.1
  have hlowerQ : forall z, Membership.mem (DQ.faccetta i) z ->
      phi v <= phi z := by
    simpa only [phi] using hsemiProps.2.2.1
  have hlevelP : {z | And (Membership.mem (DP.faccetta i) z)
      (phi z = phi v)} = segment Real v w := by
    simpa only [phi] using hsemiProps.2.2.2.1
  have hlevelQ : {z | And (Membership.mem (DQ.faccetta i) z)
      (phi z = phi v)} = segment Real v w := by
    simpa only [phi] using hsemiProps.2.2.2.2
  have hphiu : phi u = 0 := by
    rw [show u = dir P.asFinite w EP 0 by rfl, huPform]
    simp [map_sub, smul_eq_mul, hphiEdge]
  have hjne : Ne j i := by
    intro hj
    apply _root_.finRotate_ne_self (by omega : 2 <= q) i
    simpa only [hj] using hji
  have hjneNext : Ne j (finRotate q i) := by
    intro hj
    apply finRotate_due_ne hq i
    calc
      finRotate q (finRotate q i) = finRotate q j := by rw [hj]
      _ = i := hji
  have hpointR : Membership.mem (DP.faccetta i) (punto P.asFinite v DP j) := by
    simpa only [hji] using (punto_spec P.asFinite v DP j).2.2
  have hlevelOld : {y | And (Membership.mem (DP.faccetta i) y)
      (phi y = phi v)} =
      Inter.inter (DP.faccetta i) (DP.faccetta (finRotate q i)) :=
    hlevelP.trans hsegP.symm
  have hphir : 0 < phi r := by
    exact funzionale_positivo_su_dir DP i j j phi (DP.mem_v i) hpointR
      (punto_spec P.asFinite v DP j).2.1 hlowerP hlevelOld hjne hjneNext
  have hrot1ne0 : Ne (finRotate q (1 : Fin q)) 0 := by
    intro h
    apply finRotate_due_ne hq (0 : Fin q)
    simpa only [hrot01] using h
  have hrot1ne1 : Ne (finRotate q (1 : Fin q)) 1 :=
    _root_.finRotate_ne_self (by omega : 2 <= q) 1
  have hlevelEP : {y | And (Membership.mem (DP.faccetta i) y)
      (phi y = phi v)} =
      Inter.inter (EP.faccetta 0) (EP.faccetta (finRotate q 0)) :=
    hlevelP.trans hedgeEP.symm
  have hlevelEPw : {y | And (Membership.mem (DP.faccetta i) y)
      (phi y = phi w)} =
      Inter.inter (EP.faccetta 0) (EP.faccetta (finRotate q 0)) := by
    simpa only [hphiEdge.symm] using hlevelEP
  have hpointZ : Membership.mem (DP.faccetta i)
      (punto P.asFinite w EP 1) := by
    simpa only [hEP1] using (punto_spec P.asFinite w EP 1).2.1
  have hphiz : 0 < phi z := by
    exact funzionale_positivo_su_dir EP 0 1 (finRotate q 1) phi
      (by simpa only [hEP1] using EP.mem_v 1) hpointZ
      (punto_spec P.asFinite w EP 1).2.2
      (by simpa only [hEP1, hphiEdge.symm] using hlowerP) hlevelEPw hrot1ne0
      (by simpa only [hrot01] using hrot1ne1)
  have hlevelEQ : {y | And (Membership.mem (DQ.faccetta i) y)
      (phi y = phi v)} =
      Inter.inter (EQ.faccetta 0) (EQ.faccetta (finRotate q 0)) :=
    hlevelQ.trans hedgeEQ.symm
  have hlevelEQw : {y | And (Membership.mem (DQ.faccetta i) y)
      (phi y = phi w)} =
      Inter.inter (EQ.faccetta 0) (EQ.faccetta (finRotate q 0)) := by
    simpa only [hphiEdge.symm] using hlevelEQ
  have hpointZ' : Membership.mem (DQ.faccetta i)
      (punto Q.asFinite w EQ 1) := by
    simpa only [hEQ1] using (punto_spec Q.asFinite w EQ 1).2.1
  have hphiz' : 0 < phi z' := by
    exact funzionale_positivo_su_dir EQ 0 1 (finRotate q 1) phi
      (by simpa only [hEQ1] using EQ.mem_v 1) hpointZ'
      (punto_spec Q.asFinite w EQ 1).2.2
      (by simpa only [hEQ1, hphiEdge.symm] using hlowerQ) hlevelEQw hrot1ne0
      (by simpa only [hrot01] using hrot1ne1)
  have huSpan : Membership.mem (vectorSpan Real (DP.faccetta i)) u := by
    have hmem := dir_mem_vectorSpan_faccetta_destra EP (0 : Fin q)
    simpa only [u, hrot01, hEP1] using hmem
  have hrSpan : Membership.mem (vectorSpan Real (DP.faccetta i)) r := by
    have hmem := dir_mem_vectorSpan_faccetta_destra DP j
    simpa only [r, hji] using hmem
  have hspanP : vectorSpan Real (DP.faccetta i) =
      Submodule.span Real ({u, r} : Set (E 3)) :=
    vectorSpan_eq_span_vettori huSpan hrSpan hind (DP.isFacet i).2
  have hzVec : Membership.mem (vectorSpan Real (DP.faccetta i)) z := by
    have hmem := dir_mem_vectorSpan_faccetta_sinistra EP (1 : Fin q)
    simpa only [z, hEP1] using hmem
  have hzVec' : Membership.mem (vectorSpan Real (DQ.faccetta i)) z' := by
    have hmem := dir_mem_vectorSpan_faccetta_sinistra EQ (1 : Fin q)
    simpa only [z', hEQ1] using hmem
  have hvectorPlane : vectorSpan Real (DP.faccetta i) =
      vectorSpan Real (DQ.faccetta i) := by
    have hdirection := congrArg AffineSubspace.direction hpiano
    simpa only [direction_affineSpan] using hdirection
  have hzSpan : Membership.mem (Submodule.span Real ({u, r} : Set (E 3))) z := by
    rw [hspanP.symm]
    exact hzVec
  have hzSpan' : Membership.mem (Submodule.span Real ({u, r} : Set (E 3))) z' := by
    rw [hspanP.symm, hvectorPlane]
    exact hzVec'
  have hangP := inner_direzioni_consecutive P.asFinite hP hwP EP (0 : Fin q)
  have hangQ := inner_direzioni_consecutive Q.asFinite hQ hwQ EQ (0 : Fin q)
  have hang : inner Real u z = inner Real u z' := by
    calc
      inner Real u z = cosFacciale p := by
        simpa only [u, z, hrot01] using hangP
      _ = inner Real (dir Q.asFinite w EQ 0) z' := by
        simpa only [z', hrot01] using hangQ.symm
      _ = inner Real u z' := by simp only [u, hzero]
  have huno : z = z' := raggio_unico_da_semipiano_lineare
    (dir_unitaria P.asFinite w EP 0)
    (dir_unitaria P.asFinite w EP 1)
    (dir_unitaria Q.asFinite w EQ 1) hind phi hphiu hphir hphiz hphiz'
    hzSpan hzSpan' hang
  have hstesso : forall k, Ne k 0 -> Ne k 1 ->
      0 < volumeTre (dir P.asFinite w EP 0) (dir P.asFinite w EP 1)
            (dir P.asFinite w EP k) *
          volumeTre (dir Q.asFinite w EQ 0) (dir Q.asFinite w EQ 1)
            (dir Q.asFinite w EQ k) := by
    intro k hk0 hk1
    exact orientazione_al_vicino_allineato P Q hP hQ hq hwP hwQ
      DP DQ EP EQ hdir i hEP1 hEQ1 hzero huno k hk0 hk1
  have hfan := fan_geometrico_marcato_unico P Q hP hQ hwP hwQ EP EQ
    hzero huno hstesso
  exact Exists.intro w (Exists.intro hwP (Exists.intro hwQ
    (Exists.intro EP (Exists.intro EQ
      (And.intro hfan (And.intro hwne hsegP))))))


end LeanEval.Geometry.PlatonicClassification
