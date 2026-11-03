import DirectGLSSW.DaughterFirstReturn

set_option autoImplicit false

namespace DirectGLSSW.DaughterTurns

open DirectGLSSW
open DirectGLSSW.DaughterFirstReturn
open DirectGLSSW.EventSegmentGeometry

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : ℕ} (q : Fin n → PlanarPoint K)
variable (hG2 : cyclicNoTripleIntersections q)
variable (S : Finset (PolygonCrossing q))

 theorem daughterGapCarrierInvariant (hn : 3 ≤ n)
    (root : PolygonEvent q) (hroot : retainedCorner q S root)
    (c : CornerCoord q hG2 S root) :
    polygonEventEdge q (orbitEventAt q hG2 S root c.val) =
      polygonEventEdge q (lastDartStart q hG2 S root c) := by
  let d := cornerGap q hG2 S root c.val
    (cornerSuccessor q hG2 S root c).val
  have hfr := cornerSuccessor_is_firstReturn q hG2 S hn root hroot c
  rcases hfr with ⟨hd, _, _, _, _, _⟩
  have hlast : d - 1 < d := Nat.sub_lt (by omega) (by omega)
  have hpref := orbitPrefix_edge_parameter q hG2 S hn root hroot c (d - 1) hlast
  simpa [d, lastDartStart] using hpref.1.symm

 theorem daughterTurn_anchor_incomingCarrier (hn : 3 ≤ n)
    (root : PolygonEvent q) (hroot : retainedCorner q S root)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root))) (e : Fin n)
    (hhere : orbitEventAt q hG2 S root
      (cornerEnumeration q hG2 S root i).val = Sum.inl e) :
    polygonEventEdge q
      (orbitEventAt q hG2 S root
        (cornerEnumeration q hG2 S root
          ((cyclicSuccessorPerm (Fintype.card (CornerCoord q hG2 S root)))⁻¹ i)).val) =
      (cyclicSuccessorPerm n)⁻¹ e := by
  classical
  let m := Fintype.card (CornerCoord q hG2 S root)
  let prev := (cyclicSuccessorPerm m)⁻¹ i
  let cprev : CornerCoord q hG2 S root := cornerEnumeration q hG2 S root prev
  have hcyc : cyclicSuccessor prev = i := by
    change cyclicSuccessor ((cyclicSuccessorPerm m)⁻¹ i) = i
    change cyclicSuccessorPerm m ((cyclicSuccessorPerm m)⁻¹ i) = i
    exact Equiv.apply_symm_apply (cyclicSuccessorPerm m) i
  have hcornerNext : cornerSuccessor q hG2 S root cprev =
      cornerEnumeration q hG2 S root i := by
    rw [← cornerEnumeration_successor q hG2 S root prev]
    exact congrArg (cornerEnumeration q hG2 S root) hcyc
  have hfr := cornerSuccessor_is_firstReturn q hG2 S hn root hroot cprev
  rcases hfr with ⟨_, hnext, hpair, _, _, _⟩
  have hterminal : terminalEvent q hG2 (lastDartStart q hG2 S root cprev) = .inl e := by
    have hnext' : nextDartStart q hG2 S (lastDartStart q hG2 S root cprev) = .inl e := by
      calc
        nextDartStart q hG2 S (lastDartStart q hG2 S root cprev) =
            orbitEventAt q hG2 S root (cornerSuccessor q hG2 S root cprev).val := hnext
        _ = .inl e := by rw [hcornerNext]; exact hhere
    apply (smoothingPairing q S).injective
    calc
      smoothingPairing q S (terminalEvent q hG2 (lastDartStart q hG2 S root cprev)) =
          nextDartStart q hG2 S (lastDartStart q hG2 S root cprev) := hpair.symm
      _ = .inl e := hnext'
      _ = smoothingPairing q S (.inl e) := by simp [smoothingPairing, smoothingPairingMap]
  have hclass := polygonEventSuccessor_sameEdge_next_or_nextAnchor q hG2 hn
    (lastDartStart q hG2 S root cprev)
  have hpred : (cyclicSuccessorPerm n)⁻¹ e =
      polygonEventEdge q (lastDartStart q hG2 S root cprev) := by
    rcases hclass with hsame | hnext
    · exfalso
      have hparam := hsame.2.1
      change polygonEventParameter q (lastDartStart q hG2 S root cprev) <
        polygonEventParameter q
          (terminalEvent q hG2 (lastDartStart q hG2 S root cprev)) at hparam
      rw [hterminal] at hparam
      cases hlast : lastDartStart q hG2 S root cprev with
      | inl a =>
          rw [hlast] at hparam
          simp [polygonEventParameter] at hparam
      | inr w =>
          rw [hlast] at hparam
          simp only [polygonEventParameter] at hparam
          exact (not_lt_of_ge (le_of_lt (crossingVisitParameter_spec q w).1)) hparam
    ·
      have heq : e = cyclicSuccessor (polygonEventEdge q
          (lastDartStart q hG2 S root cprev)) := by
        have hnextEq := hnext.1
        change terminalEvent q hG2 (lastDartStart q hG2 S root cprev) = _ at hnextEq
        rw [hterminal] at hnextEq
        exact Sum.inl.inj hnextEq
      rw [heq]
      change (cyclicSuccessorPerm n)⁻¹
          (cyclicSuccessorPerm n (polygonEventEdge q
            (lastDartStart q hG2 S root cprev))) = _
      exact Equiv.symm_apply_apply (cyclicSuccessorPerm n) _
  rw [daughterGapCarrierInvariant q hG2 S hn root hroot cprev]
  exact hpred.symm

 theorem daughterTurn_selectedVisit_incomingCarrier (hn : 3 ≤ n)
    (root : PolygonEvent q) (hroot : retainedCorner q S root)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root))) (v : CrossingVisit q)
    (hhere : orbitEventAt q hG2 S root
      (cornerEnumeration q hG2 S root i).val = Sum.inr v)
    (hv : v.1 ∈ S) :
    polygonEventEdge q
      (orbitEventAt q hG2 S root
        (cornerEnumeration q hG2 S root
          ((cyclicSuccessorPerm (Fintype.card (CornerCoord q hG2 S root)))⁻¹ i)).val) =
      polygonEventEdge q (smoothingPairing q S (Sum.inr v)) := by
  classical
  let m := Fintype.card (CornerCoord q hG2 S root)
  let prev := (cyclicSuccessorPerm m)⁻¹ i
  let cprev : CornerCoord q hG2 S root := cornerEnumeration q hG2 S root prev
  have hcyc : cyclicSuccessor prev = i := by
    change cyclicSuccessor ((cyclicSuccessorPerm m)⁻¹ i) = i
    change cyclicSuccessorPerm m ((cyclicSuccessorPerm m)⁻¹ i) = i
    exact Equiv.apply_symm_apply (cyclicSuccessorPerm m) i
  have hcornerNext : cornerSuccessor q hG2 S root cprev =
      cornerEnumeration q hG2 S root i := by
    rw [← cornerEnumeration_successor q hG2 S root prev]
    exact congrArg (cornerEnumeration q hG2 S root) hcyc
  have hfr := cornerSuccessor_is_firstReturn q hG2 S hn root hroot cprev
  rcases hfr with ⟨_, hnext, hpair, _, _, _⟩
  have hterminal : terminalEvent q hG2 (lastDartStart q hG2 S root cprev) =
      smoothingPairing q S (Sum.inr v) := by
    have hnext' : nextDartStart q hG2 S (lastDartStart q hG2 S root cprev) = .inr v := by
      calc
        nextDartStart q hG2 S (lastDartStart q hG2 S root cprev) =
            orbitEventAt q hG2 S root (cornerSuccessor q hG2 S root cprev).val := hnext
        _ = .inr v := by rw [hcornerNext]; exact hhere
    have hpaired := congrArg (smoothingPairing q S) hnext'
    calc
      terminalEvent q hG2 (lastDartStart q hG2 S root cprev) =
          smoothingPairing q S
            (smoothingPairing q S (terminalEvent q hG2 (lastDartStart q hG2 S root cprev))) := by
              simpa [smoothingPairing_apply] using
                (smoothingPairingMap_involutive q S
                  (terminalEvent q hG2 (lastDartStart q hG2 S root cprev))).symm
      _ = smoothingPairing q S
            (nextDartStart q hG2 S (lastDartStart q hG2 S root cprev)) := by rw [hpair]
      _ = smoothingPairing q S (.inr v) := hpaired
  have hclass := polygonEventSuccessor_sameEdge_next_or_nextAnchor q hG2 hn
    (lastDartStart q hG2 S root cprev)
  have hsame : polygonEventEdge q
      (terminalEvent q hG2 (lastDartStart q hG2 S root cprev)) =
      polygonEventEdge q (lastDartStart q hG2 S root cprev) := by
    rcases hclass with hsame | hnext
    · exact hsame.1
    ·
      have hnextEq := hnext.1
      change terminalEvent q hG2 (lastDartStart q hG2 S root cprev) = _ at hnextEq
      rw [hterminal] at hnextEq
      cases v with
      | mk c b => cases b <;>
          simp [smoothingPairing, smoothingPairingMap, hv, crossingVisitFlip] at hnextEq
  rw [daughterGapCarrierInvariant q hG2 S hn root hroot cprev, ← hterminal]
  exact hsame.symm

theorem planarDet_positive_smul_ne_zero {u w : PlanarPoint K} {a b : K}
    (ha : 0 < a) (hb : 0 < b) (hdet : planarDet u w ≠ 0) :
    planarDet (a • u) (b • w) ≠ 0 := by
  have hformula : planarDet (a • u) (b • w) = (a * b) * planarDet u w := by
    simp [planarDet, smul_eq_mul]
    ring
  intro hz
  rw [hformula] at hz
  rcases mul_eq_zero.mp hz with hab | hzdet
  · exact (mul_ne_zero (ne_of_gt ha) (ne_of_gt hb)) hab
  · exact hdet hzdet

theorem daughterTurn_ne_zero (hn : 3 ≤ n) (hG1 : cyclicNoncollinear q)
    (root : PolygonEvent q) (hroot : retainedCorner q S root) :
    ∀ i : Fin (Fintype.card (CornerCoord q hG2 S root)),
      planarDet
        (daughterSideVector q hG2 S root
          ((cyclicSuccessorPerm (Fintype.card (CornerCoord q hG2 S root)))⁻¹ i))
        (daughterSideVector q hG2 S root i) ≠ 0 := by
  classical
  intro i
  let m := Fintype.card (CornerCoord q hG2 S root)
  let prev := (cyclicSuccessorPerm m)⁻¹ i
  let here := orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root i).val
  let before := orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root prev).val
  have hscalePrev := daughterSide_positive_multiple q hG2 S hn root hroot prev
  have hscaleHere := daughterSide_positive_multiple q hG2 S hn root hroot i
  have hbase : planarDet
      (cyclicTangent q (polygonEventEdge q before))
      (cyclicTangent q (polygonEventEdge q here)) ≠ 0 := by
    cases he : here with
    | inl e =>
        have hin := daughterTurn_anchor_incomingCarrier q hG2 S hn root hroot i e he
        have hsucc : cyclicSuccessor ((cyclicSuccessorPerm n)⁻¹ e) = e := by
          change cyclicSuccessorPerm n ((cyclicSuccessorPerm n)⁻¹ e) = e
          exact Equiv.apply_symm_apply (cyclicSuccessorPerm n) e
        have hturn := cyclic_turn_det_ne_zero hn q hG1
          ((cyclicSuccessorPerm n)⁻¹ e)
        dsimp [before]
        change planarDet
          (cyclicTangent q (polygonEventEdge q
            (orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root prev).val)))
          (cyclicTangent q (polygonEventEdge q (.inl e))) ≠ 0
        rw [hin]
        have hturn' : planarDet
            (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ e))
            (cyclicTangent q e) ≠ 0 := by
          simpa only [hsucc] using hturn
        exact hturn'
    | inr v =>
        have hv : v.1 ∈ S := by
          have hc := (cornerEnumeration q hG2 S root i).property
          simpa [here, he, retainedCorner] using hc
        have hin := daughterTurn_selectedVisit_incomingCarrier q hG2 S hn root hroot i v he hv
        cases v with
        | mk c b =>
            cases b with
            | false =>
                have hcross := crossing_transverse hn q hG1 c
                have hrev : planarDet (cyclicTangent q c.val.2)
                    (cyclicTangent q c.val.1) ≠ 0 := by
                  intro hz
                  have h := congrArg Neg.neg hz
                  rw [planarDet_swap] at h
                  apply hcross
                  simpa using h
                dsimp [before]
                change planarDet
                  (cyclicTangent q (polygonEventEdge q
                    (orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root prev).val)))
                  (cyclicTangent q (crossingVisitEdge q (c, false))) ≠ 0
                rw [hin]
                simpa [crossingVisitEdge, smoothingPairing, smoothingPairingMap,
                  crossingVisitFlip, hv] using hrev
            | true =>
                have hcross := crossing_transverse hn q hG1 c
                dsimp [before]
                change planarDet
                  (cyclicTangent q (polygonEventEdge q
                    (orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root prev).val)))
                  (cyclicTangent q (crossingVisitEdge q (c, true))) ≠ 0
                rw [hin]
                simpa [crossingVisitEdge, smoothingPairing, smoothingPairingMap,
                  crossingVisitFlip, hv] using hcross
  rcases hscalePrev with ⟨hposPrev, hsidePrev⟩
  rcases hscaleHere with ⟨hposHere, hsideHere⟩
  rw [hsidePrev, hsideHere]
  exact planarDet_positive_smul_ne_zero hposPrev hposHere hbase

 theorem daughterVertexCount_ge_three (hn : 3 ≤ n) (hG1 : cyclicNoncollinear q)
    (root : PolygonEvent q) (hroot : retainedCorner q S root) :
    3 ≤ Fintype.card (CornerCoord q hG2 S root) := by
  classical
  have hnonempty : Nonempty (CornerCoord q hG2 S root) := by
    refine ⟨⟨⟨0, orbitCard_pos q hG2 S root⟩, ?_⟩⟩
    simpa [orbitEventAt] using hroot
  have hmpos : 0 < Fintype.card (CornerCoord q hG2 S root) :=
    Fintype.card_pos_iff.mpr hnonempty
  have hturn := daughterTurn_ne_zero q hG2 S hn hG1 root hroot
  by_contra hnot
  have hm : Fintype.card (CornerCoord q hG2 S root) = 1 ∨
      Fintype.card (CornerCoord q hG2 S root) = 2 := by omega
  rcases hm with hm | hm
  · let i : Fin (Fintype.card (CornerCoord q hG2 S root)) := ⟨0, by omega⟩
    have hsub : Subsingleton (Fin (Fintype.card (CornerCoord q hG2 S root))) := by
      rw [hm]
      infer_instance
    have hprev : (cyclicSuccessorPerm (Fintype.card (CornerCoord q hG2 S root)))⁻¹ i = i :=
      hsub.elim _ _
    have hz := hturn i
    have hzero : planarDet (daughterSideVector q hG2 S root i)
        (daughterSideVector q hG2 S root i) = 0 := by
      simp [planarDet]
      ring
    exact hz (by simpa [hprev] using hzero)
  · let i : Fin (Fintype.card (CornerCoord q hG2 S root)) := ⟨0, by omega⟩
    let j : Fin (Fintype.card (CornerCoord q hG2 S root)) := ⟨1, by omega⟩
    have hprev : (cyclicSuccessorPerm (Fintype.card (CornerCoord q hG2 S root)))⁻¹ i = j := by
      apply (cyclicSuccessorPerm (Fintype.card (CornerCoord q hG2 S root))).injective
      calc
        cyclicSuccessorPerm (Fintype.card (CornerCoord q hG2 S root))
            ((cyclicSuccessorPerm (Fintype.card (CornerCoord q hG2 S root)))⁻¹ i) = i :=
          Equiv.apply_symm_apply _ _
        _ = cyclicSuccessorPerm (Fintype.card (CornerCoord q hG2 S root)) j := by
          symm
          apply Fin.ext
          change (cyclicSuccessor j).val = i.val
          rw [cyclicSuccessor]
          simp [cyclicVertexIndex, i, j, hm]
    have hz := hturn i
    have hsuccI : cyclicSuccessor i = j := by
      apply Fin.ext
      rw [cyclicSuccessor]
      simp [cyclicVertexIndex, i, j, hm]
    have hsuccJ : cyclicSuccessor j = i := by
      apply Fin.ext
      rw [cyclicSuccessor]
      simp [cyclicVertexIndex, i, j, hm]
    have hzero : planarDet (daughterSideVector q hG2 S root j)
        (daughterSideVector q hG2 S root i) = 0 := by
      change planarDet
        (daughterVertex q hG2 S root (cyclicSuccessor j) - daughterVertex q hG2 S root j)
        (daughterVertex q hG2 S root (cyclicSuccessor i) - daughterVertex q hG2 S root i) = 0
      rw [hsuccJ, hsuccI]
      simp [planarDet]
      ring
    apply hz
    rw [hprev]
    exact hzero

end DirectGLSSW.DaughterTurns
