import DirectGLSSW.MixedEdgeEventCircle
import DirectGLSSW.MixedEdgeFiniteOrder
import DirectGLSSW.EdgeCrossingVisits

set_option autoImplicit false

namespace DirectGLSSW.MixedEdgeSupportOrder
open FiniteCycleOrder PolygonNonalternation
attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] [LinearOrder K] {n : ℕ}

abbrev EdgeChord (q : Fin n → PlanarPoint K) (e : Fin n) :=
  DirectGLSSW.EdgeChord q e

def returnVisitBefore (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (e : Fin n)
    (c d : EdgeChord q e) : Prop := by
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
  exact strictCyclicBetween (Sum.inl (cyclicSuccessor e) : PolygonEvent q)
    (Sum.inr (DirectGLSSW.returnVisit q e c))
    (Sum.inr (DirectGLSSW.returnVisit q e d))

noncomputable def eventOrdinal (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (x : PolygonEvent q) :=
  (eventEnumeration q hq).symm x

private theorem eventOrdinal_cyclicBetween_iff
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (x y z : PolygonEvent q) :
    strictCyclicBetween (eventOrdinal q hq x) (eventOrdinal q hq y)
      (eventOrdinal q hq z) ↔
      (letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq
       strictCyclicBetween x y z) := by
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq
  change strictCyclicBetween ((polygonEventEnumeration q hq).symm x)
      ((polygonEventEnumeration q hq).symm y)
      ((polygonEventEnumeration q hq).symm z) ↔ strictCyclicBetween x y z
  simpa [eventOrdinal, eventEnumeration] using
    (strictCyclicBetween_orderIso (polygonEventEnumeration q hq)
    ((polygonEventEnumeration q hq).symm x)
    ((polygonEventEnumeration q hq).symm y)
    ((polygonEventEnumeration q hq).symm z)).symm

section Ordered
variable [IsStrictOrderedRing K]

private theorem abstractPair_iff_arcOrders
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (hn : 3 ≤ n) (e : Fin n) (c d : EdgeChord q e) (hcd : c ≠ d) :
    (strictCyclicBetween (actualEndpoint q hq (c.val, false))
        (actualEndpoint q hq (d.val, false))
        (actualEndpoint q hq (c.val, true)) ↔
      strictCyclicBetween (actualEndpoint q hq (c.val, false))
        (actualEndpoint q hq (d.val, true))
        (actualEndpoint q hq (c.val, true))) ↔
      (strictCyclicBetween
          (eventOrdinal q hq (Sum.inl e : PolygonEvent q))
          (eventOrdinal q hq (Sum.inr (DirectGLSSW.edgeVisit q e c)))
          (eventOrdinal q hq (Sum.inr (DirectGLSSW.edgeVisit q e d))) ↔
        strictCyclicBetween
          (eventOrdinal q hq (Sum.inl (cyclicSuccessor e) : PolygonEvent q))
          (eventOrdinal q hq (Sum.inr (DirectGLSSW.returnVisit q e d)))
          (eventOrdinal q hq (Sum.inr (DirectGLSSW.returnVisit q e c)))) := by
  classical
  letI : LinearOrder (PolygonEvent q) := by
    change LinearOrder (Fin n ⊕ CrossingVisit q)
    exact polygonEventOrder q hq
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
  let A := eventOrdinal q hq (Sum.inl (cyclicSuccessor e) : PolygonEvent q)
  let B := eventOrdinal q hq (Sum.inl e : PolygonEvent q)
  let rC := eventOrdinal q hq (Sum.inr (DirectGLSSW.returnVisit q e c))
  let rD := eventOrdinal q hq (Sum.inr (DirectGLSSW.returnVisit q e d))
  let sC := eventOrdinal q hq (Sum.inr (DirectGLSSW.edgeVisit q e c))
  let sD := eventOrdinal q hq (Sum.inr (DirectGLSSW.edgeVisit q e d))
  let bc := !(DirectGLSSW.edgeVisitSide q e c)
  let bd := !(DirectGLSSW.edgeVisitSide q e d)
  have hSuccNe : cyclicSuccessor e ≠ e := by
    intro h
    have hval := congrArg Fin.val h
    have hn0 : 0 < n := by omega
    have hs := cyclicVertexIndex_val e (k := 0) hn0
    unfold cyclicSuccessor at hval
    rw [hs] at hval
    simp only [Nat.add_zero] at hval
    by_cases hnext : e.val + 1 < n <;> simp [hnext] at hval <;> omega
  have hAB : A ≠ B := by
    intro h
    apply hSuccNe
    exact Sum.inl.inj ((eventEnumeration q hq).symm.injective h)
  have hrr : rC ≠ rD := by
    intro h
    have he := Sum.inr.inj ((eventEnumeration q hq).symm.injective h)
    exact hcd (DirectGLSSW.returnVisit_injective q e he)
  have hss : sC ≠ sD := by
    intro h
    have he := Sum.inr.inj ((eventEnumeration q hq).symm.injective h)
    exact hcd (DirectGLSSW.edgeVisit_injective q e he)
  have hretCraw :
      letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
      strictCyclicBetween (Sum.inl (cyclicSuccessor e) : PolygonEvent q)
        (Sum.inr (DirectGLSSW.returnVisit q e c)) (Sum.inl e) :=
    crossingVisit_between_successor_anchor_and_edge_anchor q hq e
      (DirectGLSSW.returnVisit q e c)
      (DirectGLSSW.edgeVisitSide_spec q e c).2
  have hretDraw :
      letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
      strictCyclicBetween (Sum.inl (cyclicSuccessor e) : PolygonEvent q)
        (Sum.inr (DirectGLSSW.returnVisit q e d)) (Sum.inl e) :=
    crossingVisit_between_successor_anchor_and_edge_anchor q hq e
      (DirectGLSSW.returnVisit q e d)
      (DirectGLSSW.edgeVisitSide_spec q e d).2
  have hselCraw :
      letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
      strictCyclicBetween (Sum.inl e : PolygonEvent q)
        (Sum.inr (DirectGLSSW.edgeVisit q e c))
        (Sum.inl (cyclicSuccessor e)) :=
    crossingVisit_between_edge_anchor_and_successor_anchor q hq hn e
      (DirectGLSSW.edgeVisit q e c) (DirectGLSSW.edgeVisitSide_spec q e c).1
  have hselDraw :
      letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
      strictCyclicBetween (Sum.inl e : PolygonEvent q)
        (Sum.inr (DirectGLSSW.edgeVisit q e d))
        (Sum.inl (cyclicSuccessor e)) :=
    crossingVisit_between_edge_anchor_and_successor_anchor q hq hn e
      (DirectGLSSW.edgeVisit q e d) (DirectGLSSW.edgeVisitSide_spec q e d).1
  have hrC : strictCyclicBetween A rC B := by
    exact (eventOrdinal_cyclicBetween_iff q hq _ _ _).2 hretCraw
  have hrD : strictCyclicBetween A rD B := by
    exact (eventOrdinal_cyclicBetween_iff q hq _ _ _).2 hretDraw
  have hsC : strictCyclicBetween B sC A := by
    exact (eventOrdinal_cyclicBetween_iff q hq _ _ _).2 hselCraw
  have hsD : strictCyclicBetween B sD A := by
    exact (eventOrdinal_cyclicBetween_iff q hq _ _ _).2 hselDraw
  have hFour := fourEndpoint_nonAlternation_iff_reverseArcOrder
    A B rC rD sC sD hAB hrr hss hrC hrD hsC hsD bc bd
  have hc0 : actualEndpoint q hq (c.val, false) = if bc then sC else rC := by
    dsimp [bc, sC, rC, eventOrdinal, eventEnumeration, actualEndpoint]
    cases hs : DirectGLSSW.edgeVisitSide q e c <;>
      simp [DirectGLSSW.edgeVisit, DirectGLSSW.returnVisit,
        crossingVisitFlip, hs]
  have hc1 : actualEndpoint q hq (c.val, true) = if bc then rC else sC := by
    dsimp [bc, sC, rC, eventOrdinal, eventEnumeration, actualEndpoint]
    cases hs : DirectGLSSW.edgeVisitSide q e c <;>
      simp [DirectGLSSW.edgeVisit, DirectGLSSW.returnVisit,
        crossingVisitFlip, hs]
  have hd0 : actualEndpoint q hq (d.val, false) = if bd then sD else rD := by
    dsimp [bd, sD, rD, eventOrdinal, eventEnumeration, actualEndpoint]
    cases hs : DirectGLSSW.edgeVisitSide q e d <;>
      simp [DirectGLSSW.edgeVisit, DirectGLSSW.returnVisit,
        crossingVisitFlip, hs]
  have hd1 : actualEndpoint q hq (d.val, true) = if bd then rD else sD := by
    dsimp [bd, sD, rD, eventOrdinal, eventEnumeration, actualEndpoint]
    cases hs : DirectGLSSW.edgeVisitSide q e d <;>
      simp [DirectGLSSW.edgeVisit, DirectGLSSW.returnVisit,
        crossingVisitFlip, hs]
  simpa [A, B, rC, rD, sC, sD, hc0, hc1, hd0, hd1] using hFour

/-- Actual nonalternation of selected crossings on a descending horizontal
closing edge is exactly increasing abscissa and complementary return order. -/
theorem polygonNonalternating_iff_returnVisitOrder
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (hn : 3 ≤ n) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (T : Finset (EdgeChord q e)) :
    PolygonNonalternation.polygonNonalternating q hq (T.image Subtype.val) ↔
    ∀ c ∈ T, ∀ d ∈ T, c ≠ d →
        (crossingPoint q c.val).1 < (crossingPoint q d.val).1 →
          returnVisitBefore q hq e c d := by
  classical
  rw [PolygonNonalternation.polygonNonalternating_iff_abstract]
  letI : LinearOrder (PolygonEvent q) := by
    change LinearOrder (Fin n ⊕ CrossingVisit q)
    exact polygonEventOrder q hq
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
  constructor
  · intro h c hc d hd hcd hxd
    have hcdVal : c.val ≠ d.val := by
      intro hv
      exact hcd (Subtype.ext hv)
    have hcMem : c.val ∈ T.image Subtype.val :=
      Finset.mem_image.mpr ⟨c, hc, rfl⟩
    have hdMem : d.val ∈ T.image Subtype.val :=
      Finset.mem_image.mpr ⟨d, hd, rfl⟩
    have hPair := h c.val hcMem d.val hdMem hcdVal
    let A := eventOrdinal q hq (Sum.inl (cyclicSuccessor e) : PolygonEvent q)
    let B := eventOrdinal q hq (Sum.inl e : PolygonEvent q)
    let rC := eventOrdinal q hq
      (Sum.inr (DirectGLSSW.returnVisit q e c))
    let rD := eventOrdinal q hq
      (Sum.inr (DirectGLSSW.returnVisit q e d))
    let sC := eventOrdinal q hq (Sum.inr (DirectGLSSW.edgeVisit q e c))
    let sD := eventOrdinal q hq (Sum.inr (DirectGLSSW.edgeVisit q e d))
    have hArcRCraw := crossingVisit_between_successor_anchor_and_edge_anchor q hq e
      (DirectGLSSW.returnVisit q e c) (DirectGLSSW.edgeVisitSide_spec q e c).2
    have hArcRDraw := crossingVisit_between_successor_anchor_and_edge_anchor q hq e
      (DirectGLSSW.returnVisit q e d) (DirectGLSSW.edgeVisitSide_spec q e d).2
    have hArcRC : strictCyclicBetween A rC B := by
      exact (eventOrdinal_cyclicBetween_iff q hq _ _ _).2 hArcRCraw
    have hArcRD : strictCyclicBetween A rD B := by
      exact (eventOrdinal_cyclicBetween_iff q hq _ _ _).2 hArcRDraw
    have hOrders :
        (strictCyclicBetween B sC sD ↔ strictCyclicBetween A rD rC) :=
      (abstractPair_iff_arcOrders q hq hn e c d hcd).mp hPair
    have hBsc : B < sC := by
      letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
      have hEdge : e ≤ crossingVisitEdge q (DirectGLSSW.edgeVisit q e c) := by
        rw [(DirectGLSSW.edgeVisitSide_spec q e c).1]
      have hev : (Sum.inl e : PolygonEvent q) <
          Sum.inr (DirectGLSSW.edgeVisit q e c) :=
        (anchor_lt_visit_iff q hq e (DirectGLSSW.edgeVisit q e c)).2 hEdge
      simpa [B, sC, eventOrdinal, eventEnumeration] using
        (polygonEventEnumeration q hq).symm.strictMono hev
    have hBsd : B < sD := by
      letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
      have hEdge : e ≤ crossingVisitEdge q (DirectGLSSW.edgeVisit q e d) := by
        rw [(DirectGLSSW.edgeVisitSide_spec q e d).1]
      have hev : (Sum.inl e : PolygonEvent q) <
          Sum.inr (DirectGLSSW.edgeVisit q e d) :=
        (anchor_lt_visit_iff q hq e (DirectGLSSW.edgeVisit q e d)).2 hEdge
      simpa [B, sD, eventOrdinal, eventEnumeration] using
        (polygonEventEnumeration q hq).symm.strictMono hev
    have hS : strictCyclicBetween B sC sD ↔ sC < sD :=
      strictCyclicBetween_lowerAnchor_iff_lt B sC sD hBsc hBsd
    have hEventDC : (Sum.inr (DirectGLSSW.edgeVisit q e d) : PolygonEvent q) <
        Sum.inr (DirectGLSSW.edgeVisit q e c) :=
      ((DirectGLSSW.edgeVisit_order_iff_reverse_abscissa q hq e hflat hleft d c).2 hxd)
    have hSdc : sD < sC := by
      simpa [sC, sD, eventOrdinal, eventEnumeration] using
        (polygonEventEnumeration q hq).symm.strictMono hEventDC
    have hNoS : ¬ strictCyclicBetween B sC sD := by
      intro hs
      exact (lt_asymm (hS.mp hs) hSdc)
    have hA_rC : A ≠ rC := by
      intro heq
      have hx := hArcRC
      rw [← heq] at hx
      simp [strictCyclicBetween] at hx
      omega
    have hA_rD : A ≠ rD := by
      intro heq
      have hx := hArcRD
      rw [← heq] at hx
      simp [strictCyclicBetween] at hx
      omega
    have hRrev : strictCyclicBetween A rD rC ↔
        ¬ strictCyclicBetween A rC rD :=
      strictCyclicBetween_reverse_iff_not A rC rD hA_rC hA_rD
        (by intro heq; exact hcd (DirectGLSSW.returnVisit_injective q e
          (Sum.inr.inj ((eventEnumeration q hq).symm.injective heq))))
    have hNoR : ¬ strictCyclicBetween A rD rC := by
      intro hr
      exact hNoS (hOrders.mpr hr)
    have hReturn : strictCyclicBetween A rC rD := by
      apply not_not.mp
      intro hnot
      exact hNoR (hRrev.mpr hnot)
    have hReturnActual : returnVisitBefore q hq e c d := by
      simpa [returnVisitBefore, A, rC, rD, eventOrdinal, eventEnumeration] using
        (eventOrdinal_cyclicBetween_iff q hq _ _ _).mp hReturn
    exact hReturnActual
  · intro h c0 hc0 d0 hd0 hcd0
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc0
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd0
    have hcd : c ≠ d := by
      intro heq
      exact hcd0 (congrArg Subtype.val heq)
    have hcdVal : c.val ≠ d.val := by
      intro hv
      exact hcd (Subtype.ext hv)
    have hxne : (crossingPoint q c.val).1 ≠ (crossingPoint q d.val).1 := by
      intro hx
      exact hcd (DirectGLSSW.edgeChord_abscissa_injective q hq e hflat c d hx)
    rcases lt_or_gt_of_ne hxne with hxcd | hxdc
    · have hret := h c hc d hd hcd hxcd
      let A := eventOrdinal q hq (Sum.inl (cyclicSuccessor e) : PolygonEvent q)
      let B := eventOrdinal q hq (Sum.inl e : PolygonEvent q)
      let rC := eventOrdinal q hq (Sum.inr (DirectGLSSW.returnVisit q e c))
      let rD := eventOrdinal q hq (Sum.inr (DirectGLSSW.returnVisit q e d))
      let sC := eventOrdinal q hq (Sum.inr (DirectGLSSW.edgeVisit q e c))
      let sD := eventOrdinal q hq (Sum.inr (DirectGLSSW.edgeVisit q e d))
      have hBsc : B < sC := by
        letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
        have hEdge : e ≤ crossingVisitEdge q (DirectGLSSW.edgeVisit q e c) := by
          rw [(DirectGLSSW.edgeVisitSide_spec q e c).1]
        have hev : (Sum.inl e : PolygonEvent q) <
            Sum.inr (DirectGLSSW.edgeVisit q e c) :=
          (anchor_lt_visit_iff q hq e (DirectGLSSW.edgeVisit q e c)).2 hEdge
        simpa [B, sC, eventOrdinal, eventEnumeration] using
          (polygonEventEnumeration q hq).symm.strictMono hev
      have hBsd : B < sD := by
        letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
        have hEdge : e ≤ crossingVisitEdge q (DirectGLSSW.edgeVisit q e d) := by
          rw [(DirectGLSSW.edgeVisitSide_spec q e d).1]
        have hev : (Sum.inl e : PolygonEvent q) <
            Sum.inr (DirectGLSSW.edgeVisit q e d) :=
          (anchor_lt_visit_iff q hq e (DirectGLSSW.edgeVisit q e d)).2 hEdge
        simpa [B, sD, eventOrdinal, eventEnumeration] using
          (polygonEventEnumeration q hq).symm.strictMono hev
      have hS : strictCyclicBetween B sC sD ↔ sC < sD :=
      strictCyclicBetween_lowerAnchor_iff_lt B sC sD hBsc hBsd
      have hEventDC : (Sum.inr (DirectGLSSW.edgeVisit q e d) : PolygonEvent q) <
          Sum.inr (DirectGLSSW.edgeVisit q e c) :=
        ((DirectGLSSW.edgeVisit_order_iff_reverse_abscissa q hq e hflat hleft d c).2 hxcd)
      have hSdc : sD < sC := by
        simpa [sC, sD, eventOrdinal, eventEnumeration] using
          (polygonEventEnumeration q hq).symm.strictMono hEventDC
      have hNoS : ¬ strictCyclicBetween B sC sD := by
        intro hs
        exact (lt_asymm (hS.mp hs) hSdc)
      have hR : strictCyclicBetween A rC rD := by
        simpa [A, rC, rD, returnVisitBefore, eventOrdinal, eventEnumeration] using
          (eventOrdinal_cyclicBetween_iff q hq _ _ _).mpr hret
      have hA_rC : A ≠ rC := by
        intro heq
        have hx := hR
        rw [← heq] at hx
        simp [strictCyclicBetween] at hx
        omega
      have hA_rD : A ≠ rD := by
        intro heq
        have hx := hR
        rw [← heq] at hx
        simp [strictCyclicBetween] at hx
        omega
      have hRrev : strictCyclicBetween A rD rC ↔
          ¬ strictCyclicBetween A rC rD :=
        strictCyclicBetween_reverse_iff_not A rC rD hA_rC hA_rD
          (by intro heq; exact hcd (DirectGLSSW.returnVisit_injective q e
            (Sum.inr.inj ((eventEnumeration q hq).symm.injective heq))))
      have hNoR : ¬ strictCyclicBetween A rD rC := by
        intro hrev
        exact (hRrev.mp hrev) hR
      have hOrders' : strictCyclicBetween B sC sD ↔
          strictCyclicBetween A rD rC := by
        constructor
        · intro hs
          exact False.elim (hNoS hs)
        · intro hr
          exact False.elim (hNoR hr)
      exact (abstractPair_iff_arcOrders q hq hn e c d hcd).mpr hOrders'
    · have hret := h d hd c hc (Ne.symm hcd) hxdc
      let A := eventOrdinal q hq (Sum.inl (cyclicSuccessor e) : PolygonEvent q)
      let B := eventOrdinal q hq (Sum.inl e : PolygonEvent q)
      let rC := eventOrdinal q hq (Sum.inr (DirectGLSSW.returnVisit q e c))
      let rD := eventOrdinal q hq (Sum.inr (DirectGLSSW.returnVisit q e d))
      let sC := eventOrdinal q hq (Sum.inr (DirectGLSSW.edgeVisit q e c))
      let sD := eventOrdinal q hq (Sum.inr (DirectGLSSW.edgeVisit q e d))
      have hBsc : B < sC := by
        letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
        have hEdge : e ≤ crossingVisitEdge q (DirectGLSSW.edgeVisit q e c) := by
          rw [(DirectGLSSW.edgeVisitSide_spec q e c).1]
        have hev : (Sum.inl e : PolygonEvent q) <
            Sum.inr (DirectGLSSW.edgeVisit q e c) :=
          (anchor_lt_visit_iff q hq e (DirectGLSSW.edgeVisit q e c)).2 hEdge
        simpa [B, sC, eventOrdinal, eventEnumeration] using
          (polygonEventEnumeration q hq).symm.strictMono hev
      have hBsd : B < sD := by
        letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
        have hEdge : e ≤ crossingVisitEdge q (DirectGLSSW.edgeVisit q e d) := by
          rw [(DirectGLSSW.edgeVisitSide_spec q e d).1]
        have hev : (Sum.inl e : PolygonEvent q) <
            Sum.inr (DirectGLSSW.edgeVisit q e d) :=
          (anchor_lt_visit_iff q hq e (DirectGLSSW.edgeVisit q e d)).2 hEdge
        simpa [B, sD, eventOrdinal, eventEnumeration] using
          (polygonEventEnumeration q hq).symm.strictMono hev
      have hS : strictCyclicBetween B sC sD ↔ sC < sD :=
        strictCyclicBetween_lowerAnchor_iff_lt B sC sD hBsc hBsd
      have hEventCD : (Sum.inr (DirectGLSSW.edgeVisit q e c) : PolygonEvent q) <
          Sum.inr (DirectGLSSW.edgeVisit q e d) :=
        ((DirectGLSSW.edgeVisit_order_iff_reverse_abscissa q hq e hflat hleft c d).2 hxdc)
      have hScd : sC < sD := by
        simpa [sC, sD, eventOrdinal, eventEnumeration] using
          (polygonEventEnumeration q hq).symm.strictMono hEventCD
      have hStrue : strictCyclicBetween B sC sD := hS.mpr hScd
      have hA_rC : A ≠ rC := by
        intro heq
        have hR : strictCyclicBetween A rD rC := by
          simpa [A, rC, rD, returnVisitBefore, eventOrdinal, eventEnumeration] using
            (eventOrdinal_cyclicBetween_iff q hq _ _ _).mpr hret
        have hx := hR
        rw [← heq] at hx
        simp [strictCyclicBetween] at hx
        exact lt_asymm hx.1 hx.2
      have hA_rD : A ≠ rD := by
        intro heq
        have hR : strictCyclicBetween A rD rC := by
          simpa [A, rC, rD, returnVisitBefore, eventOrdinal, eventEnumeration] using
            (eventOrdinal_cyclicBetween_iff q hq _ _ _).mpr hret
        have hx := hR
        rw [← heq] at hx
        simp [strictCyclicBetween] at hx
        exact lt_asymm hx.1 hx.2
      have hRrev : strictCyclicBetween A rD rC ↔
          ¬ strictCyclicBetween A rC rD :=
        strictCyclicBetween_reverse_iff_not A rC rD hA_rC hA_rD
          (by intro heq; exact hcd (DirectGLSSW.returnVisit_injective q e
            (Sum.inr.inj ((eventEnumeration q hq).symm.injective heq))))
      have hRtrue : strictCyclicBetween A rD rC := by
        simpa [A, rC, rD, returnVisitBefore, eventOrdinal, eventEnumeration] using
          (eventOrdinal_cyclicBetween_iff q hq _ _ _).mpr hret
      have hOrders : strictCyclicBetween B sC sD ↔
          strictCyclicBetween A rD rC := Iff.intro (fun _ => hRtrue) (fun _ => hStrue)
      exact (abstractPair_iff_arcOrders q hq hn e c d hcd).mpr hOrders

noncomputable def EdgeSeparatingSupport (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) := by
  classical
  exact {T : Finset (EdgeChord q e) // T.Nonempty ∧
    PolygonNonalternation.polygonNonalternating q hq (T.image Subtype.val)}

def ValidEdgeChain (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) :=
  {L : List (EdgeChord q e) // L ≠ [] ∧ L.Nodup ∧
    List.Pairwise (fun c d =>
      (crossingPoint q c.val).1 < (crossingPoint q d.val).1 ∧
      returnVisitBefore q hq e c d) L}

private def edgeCrossingAbscissaLE (q : Fin n → PlanarPoint K) (e : Fin n)
    (c d : EdgeChord q e) : Prop :=
  (crossingPoint q c.val).1 ≤ (crossingPoint q d.val).1

private theorem edgeCrossingAbscissaLE_trans
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (e : Fin n) (hflat : (q e).2 = (q (cyclicSuccessor e)).2) :
    IsTrans (EdgeChord q e) (edgeCrossingAbscissaLE q e) := by
  exact ⟨fun a b c hab hbc => le_trans hab hbc⟩

private theorem edgeCrossingAbscissaLE_antisymm
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (e : Fin n) (hflat : (q e).2 = (q (cyclicSuccessor e)).2) :
    IsAntisymm (EdgeChord q e) (edgeCrossingAbscissaLE q e) := by
  exact ⟨fun a b hab hba =>
    DirectGLSSW.edgeChord_abscissa_injective q hq e hflat a b
      (le_antisymm hab hba)⟩

private theorem edgeCrossingAbscissaLE_total
    (q : Fin n → PlanarPoint K) (e : Fin n) :
    IsTotal (EdgeChord q e) (edgeCrossingAbscissaLE q e) := by
  exact ⟨fun a b => le_total _ _⟩

noncomputable def edgeSupportOrderEquiv
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (hn : 3 ≤ n) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) :
    EdgeSeparatingSupport q hq e hflat hleft ≃
      ValidEdgeChain q hq e hflat hleft := by
  classical
  let r := edgeCrossingAbscissaLE q e
  letI : IsTrans (EdgeChord q e) r := edgeCrossingAbscissaLE_trans q hq e hflat
  letI : IsAntisymm (EdgeChord q e) r :=
    edgeCrossingAbscissaLE_antisymm q hq e hflat
  letI : IsTotal (EdgeChord q e) r := edgeCrossingAbscissaLE_total q e
  letI : DecidableRel r := Classical.decRel r
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro S
    let T := S.val
    let L := T.sort r
    have hnonalt :=
      (polygonNonalternating_iff_returnVisitOrder q hq hn e hflat hleft T).mp
        S.property.2
    have hSortR : List.Pairwise r L := Finset.sort_sorted r T
    have hNodup : L.Nodup := by
      change (T.sort r).Nodup
      exact Finset.sort_nodup r T
    have hCoordSorted : List.Sorted (· ≤ ·)
        (L.map fun c => (crossingPoint q c.val).1) := by
      apply List.pairwise_map.mpr
      simpa [L, r, edgeCrossingAbscissaLE] using hSortR
    have hCoordNodup : (L.map fun c => (crossingPoint q c.val).1).Nodup :=
      hNodup.map (by
        intro c d hxy
        exact DirectGLSSW.edgeChord_abscissa_injective q hq e hflat c d hxy)
    have hStrict : List.Pairwise
        (fun c d => (crossingPoint q c.val).1 < (crossingPoint q d.val).1) L := by
      exact (List.pairwise_map).mp (hCoordSorted.lt_of_le hCoordNodup)
    have hMem : ∀ c ∈ L, c ∈ T := by
      intro c hc
      exact (Finset.mem_sort r).mp hc
    have hBoth : List.Pairwise
        (fun c d => (crossingPoint q c.val).1 < (crossingPoint q d.val).1 ∧
          returnVisitBefore q hq e c d) L := by
      exact List.Pairwise.imp_of_mem
        (l := L) (by
          intro c d hc hd hcdx
          exact ⟨hcdx, hnonalt c (hMem c hc) d (hMem d hd)
            (by intro heq; subst d; exact (lt_irrefl _ hcdx)) hcdx⟩)
        hStrict
    have hLne : L ≠ [] := by
      intro hempty
      have hcard : 0 < T.card := Finset.card_pos.mpr S.property.1
      have hlen := Finset.length_sort (r := r) (s := T)
      change T.sort r = [] at hempty
      rw [hempty] at hlen
      simp at hlen
      omega
    exact ⟨L, hLne, hNodup, hBoth⟩
  · intro C
    let L := C.val
    let T := L.toFinset
    have hTne : T.Nonempty := by
      cases hL : L with
      | nil => exact False.elim (C.property.1 hL)
      | cons a l => exact ⟨a, by simp [T, hL]⟩
    have hReturn : ∀ c ∈ T, ∀ d ∈ T, c ≠ d →
        (crossingPoint q c.val).1 < (crossingPoint q d.val).1 →
          returnVisitBefore q hq e c d := by
      intro c hc d hd hcd hxd
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hc)
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hd)
      have hpair := List.pairwise_iff_get.mp C.property.2.2
      have hij : i < j := by
        by_cases hEq : i = j
        · subst j
          have hcd' : c = d := by rw [← hi, ← hj]
          exact False.elim (hcd hcd')
        · rcases lt_or_gt_of_ne hEq with hij | hji
          · exact hij
          · have hback := hpair j i hji
            rw [hj, hi] at hback
            exact False.elim (lt_asymm hback.1 hxd)
      have hret := (hpair i j hij).2
      rw [hi, hj] at hret
      exact hret
    have hnonalt :=
      (polygonNonalternating_iff_returnVisitOrder q hq hn e hflat hleft T).mpr
        hReturn
    exact ⟨T, hTne, hnonalt⟩
  · intro S
    apply Subtype.ext
    exact Finset.sort_toFinset r S.val
  · intro C
    apply Subtype.ext
    change Finset.sort r C.val.toFinset = C.val
    apply (List.toFinset_sort r C.property.2.1).2
    exact List.Pairwise.imp
      (R := fun c d => (crossingPoint q c.val).1 < (crossingPoint q d.val).1 ∧
        returnVisitBefore q hq e c d)
      (S := r)
      (by intro c d hlt; exact le_of_lt hlt.1)
      C.property.2.2

@[simp] theorem edgeSupportOrderEquiv_length
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (hn : 3 ≤ n) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (S : EdgeSeparatingSupport q hq e hflat hleft) :
    (edgeSupportOrderEquiv q hq hn e hflat hleft S).val.length = S.val.card := by
  classical
  simp [edgeSupportOrderEquiv, Finset.length_sort]

end Ordered
end DirectGLSSW.MixedEdgeSupportOrder
