import InteriorEdgeEvents

set_option autoImplicit false

namespace DirectGLSSW.MixedEventOrder
open OrderedCapEvents MixedEdgeSupportOrder MixedConsecutiveCapWord
open ExtendedReturnArcGeometry

/-- On a chosen edge, different return visits are on different edges.
Consequently the parameter coordinate never changes their relative rank order. -/
theorem returnVisitBefore_iff_rank_lt
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}
    (q : Fin n → PlanarPoint K) (hq : CyclicGeneric q) (e : Fin n)
    (c d : DirectGLSSW.EdgeChord q e) :
    returnVisitBefore q hq.g2 e c d ↔
      complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e c)) <
      complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e d)) := by
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
  change FiniteCycleOrder.strictCyclicBetween (Sum.inl (cyclicSuccessor e) : PolygonEvent q)
      (Sum.inr (DirectGLSSW.returnVisit q e c)) (Sum.inr (DirectGLSSW.returnVisit q e d)) ↔ _
  rw [crossingVisit_arcOrder_iff_complementaryKey_lt q hq.g2 e _ _
    (DirectGLSSW.edgeVisitSide_spec q e c).2 (DirectGLSSW.edgeVisitSide_spec q e d).2]
  change toLex (_, _) < toLex (_, _) ↔ _
  rw [Prod.Lex.toLex_lt_toLex]
  constructor
  · rintro (hlt | ⟨heq,hpar⟩)
    · exact hlt
    · have hedge := complementaryEventRank_injective e heq
      have hcd := returnVisitEdge_injective q e hedge
      subst d
      exact (lt_irrefl _ hpar).elim
  · exact Or.inl

theorem event_lt_iff_abscissa_lt
    {n m : ℕ} (q : Fin n → PlanarPoint ℝ) (e : Fin n)
    (Q : ℕ → PlanarPoint ℝ) (F : DirectGLSSW.EdgeChord q e → EventIndex Q m)
    (offset : ℝ) (htime : ∀ z, eventTime Q m (F z) = (crossingPoint q z.val).1-offset)
    (c d : DirectGLSSW.EdgeChord q e) :
    F c < F d ↔ (crossingPoint q c.val).1 < (crossingPoint q d.val).1 := by
  rw [← (eventTime_strictMono Q m).lt_iff_lt, htime c, htime d]
  exact sub_lt_sub_iff_right offset

theorem event_pair_order_iff_returnVisitBefore
    {n m : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (Q : ℕ → PlanarPoint ℝ) (F : DirectGLSSW.EdgeChord q e → EventIndex Q m)
    (hpairs : ∀ z, eventPair Q m (F z) =
      (complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))+1,
       complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))+2))
    (c d : DirectGLSSW.EdgeChord q e) :
    (eventPair Q m (F c)).1 < (eventPair Q m (F d)).1 ↔ returnVisitBefore q hq.g2 e c d := by
  rw [hpairs c,hpairs d,returnVisitBefore_iff_rank_lt q hq e c d]
  simp only [Nat.add_lt_add_iff_right]

theorem mapped_event_list_pairwise_iff
    {n m : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (Q : ℕ → PlanarPoint ℝ) (F : DirectGLSSW.EdgeChord q e → EventIndex Q m)
    (offset : ℝ) (htime : ∀ z, eventTime Q m (F z) = (crossingPoint q z.val).1-offset)
    (hpairs : ∀ z, eventPair Q m (F z) =
      (complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))+1,
       complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))+2))
    (L : List (DirectGLSSW.EdgeChord q e)) :
    (L.map F).Pairwise (fun c d => c < d ∧ (eventPair Q m c).1 < (eventPair Q m d).1) ↔
      L.Pairwise (fun c d => (crossingPoint q c.val).1 < (crossingPoint q d.val).1 ∧
        returnVisitBefore q hq.g2 e c d) := by
  simp only [List.pairwise_map, event_lt_iff_abscissa_lt q e Q F offset htime,
    event_pair_order_iff_returnVisitBefore q hq e Q F hpairs]





end DirectGLSSW.MixedEventOrder
