import DirectGLSSW.MixedConsecutiveCapWord

set_option autoImplicit false

namespace DirectGLSSW.CellAnchorRanks
open DirectGLSSW MixedConsecutiveCapWord MixedEdgeSupportOrder FiniteCycleOrder

variable {K : Type*} [Field K] [LinearOrder K] {n : ℕ}

/-- Transfer the actual circular relation through the public event order isomorphism.
This explicitly reproves the small ordinal wrapper needed outside the staged module. -/
theorem ordinal_between_iff (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (x y z : PolygonEvent q) :
    strictCyclicBetween (eventOrdinal q hq x) (eventOrdinal q hq y) (eventOrdinal q hq z) ↔
      (letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq
       strictCyclicBetween x y z) := by
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq
  change strictCyclicBetween ((polygonEventEnumeration q hq).symm x)
    ((polygonEventEnumeration q hq).symm y) ((polygonEventEnumeration q hq).symm z) ↔ _
  exact strictCyclicBetween_orderIso (polygonEventEnumeration q hq).symm x y z

/-- The actual filter imposes only its circular predicate: the base ofFn list
contains every anchor by the public cyclic-vertex bijection. -/
theorem cellInteriorAnchors_mem_iff (q : Fin n → PlanarPoint K)
    (hq : CyclicGeneric q) (e : Fin n) (L : List (DirectGLSSW.EdgeChord q e))
    (i : Fin (L.length+1)) (a : Fin n) :
    a ∈ cellInteriorAnchors q hq e L i ↔
      strictCyclicBetween (eventOrdinal q hq.g2 (cellLeftEvent q e L i))
        (eventOrdinal q hq.g2 (Sum.inl a : PolygonEvent q))
        (eventOrdinal q hq.g2 (cellRightEvent q e L i)) := by
  classical
  have hbase : a ∈ List.ofFn (fun j : Fin n => cyclicVertexIndex e j.val) :=
    List.mem_ofFn.mpr ((cyclicVertexIndex_bijective e).surjective a)
  simp only [cellInteriorAnchors, List.mem_filter, decide_eq_true_eq]
  exact and_iff_right hbase

variable [IsStrictOrderedRing K]

/-- Internal cell anchors occupy the exact complementary-edge rank interval
(leftReturnRank,rightReturnRank]. The right return edge's anchor is included
because a crossing visit has strictly positive parameter on its edge. -/
theorem cellInteriorAnchors_internal_iff_rank (q : Fin n → PlanarPoint K)
    (hq : CyclicGeneric q) (e : Fin n) (L : List (DirectGLSSW.EdgeChord q e))
    (hL : OrderedEdgeSupport q hq e L) (i : Fin (L.length+1))
    (hi0 : 0 < i.val) (hiL : i.val < L.length) (a : Fin n) :
    a ∈ cellInteriorAnchors q hq e L i ↔
      complementaryEventRank e (crossingVisitEdge q
        (DirectGLSSW.returnVisit q e (L.get ⟨i.val-1, by omega⟩))) < complementaryEventRank e a ∧
      complementaryEventRank e a ≤ complementaryEventRank e (crossingVisitEdge q
        (DirectGLSSW.returnVisit q e (L.get ⟨i.val, hiL⟩))) := by
  classical
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq.g2
  let j : Fin L.length := ⟨i.val-1, by omega⟩
  let k : Fin L.length := ⟨i.val, hiL⟩
  let v := DirectGLSSW.returnVisit q e (L.get j)
  let w := DirectGLSSW.returnVisit q e (L.get k)
  have hleft : cellLeftEvent q e L i = Sum.inr v := by
    simp [cellLeftEvent, ne_of_gt hi0, v, j]
  have hright : cellRightEvent q e L i = Sum.inr w := by
    simp [cellRightEvent, hiL, w, k]
  have hjk : j < k := by change i.val - 1 < i.val; omega
  have hpair := (List.pairwise_iff_get.mp hL.2) j k hjk
  have hcut : strictCyclicBetween
      (eventOrdinal q hq.g2 (Sum.inl (cyclicSuccessor e) : PolygonEvent q))
      (eventOrdinal q hq.g2 (Sum.inr v)) (eventOrdinal q hq.g2 (Sum.inr w)) := by
    apply (ordinal_between_iff q hq.g2 _ _ _).mpr
    exact hpair.2
  rw [cellInteriorAnchors_mem_iff, hleft, hright]
  change _ ↔ complementaryEventRank e (crossingVisitEdge q v) < complementaryEventRank e a ∧
    complementaryEventRank e a ≤ complementaryEventRank e (crossingVisitEdge q w)
  constructor
  · intro hbetween
    have hcuts := strictCyclicBetween_nested_interval _ _ _ _ hcut hbetween
    have hleftCut := (ordinal_between_iff q hq.g2 _ _ _).mp hcuts.1
    have hrightCut := (ordinal_between_iff q hq.g2 _ _ _).mp hcuts.2
    have hl := (visitAnchor_arcOrder_iff_complementaryRank_lt q hq.g2 e a v).mp hleftCut
    have hr := ((anchorVisit_arcOrder_iff_complementaryKey_lt q hq.g2 e a w).mp hrightCut).2
    refine ⟨hl,?_⟩
    change toLex (complementaryEventRank e a, (0 : K)) <
      toLex (complementaryEventRank e (crossingVisitEdge q w), crossingVisitParameter q w) at hr
    rw [Prod.Lex.toLex_lt_toLex] at hr
    rcases hr with hlt | ⟨heq,_⟩
    · exact le_of_lt hlt
    · exact le_of_eq heq
  · rintro ⟨hl,hr⟩
    have hleftCut := (visitAnchor_arcOrder_iff_complementaryRank_lt q hq.g2 e a v).mpr hl
    have hne : a ≠ cyclicSuccessor e := by
      intro heq
      have hzero : complementaryEventRank e (cyclicSuccessor e) = 0 := by
        simp [complementaryEventRank]
      rw [heq,hzero] at hl
      omega
    have hkey : toLex (complementaryEventRank e a, (0 : K)) < complementaryVisitKey q e w := by
      change toLex (complementaryEventRank e a, (0 : K)) <
        toLex (complementaryEventRank e (crossingVisitEdge q w), crossingVisitParameter q w)
      rw [Prod.Lex.toLex_lt_toLex]
      rcases lt_or_eq_of_le hr with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr ⟨heq,(crossingVisitParameter_spec q w).1⟩
    have hrightCut := (anchorVisit_arcOrder_iff_complementaryKey_lt q hq.g2 e a w).mpr ⟨hne,hkey⟩
    exact (ordinal_between_iff q hq.g2 _ _ _).mpr (strictCyclicBetween_chain hleftCut hrightCut)

/-- Distinct ordered chosen-edge crossings have strictly increasing return-edge
ranks: equal ranks would force the same return edge, hence the same crossing. -/
theorem internal_return_ranks_strict (q : Fin n → PlanarPoint K)
    (hq : CyclicGeneric q) (e : Fin n) (L : List (DirectGLSSW.EdgeChord q e))
    (hL : OrderedEdgeSupport q hq e L) (i : Fin (L.length+1))
    (hi0 : 0 < i.val) (hiL : i.val < L.length) :
    complementaryEventRank e (crossingVisitEdge q
      (DirectGLSSW.returnVisit q e (L.get ⟨i.val-1, by omega⟩))) <
    complementaryEventRank e (crossingVisitEdge q
      (DirectGLSSW.returnVisit q e (L.get ⟨i.val, hiL⟩))) := by
  let j : Fin L.length := ⟨i.val-1, by omega⟩
  let k : Fin L.length := ⟨i.val, hiL⟩
  have hjk : j < k := by change i.val - 1 < i.val; omega
  have hr := cellReturnKey_strict q hq e L hL j k hjk
  change toLex (complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e (L.get j))),
      crossingVisitParameter q (DirectGLSSW.returnVisit q e (L.get j))) <
    toLex (complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e (L.get k))),
      crossingVisitParameter q (DirectGLSSW.returnVisit q e (L.get k))) at hr
  rw [Prod.Lex.toLex_lt_toLex] at hr
  rcases hr with hlt | ⟨heq,_⟩
  · exact hlt
  · have hedge := complementaryEventRank_injective e heq
    have hchord := returnVisitEdge_injective q e hedge
    have hx := ((List.pairwise_iff_get.mp hL.2) j k hjk).1
    rw [hchord] at hx
    exact (lt_irrefl _ hx).elim

/-- In particular the anchor at the current return edge belongs to the cell. -/
theorem right_return_anchor_mem (q : Fin n → PlanarPoint K)
    (hq : CyclicGeneric q) (e : Fin n) (L : List (DirectGLSSW.EdgeChord q e))
    (hL : OrderedEdgeSupport q hq e L) (i : Fin (L.length+1))
    (hi0 : 0 < i.val) (hiL : i.val < L.length) :
    crossingVisitEdge q (DirectGLSSW.returnVisit q e (L.get ⟨i.val,hiL⟩)) ∈
      cellInteriorAnchors q hq e L i := by
  apply (cellInteriorAnchors_internal_iff_rank q hq e L hL i hi0 hiL _).mpr
  exact ⟨internal_return_ranks_strict q hq e L hL i hi0 hiL,le_rfl⟩

/-- For adjacent return-edge ranks, the membership predicate is the singleton
right anchor. This is a predicate corollary, not a list-contiguity assertion. -/
theorem cellInteriorAnchors_internal_adjacent_iff (q : Fin n → PlanarPoint K)
    (hq : CyclicGeneric q) (e : Fin n) (L : List (DirectGLSSW.EdgeChord q e))
    (hL : OrderedEdgeSupport q hq e L) (i : Fin (L.length+1))
    (hi0 : 0 < i.val) (hiL : i.val < L.length)
    (hadj : complementaryEventRank e (crossingVisitEdge q
      (DirectGLSSW.returnVisit q e (L.get ⟨i.val,hiL⟩))) =
      complementaryEventRank e (crossingVisitEdge q
      (DirectGLSSW.returnVisit q e (L.get ⟨i.val-1,by omega⟩))) + 1)
    (a : Fin n) :
    a ∈ cellInteriorAnchors q hq e L i ↔
      a = crossingVisitEdge q (DirectGLSSW.returnVisit q e (L.get ⟨i.val,hiL⟩)) := by
  constructor
  · intro ha
    have hb := (cellInteriorAnchors_internal_iff_rank q hq e L hL i hi0 hiL a).mp ha
    apply complementaryEventRank_injective e
    omega
  · rintro rfl
    exact right_return_anchor_mem q hq e L hL i hi0 hiL







end DirectGLSSW.CellAnchorRanks
