import CellAnchorRanks

set_option autoImplicit false

namespace DirectGLSSW.CellAnchorInterval
open MixedConsecutiveCapWord MixedEdgeSupportOrder FiniteCycleOrder
open CellAnchorRanks CyclicAnchorInterval

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-- The actual internal-cell filter is exactly the consecutive original-anchor slice.
The current return edge's anchor is included as the last element. -/
theorem cellInteriorAnchors_internal_eq_interval (q : Fin n → PlanarPoint K)
    (hq : CyclicGeneric q) (e : Fin n) (L : List (DirectGLSSW.EdgeChord q e))
    (hL : OrderedEdgeSupport q hq e L) (i : Fin (L.length+1))
    (hi0 : 0 < i.val) (hiL : i.val < L.length) :
    let r := complementaryEventRank e (crossingVisitEdge q
      (DirectGLSSW.returnVisit q e (L.get ⟨i.val-1, by omega⟩)))
    let s := complementaryEventRank e (crossingVisitEdge q
      (DirectGLSSW.returnVisit q e (L.get ⟨i.val, hiL⟩)))
    cellInteriorAnchors q hq e L i =
      List.ofFn (fun j : Fin (s-r) => cyclicVertexIndex e (r+1+j.val)) := by
  classical
  dsimp only
  let r := complementaryEventRank e (crossingVisitEdge q
    (DirectGLSSW.returnVisit q e (L.get ⟨i.val-1, by omega⟩)))
  let s := complementaryEventRank e (crossingVisitEdge q
    (DirectGLSSW.returnVisit q e (L.get ⟨i.val, hiL⟩)))
  change cellInteriorAnchors q hq e L i =
    List.ofFn (fun j : Fin (s-r) => cyclicVertexIndex e (r+1+j.val))
  have hs : s+1 ≤ n := Nat.succ_le_iff.mpr (complementaryRank_lt_size e _)
  have hpred : (fun a : Fin n => decide
      (strictCyclicBetween (eventOrdinal q hq.g2 (cellLeftEvent q e L i))
        (eventOrdinal q hq.g2 (Sum.inl a : PolygonEvent q))
        (eventOrdinal q hq.g2 (cellRightEvent q e L i)))) =
      (fun a : Fin n => decide
        (r+1 ≤ complementaryEventRank e a ∧ complementaryEventRank e a < s+1)) := by
    funext a
    have hp : strictCyclicBetween (eventOrdinal q hq.g2 (cellLeftEvent q e L i))
        (eventOrdinal q hq.g2 (Sum.inl a : PolygonEvent q))
        (eventOrdinal q hq.g2 (cellRightEvent q e L i)) ↔
        r+1 ≤ complementaryEventRank e a ∧ complementaryEventRank e a < s+1 := by
      rw [← CellAnchorRanks.cellInteriorAnchors_mem_iff q hq e L i a,
        CellAnchorRanks.cellInteriorAnchors_internal_iff_rank q hq e L hL i hi0 hiL a]
      dsimp [r,s]
      omega
    simp only [hp]
  unfold cellInteriorAnchors
  rw [hpred, cyclic_anchor_interval e (r+1) (s+1) hs]
  simp only [Nat.add_sub_add_right]
  rfl


end DirectGLSSW.CellAnchorInterval
