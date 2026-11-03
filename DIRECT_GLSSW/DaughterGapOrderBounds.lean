import RetainedGapRank
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DaughterFirstReturn
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {n : ℕ} (q : Fin n → PlanarPoint K) (hG2 : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)

theorem cornerGap_offset_lt_later (c d : CornerCoord q hG2 S root)
    (hcd : c<d) (k : ℕ)
    (hk : k<cornerGap q hG2 S root c.val (cornerSuccessor q hG2 S root c).val) :
    c.val.val+k<d.val.val := by
  have hs := orderedCyclicSuccessor_order_spec (CornerCoord q hG2 S root) c
  rcases hs with ⟨hinc,hmin⟩ | ⟨hmax,_⟩
  · have hle := hmin d hcd
    change c.val.val < (cornerSuccessor q hG2 S root c).val.val at hinc
    change (cornerSuccessor q hG2 S root c).val.val ≤ d.val.val at hle
    unfold cornerGap at hk
    rw [if_pos hinc] at hk
    omega
  · exact ((not_lt_of_ge (hmax d)) hcd).elim
end DirectGLSSW.DaughterFirstReturn
