import NormalizedMixedEdgeMatrixSum

set_option autoImplicit false

namespace DirectGLSSW.NormalizedEdgeTurns
open ExtendedReturnArcGeometry InteriorEdgeEvents

/-- The complementary penultimate vertex labels the incoming edge at e. -/
theorem penultimate_precedes_edge {n : ℕ} (hn : 3 ≤ n) (e : Fin n) :
    cyclicSuccessor (cyclicVertexIndex e (n-2)) = e := by
  rw [← InteriorEdgeEvents.index_succ e (n-2) (by omega)]
  have h : n-2+1=n-1 := by omega
  rw [h,cyclicVertexIndex_last]

theorem cyclicTangent_relabel {K : Type*} [Field K] [LinearOrder K] {n : ℕ}
    (q : Fin n → PlanarPoint K) (e : Fin n) :
    cyclicTangent (q ∘ cyclicVertexEquiv e) = cyclicTangent q ∘ cyclicVertexEquiv e := by
  funext a
  simp only [cyclicTangent,Function.comp_apply,cyclicVertexEquiv_commutes_successor]

/-- The opened word's endpoint determinants are the Cartesian turns at the
two actual endpoints of the chosen polygon edge. -/
theorem opened_endpoint_turn_product {n : ℕ} (hn : 3 ≤ n)
    (q : Fin n → PlanarPoint ℝ) (e : Fin n) :
    planarDet (cyclicTangent (q ∘ cyclicVertexEquiv e) (lastIndex hn))
      (cyclicTangent (q ∘ cyclicVertexEquiv e) (zeroIndex hn)) *
    planarDet (cyclicTangent (q ∘ cyclicVertexEquiv e) (penultimateIndex hn))
      (cyclicTangent (q ∘ cyclicVertexEquiv e) (lastIndex hn)) =
    planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
      planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) := by
  rw [cyclicTangent_relabel,InteriorEdgeEvents.opened_last,InteriorEdgeEvents.opened_zero]
  rfl




end DirectGLSSW.NormalizedEdgeTurns
