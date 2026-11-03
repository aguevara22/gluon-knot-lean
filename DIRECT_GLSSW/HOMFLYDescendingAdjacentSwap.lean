import HOMFLYAllBasepointIndependence

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section

/-- On a descending diagram, an adjacent component swap makes precisely the
crossings between those two components bad. This is the concrete terminal
case remaining for component-order invariance. -/
theorem badAt_adjacentSwap_of_descending {D : PLLinkDiagram}
    (T : BasedTraversal D) (hT : badCrossings T = ∅)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) :
    badAt (reindexTraversalComponents T (adjacentComponentSwap r hr)) c ↔
      adjacentSwapAffectedCrossing T r c := by
  have hover := (badCrossings_eq_empty_iff_firstVisited_over T).1 hT c
  rw [adjacentSwapAffectedCrossing_iff_branch_changes T r hr c]
  change (firstVisitedBranch (reindexTraversalComponents T (adjacentComponentSwap r hr)) c ≠
    D.overBranch c) ↔ _
  rw [hover]

theorem badCrossings_adjacentSwap_of_descending {D : PLLinkDiagram}
    (T : BasedTraversal D) (hT : badCrossings T = ∅)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D) :
    badCrossings (reindexTraversalComponents T (adjacentComponentSwap r hr)) =
      (by classical exact Finset.univ.filter (adjacentSwapAffectedCrossing T r)) := by
  classical
  ext c
  simp only [badCrossings, Finset.mem_filter, Finset.mem_univ, true_and]
  exact badAt_adjacentSwap_of_descending T hT r hr c

end
end DirectGLSSW.HOMFLY



