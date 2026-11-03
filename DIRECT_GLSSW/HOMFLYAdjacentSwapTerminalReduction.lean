import HOMFLYTraversalDifference
import HOMFLYDescendingAdjacentSwap

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section

private theorem adjacentSwap_eq_from_descending_terminal {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (terminal : ∀ (D : PLLinkDiagram), D.nCrossing = n →
      ∀ (T : BasedTraversal D), badCrossings T = ∅ →
      ∀ (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D),
        descendingLaurentEvaluator D
          (reindexTraversalComponents T (adjacentComponentSwap r hr)) =
            descendingUnlinkValue D)
    (D : PLLinkDiagram) (hD : D.nCrossing = n) (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D) :
    descendingLaurentEvaluator D T =
      descendingLaurentEvaluator D
        (reindexTraversalComponents T (adjacentComponentSwap r hr)) := by
  classical
  by_cases hbad : (badCrossings T).Nonempty
  · obtain ⟨c, hc⟩ := hbad
    have hs := adjacentSwap_eq_from_descending_terminal outer terminal
      (switchCrossing D c) hD (switchTraversal T c) r hr
    exact (descendingEvaluator_agreement_switch_iff outer D hD T
      (reindexTraversalComponents T (adjacentComponentSwap r hr)) c).2 hs
  · have hT := Finset.not_nonempty_iff_eq_empty.mp hbad
    rw [descendingLaurentEvaluator_terminal D T (by simp only [hbad, eq_false])]
    exact (terminal D hD T hT r hr).symm
termination_by (badCrossings T).card
decreasing_by
  have hdrop := badCrossings_switch_card T c hc
  omega

/-- Exact fixed-stage reduction to the geometric descending-stack problem.
Neither side of this equivalence is asserted unconditionally. The backward
implication uses an actual terminating sequence of bad-crossing switches,
with the arbitrary second traversal carried throughout. -/
theorem adjacentSwap_invariance_iff_descending_terminal {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n) :
    (∀ (D : PLLinkDiagram), D.nCrossing = n → ∀ (T : BasedTraversal D)
      (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D),
        descendingLaurentEvaluator D T =
          descendingLaurentEvaluator D
            (reindexTraversalComponents T (adjacentComponentSwap r hr))) ↔
    (∀ (D : PLLinkDiagram), D.nCrossing = n →
      ∀ (T : BasedTraversal D), badCrossings T = ∅ →
      ∀ (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D),
        descendingLaurentEvaluator D
          (reindexTraversalComponents T (adjacentComponentSwap r hr)) =
            descendingUnlinkValue D) := by
  constructor
  · intro all D hD T hT r hr
    rw [← all D hD T r hr]
    exact descendingLaurentEvaluator_terminal D T (by simp only [hT, Finset.not_nonempty_empty, eq_false])
  · intro terminal D hD T r hr
    exact adjacentSwap_eq_from_descending_terminal outer terminal D hD T r hr

end
end DirectGLSSW.HOMFLY


