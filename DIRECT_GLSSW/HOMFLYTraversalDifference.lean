import HOMFLYFullSkeinStage

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section

/-- The two traversals use exactly the same chosen smoothing child. Their
skein difference therefore has only the switched term, at any pivot. -/
theorem descendingEvaluator_difference_switch {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n) (D : PLLinkDiagram)
    (hD : D.nCrossing = n) (T U : BasedTraversal D) (c : Fin D.nCrossing) :
    descendingLaurentEvaluator D T - descendingLaurentEvaluator D U =
      pivotSwitchFactor D c *
        (descendingLaurentEvaluator (switchCrossing D c) (switchTraversal T c) -
          descendingLaurentEvaluator (switchCrossing D c) (switchTraversal U c)) := by
  rw [descendingEvaluator_eq_any_pivot outer D hD T c,
    descendingEvaluator_eq_any_pivot outer D hD U c,
    descendingEvaluatorPivotBranch, descendingEvaluatorPivotBranch]
  ring

/-- Switching any common geometric site preserves the truth of traversal
agreement. This permits a reduction to a descending source traversal while
retaining the second traversal, including its different component order. -/
theorem descendingEvaluator_agreement_switch_iff {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n) (D : PLLinkDiagram)
    (hD : D.nCrossing = n) (T U : BasedTraversal D) (c : Fin D.nCrossing) :
    (descendingLaurentEvaluator D T = descendingLaurentEvaluator D U) ↔
      descendingLaurentEvaluator (switchCrossing D c) (switchTraversal T c) =
        descendingLaurentEvaluator (switchCrossing D c) (switchTraversal U c) := by
  constructor
  · intro h
    have hd := descendingEvaluator_difference_switch outer (switchCrossing D c) hD
      (switchTraversal T c) (switchTraversal U c) c
    rw [descendingEvaluator_switch_twice, descendingEvaluator_switch_twice,
      h, sub_self, mul_zero] at hd
    exact sub_eq_zero.mp hd
  · intro h
    have hd := descendingEvaluator_difference_switch outer D hD T U c
    rw [h, sub_self, mul_zero] at hd
    exact sub_eq_zero.mp hd

end
end DirectGLSSW.HOMFLY



