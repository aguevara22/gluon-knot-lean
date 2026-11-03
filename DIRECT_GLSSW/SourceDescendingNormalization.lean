import Gemini.Solution

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY.DescendingSpatialNormalization
open Coefficients

/-- The already constructed normalized evaluator has the literal k-component
unlink value at every terminal descending traversal. -/
theorem candidateEvaluator_descending_value
    (D : PLLinkDiagram) (hD : 0 < D.nArc) (T : BasedTraversal D)
    (hbad : badCrossings T = ∅) :
    Gemini.candidateEvaluator D hD =
      unlinkFactor ^ (diagramComponentCount D - 1) :=
  (Gemini.candidateEvaluator_isNormalized
    Gemini.all_lowerCrossingEvaluatorSkeinIH).1 D hD T hbad

/-- The knot case has polynomial one without any topological premise
being inserted into the evaluator theorem. -/
theorem candidateEvaluator_descending_knot_one
    (D : PLLinkDiagram) (hD : 0 < D.nArc) (T : BasedTraversal D)
    (hbad : badCrossings T = ∅) (hknot : diagramComponentCount D = 1) :
    Gemini.candidateEvaluator D hD = 1 := by
  rw [candidateEvaluator_descending_value D hD T hbad, hknot]
  simp

end DirectGLSSW.HOMFLY.DescendingSpatialNormalization

