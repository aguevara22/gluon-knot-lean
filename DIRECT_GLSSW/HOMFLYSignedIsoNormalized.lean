import Gemini.Solution
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SignedDiagramIso
open Coefficients

/-- Every normalized evaluator inherits signed-diagram invariance from the
unconditional normalized evaluator package and its proved uniqueness. -/
theorem normalizedEvaluator_eq
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    {D E : PLLinkDiagram} (I : SignedDiagramIso D E)
    (hD : 0 < D.nArc) (hE : 0 < E.nArc) : H D hD = H E hE := by
  have hG := Gemini.candidateEvaluator_isNormalized Gemini.all_lowerCrossingEvaluatorSkeinIH
  have hD' := normalized_descending_skein_evaluator_unique H Gemini.candidateEvaluator hH hG D hD
  have hE' := normalized_descending_skein_evaluator_unique H Gemini.candidateEvaluator hH hG E hE
  have hI := Gemini.candidateEvaluator_signedDiagramIso
    Gemini.all_lowerCrossingEvaluatorSkeinIH D E hD hE I
  exact hD'.trans (hI.trans hE'.symm)

end DirectGLSSW.HOMFLY.SignedDiagramIso
