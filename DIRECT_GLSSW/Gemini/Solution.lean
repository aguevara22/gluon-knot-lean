import Gemini.PlanarAlgebraicIntersection

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY.Gemini

open DirectGLSSW.HOMFLY DirectGLSSW.HOMFLY.Coefficients

noncomputable section

theorem all_lowerCrossingEvaluatorSkeinIH :
    ∀ n : ℕ, LowerCrossingEvaluatorSkeinIH n :=
  all_skeinIH_of_descending_terminal_step
    (fun _n outer D hD T hT r hr =>
      descending_adjacentSwap_unconditional outer D hD T hT r hr)

theorem normalizedEvaluator_existsUnique :
    ∃! H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff,
      IsNormalizedDescendingSkeinEvaluator H :=
  normalizedEvaluator_existsUnique_of_all_skeinIH all_lowerCrossingEvaluatorSkeinIH

theorem normalizedEvaluator_package :
    ∃ H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff,
      IsNormalizedDescendingSkeinEvaluator H ∧
      (∀ K : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff,
        IsNormalizedDescendingSkeinEvaluator K → K = H) ∧
      (∀ (D : PLLinkDiagram) (hD : 0 < D.nArc) (T : BasedTraversal D),
        H D hD = descendingLaurentEvaluator D T) ∧
      (∀ (D E : PLLinkDiagram) (hD : 0 < D.nArc) (hE : 0 < E.nArc),
        SignedDiagramIso D E → H D hD = H E hE) ∧
      (∀ (D E : PLLinkDiagram) (hD : 0 < D.nArc) (hE : 0 < E.nArc),
        SignedRegularDeletion D E → H D hD = H E hE) :=
  normalizedEvaluator_package_of_all_skeinIH all_lowerCrossingEvaluatorSkeinIH

end

end DirectGLSSW.HOMFLY.Gemini
