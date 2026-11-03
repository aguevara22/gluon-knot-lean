import GeminiLowest.LayeredSublinkFactorization
import Gemini.Solution

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SourceSplitCircle
open DirectGLSSW.HOMFLY DirectGLSSW.HOMFLY.Coefficients
open DirectGLSSW.HOMFLY.Gemini GeminiLowest

/-- Full-polynomial split-circle factor for an actual two-block partition. The
geometric split-circle constructor still has to supply the partition. -/
theorem normalizedEvaluator_twoBlock_circle
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (P : SublinkPartition D (Fin 2)) (hLayer : IsLayeredPartition P)
    (hCircleCrossings : (restrictSublink D (P.block 1)).nCrossing = 0)
    (hCircleComponents : diagramComponentCount (restrictSublink D (P.block 1)) = 1) :
    H D hD = unlinkFactor *
      H (restrictSublink D (P.block 0)) (sublink_arc_count_pos D (P.block 0)) := by
  have hHcandidate : ∀ (E : PLLinkDiagram) (hE : 0 < E.nArc),
      H E hE = candidateEvaluator E hE := by
    intro E hE
    exact normalized_descending_skein_evaluator_unique H candidateEvaluator hH
      (candidateEvaluator_isNormalized all_lowerCrossingEvaluatorSkeinIH) E hE
  rw [hHcandidate D hD]
  rw [candidateEvaluator_layeredPartition hD P hLayer]
  have hcircle : candidateEvaluator (restrictSublink D (P.block 1))
      (sublink_arc_count_pos D (P.block 1)) = 1 := by
    let E := restrictSublink D (P.block 1)
    let T := chooseBasedTraversal E
    have hbad : badCrossings T = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro c hc
      have : IsEmpty (Fin E.nCrossing) := by
        change IsEmpty (Fin (restrictSublink D (P.block 1)).nCrossing)
        rw [hCircleCrossings]
        infer_instance
      exact isEmptyElim c
    have hterm := (candidateEvaluator_isNormalized all_lowerCrossingEvaluatorSkeinIH).1
      E (sublink_arc_count_pos D (P.block 1)) T hbad
    simpa [E, hCircleComponents] using hterm
  simp [Fin.prod_univ_two, hcircle, hHcandidate]

end DirectGLSSW.HOMFLY.SourceSplitCircle

