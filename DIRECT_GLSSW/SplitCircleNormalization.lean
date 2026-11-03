import SplitCircleOldIso
import SourceSplitCircle

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SplitCircleConstructor
open DirectGLSSW DirectGLSSW.PermutationOrbits GeminiLowest Coefficients

/-- The actual translated triangle adjoins one split circle to every nonempty
admitted polygonal link diagram, with the source normalized HOMFLY factor. -/
theorem normalizedEvaluator_splitCircle
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    (D : PLLinkDiagram) (hD : 0 < D.nArc) :
    H (splitCircleDiagram D hD) (by rw [splitCircle_arc_count]; omega) =
      unlinkFactor * H D hD := by
  let R := chosenRightBound D hD
  let hl := chosenRightBound_left D hD
  let hr := chosenRightBound_triangle D hD
  let E := J D R hl hr
  let P := joinedPartition D R hl hr hD
  have hE : 0 < E.nArc := by change 0 < D.nArc + 3; omega
  have hfactor := SourceSplitCircle.normalizedEvaluator_twoBlock_circle H hH
    E hE P (joinedPartition_layered D R hl hr hD)
    (joinedPartition_right_crossing_count D R hl hr hD)
    (joinedPartition_right_component_count D R hl hr hD)
  have hiso := SignedDiagramIso.normalizedEvaluator_eq H hH
    (leftRestrictionSignedIso D R hl hr hD)
    (sublink_arc_count_pos E (P.block 0)) hD
  change H (splitCircleDiagram D hD) _ = _
  simpa only [splitCircleDiagram, E, P, R, hl, hr] using
    (hfactor.trans (congrArg (fun x => unlinkFactor * x) hiso))

end DirectGLSSW.HOMFLY.SplitCircleConstructor

