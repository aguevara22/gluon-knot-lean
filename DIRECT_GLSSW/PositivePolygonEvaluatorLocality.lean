import PositivePolygonLocalIso
import FramingActualRelations
import HOMFLYSignedIsoNormalized
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PositivePolygonLocality
open PolygonDrawingBridge Coefficients Filter Topology

/-- Crossing count and the same concrete normalized evaluator are preserved
on an actual polygon neighborhood. No knot equivalence is supplied. -/
theorem eventually_positivePolygon_evaluator_count {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ r in 𝓝 q, ∃ hr : CyclicGeneric r,
      (positivePolygonEventDiagram r hr).nCrossing=(positivePolygonEventDiagram q hq).nCrossing ∧
      Gemini.candidateEvaluator (positivePolygonEventDiagram r hr) (positivePolygonEventDiagram_nArc_pos r hr)=
        Gemini.candidateEvaluator (positivePolygonEventDiagram q hq) (positivePolygonEventDiagram_nArc_pos q hq) := by
  filter_upwards [eventually_positivePolygon_signedIso q hq] with r h
  obtain ⟨hr,⟨E⟩⟩ := h
  refine ⟨hr,?_,?_⟩
  · simpa only [Fintype.card_fin] using (Fintype.card_congr E.crossingEquiv).symm
  · exact (E.normalizedEvaluator_eq Gemini.candidateEvaluator
      (Gemini.candidateEvaluator_isNormalized Gemini.all_lowerCrossingEvaluatorSkeinIH)
      (positivePolygonEventDiagram_nArc_pos q hq) (positivePolygonEventDiagram_nArc_pos r hr)).symm
end DirectGLSSW.HOMFLY.PositivePolygonLocality
