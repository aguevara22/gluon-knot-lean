import HistoricalChildAuxiliary
import ExposedPolygonCornerFromChildren
import SupportingTruncationAuxiliary
import PolygonRebaseTurning
import ActiveArcExposedAuxiliary
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract FramedPolynomial PolygonDrawingBridge Coefficients PrincipalTurning
attribute [local instance] Classical.propDecidable

theorem MarkedParentStep.nCrossing_le {s t : MarkedParentState}
    (step : MarkedParentStep s t) : t.1.nCrossing ≤ s.1.nCrossing := by
  cases step with
  | switched S c hc hgood => exact le_rfl
  | smoothed S c hc hgood R => exact Nat.le_of_lt (R.nCrossing_lt_before_smoothing _ c _)

theorem MarkedParentTrace.nCrossing_le {s t : MarkedParentState}
    (h : MarkedParentTrace s t) : t.1.nCrossing ≤ s.1.nCrossing := by
  induction h with
  | nil => exact le_rfl
  | cons step tail ih => exact ih.trans step.nCrossing_le

namespace PolygonDrawingBridge
/-- Internal framed-row transport; actual truncation/rebase supplies all three equalities. -/
theorem positivePolygon_framedRow_eq_of_data {m n : ℕ}
    (q : Fin m → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (Q : Fin n → PlanarPoint ℝ) (hQ : CyclicGeneric Q)
    (hcount : (positivePolygonEventDiagram q hq).nCrossing = (positivePolygonEventDiagram Q hQ).nCrossing)
    (hturn : turnInteger (positivePolygonEventDiagram q hq) = turnInteger (positivePolygonEventDiagram Q hQ))
    (heval : Gemini.candidateEvaluator (positivePolygonEventDiagram q hq) (positivePolygonEventDiagram_nArc_pos _ _) =
      Gemini.candidateEvaluator (positivePolygonEventDiagram Q hQ) (positivePolygonEventDiagram_nArc_pos _ _)) :
    framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram q hq) (positivePolygonEventDiagram_nArc_pos _ _)
      (componentOf (positivePolygonEventDiagram q hq).continuation ⟨0,positivePolygonEventDiagram_nArc_pos _ _⟩) =
    framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram Q hQ) (positivePolygonEventDiagram_nArc_pos _ _)
      (componentOf (positivePolygonEventDiagram Q hQ).continuation ⟨0,positivePolygonEventDiagram_nArc_pos _ _⟩) := by
  have hw (D : PLLinkDiagram) (hp : ∀ c, crossingSign D c=Sign.pos) : diagramWrithe D=(D.nCrossing : ℤ) := by
    unfold diagramWrithe writheSign
    simp only [hp]
    simp
  unfold framedKnotRow
  rw [componentTurnInteger_eq_total_of_connected _ (positivePolygonEventDiagram_connected q hq),
    componentTurnInteger_eq_total_of_connected _ (positivePolygonEventDiagram_connected Q hQ),
    hw _ (positivePolygonEventDiagram_crossingSign q hq),
    hw _ (positivePolygonEventDiagram_crossingSign Q hQ),hcount,hturn,heval]
end PolygonDrawingBridge
end DirectGLSSW.HOMFLY
