import PositivePolygonChildCrossings
import ArcPolygonVisitParameters

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW PermutationOrbits PolygonDrawing
attribute [local instance] Classical.propDecidable

/-- Every actual child self-crossing has its upper physical edge no later than the cut's upper edge. -/
theorem positiveSmoothedChild_rightEdge_le {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (c d : PolygonCrossing q) (hd : d≠c)
    (hself : ∀ i : Fin 2,
      componentOf (smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)).continuation
        ((smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)).incoming
          (positiveSmoothedCrossing q hq c d hd) i) = positiveSmoothedChildComponent q hq c) :
    d.val.2 ≤ c.val.2 := by
  letI := polygonEventOrder q hq.g2
  have h := ((positiveSmoothedChild_selfCrossing_iff q hq c d hd).mp hself).2
  rcases (polygonEvent_lt_iff q hq.g2 _ _).mp h with h|h
  · exact le_of_lt (by simpa [visit,polygonEventEdge,crossingVisitEdge] using h)
  · exact le_of_eq (by simpa [visit,polygonEventEdge,crossingVisitEdge] using h.1)

/-- No closing-edge crossing is a self-crossing of the first detached child. -/
theorem positiveSmoothedChild_no_closing_edge {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (c : ActiveArc.Crossing q) (d : PolygonCrossing q)
    (hd : d≠ActiveArc.polygonCrossingOfArc q c)
    (hself : ∀ i : Fin 2,
      componentOf (smoothCrossing (positivePolygonEventDiagram q hq)
        (crossingFin q (ActiveArc.polygonCrossingOfArc q c))).continuation
        ((smoothCrossing (positivePolygonEventDiagram q hq)
          (crossingFin q (ActiveArc.polygonCrossingOfArc q c))).incoming
          (positiveSmoothedCrossing q hq (ActiveArc.polygonCrossingOfArc q c) d hd) i) =
        positiveSmoothedChildComponent q hq (ActiveArc.polygonCrossingOfArc q c)) :
    d.val.2.val<n+1 := by
  have h := positiveSmoothedChild_rightEdge_le q hq (ActiveArc.polygonCrossingOfArc q c) d hd hself
  exact lt_of_le_of_lt h c.val.2.isLt
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
