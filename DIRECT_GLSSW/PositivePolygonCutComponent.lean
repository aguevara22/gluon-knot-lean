import OrderedCutInterval
import PositivePolygonInitialEncounter
import HOMFLYSmoothingVisitTransport

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW PermutationOrbits PolygonDrawing Equiv
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

private theorem incoming_rep (c : PolygonCrossing q) (i : Fin 2) :
    (positivePolygonEventDiagram q hq).incoming (crossingFin q c) i =
      eventFin q (incoming q hq c i) := by
  simp only [positivePolygonEventDiagram,positiveDiagram,polygonEventDiagram,
    incomingIndex,Equiv.symm_apply_apply]

/-- Incoming physical event labels of a polygon crossing are in original edge order. -/
theorem polygon_incoming_zero_lt_one (c : PolygonCrossing q) :
    letI := polygonEventOrder q hq.g2
    incoming q hq c 0 < incoming q hq c 1 := by
  letI := polygonEventOrder q hq.g2
  apply (polygonEvent_lt_iff q hq.g2 _ _).mpr
  left
  rw [incoming_edge,incoming_edge]
  simpa [visit,polygonEventEdge,crossingVisitEdge] using c.property.1

private theorem eventFin_cut_step (c : PolygonCrossing q) (x : PolygonEvent q) :
    eventFin q ((polygonEventSuccessor q hq.g2 *
      swap (incoming q hq c 0) (incoming q hq c 1)) x) =
      cutContinuation (positivePolygonEventDiagram q hq) (crossingFin q c) (eventFin q x) := by
  simp only [Perm.mul_apply,cutContinuation,incoming_rep]
  change eventFin q (polygonEventSuccessor q hq.g2 _) =
    (polygonEventDiagram q hq).continuation _
  rw [←polygonEventDiagram_continuation]
  exact congrArg (polygonEventDiagram q hq).continuation
    ((eventFin q).injective.map_swap (incoming q hq c 0) (incoming q hq c 1) x)

/-- Exact physical old arcs in connector1's smoothed component form (incoming0,incoming1]. -/
theorem smooth_child_component_old_arc_iff (c : PolygonCrossing q) (x : PolygonEvent q) :
    letI := polygonEventOrder q hq.g2
    componentOf (smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)).continuation
      (smoothArcEquiv (positivePolygonEventDiagram q hq) (Sum.inl (eventFin q x))) =
    componentOf (smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)).continuation
      (smoothArcEquiv (positivePolygonEventDiagram q hq) (Sum.inr (1 : Fin 2))) ↔
      incoming q hq c 0 < x ∧ x ≤ incoming q hq c 1 := by
  letI := polygonEventOrder q hq.g2
  rw [←smoothCutComponentEquiv_old,←smoothCutComponentEquiv_connector]
  have he := sameCycle_iff_of_intertwining (eventFin q)
    (polygonEventSuccessor q hq.g2 * swap (incoming q hq c 0) (incoming q hq c 1))
    (cutContinuation (positivePolygonEventDiagram q hq) (crossingFin q c))
    (eventFin_cut_step q hq c) (incoming q hq c 1) x
  have hc :
      componentOf (cutContinuation (positivePolygonEventDiagram q hq) (crossingFin q c))
        (eventFin q x) =
      componentOf (cutContinuation (positivePolygonEventDiagram q hq) (crossingFin q c))
        ((positivePolygonEventDiagram q hq).incoming (crossingFin q c) 1) ↔
      (polygonEventSuccessor q hq.g2 * swap (incoming q hq c 0) (incoming q hq c 1)).SameCycle
        (incoming q hq c 1) x := by
    rw [incoming_rep]
    constructor
    · intro h
      exact he.mpr ((componentOf_eq_iff _ _ _).mp h.symm)
    · intro h
      exact ((componentOf_eq_iff _ _ _).mpr (he.mp h)).symm
  rw [(smoothCutComponentEquiv (positivePolygonEventDiagram q hq) (crossingFin q c)).injective.eq_iff]
  have ho := orderedCut_sameCycle_right_iff (α := PolygonEvent q)
    (incoming q hq c 0) (incoming q hq c 1) x (polygon_incoming_zero_lt_one q hq c)
  exact hc.trans ho
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
