import ProcessedChildNonnegativeTurns
import PositivePolygonTurns
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SmoothingCornerGeometry
open PermutationOrbits LowestRowContract PolygonDrawingBridge
attribute [local instance] Classical.propDecidable

/-- The actual positive polygon diagram, with the selected initial traversal
and empty processed marks. Connectedness is derived from its physical cycle. -/
def positivePolygonMarkedState {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (T : BasedTraversal (positivePolygonEventDiagram q hq)) : MarkedParentState :=
  ⟨positivePolygonEventDiagram q hq,T,
    ProcessedParentMarks.initial (positivePolygonEventDiagram q hq) T
      (fun x y => (polygonEventDiagram_isCycleOn q hq).2 (Set.mem_univ x) (Set.mem_univ y))⟩

/-- On the actual uniform-left source polygon, every extracted child after any
literal fixed-parent-root history has nonnegative turns. Straight subdivision
vertices are retained; no false strict-turn assertion is made about them. -/
theorem uniform_left_history_child_turns_nonnegative {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i : Fin n, 0 < planarDet (cyclicTangent q i)
      (cyclicTangent q (cyclicSuccessor i)))
    (T : BasedTraversal (positivePolygonEventDiagram q hq))
    (t : MarkedParentState) (h : MarkedParentTrace (positivePolygonMarkedState q hq T) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true))) :
    ∀ a : Fin R.diagram.nArc, 0 ≤ turnDet R.diagram a := by
  exact actual_history_child_turns_nonnegative (positivePolygonEventDiagram q hq) T
    (fun x y => (polygonEventDiagram_isCycleOn q hq).2 (Set.mem_univ x) (Set.mem_univ y))
    (positivePolygonEventDiagram_crossingSign q hq)
    (positivePolygonEventDiagram_turn_nonneg_of_uniform_left q hq hleft) t h c hc R

/-- The same actual child also has a genuine pair of new positive turns, so
nonnegativity does not merely describe an entirely straight cycle. -/
theorem uniform_left_history_child_new_left_corners {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (T : BasedTraversal (positivePolygonEventDiagram q hq))
    (t : MarkedParentState) (h : MarkedParentTrace (positivePolygonMarkedState q hq T) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true))) :
    ∃ a b : Fin R.diagram.nArc, R.diagram.continuation a = b ∧
      0 < turnDet R.diagram a ∧ 0 < turnDet R.diagram b := by
  obtain ⟨a,b,_,_,hab,ha,hb⟩ := actual_child_connector_left_turns
    (positivePolygonEventDiagram q hq) T
    (fun x y => (polygonEventDiagram_isCycleOn q hq).2 (Set.mem_univ x) (Set.mem_univ y))
    (positivePolygonEventDiagram_crossingSign q hq) t h c hc R
  exact ⟨a,b,hab,ha,hb⟩

end DirectGLSSW.HOMFLY.SmoothingCornerGeometry
