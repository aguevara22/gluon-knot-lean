import ExposedWhitney
import PositivePolygonInitialGeometryProbe

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits PrincipalTurning
attribute [local instance] Classical.propDecidable

/-- The accepted literal supporting-root invariant supplies the old Whitney domain. -/
theorem supportingRootGeometry_actualRootVertexHalfplane
    (s : MarkedParentState) (p q : PlanarPoint ℝ)
    (hs : SupportingRootGeometry s p q) (C : diagramComponent s.1) :
    actualRootVertexHalfplane s.2.1 C := by
  intro v
  rw [(hs.1 C).1, (hs.1 C).2]
  exact hs.2 v

/-- Actual exposed Whitney identity throughout an initial-anchored parent history. -/
theorem supportingRootGeometry_exposed_whitney
    (s : MarkedParentState) (p q : PlanarPoint ℝ)
    (hs : SupportingRootGeometry s p q) (C : diagramComponent s.1) :
    (componentTurnInteger s.1 C : ℝ) +
      (∑ c ∈ actualComponentSelfCrossings s.2.1 C,
        if 0 < complexDet (crossingVector s.1 c (firstVisitedBranch s.2.1 c))
            (crossingVector s.1 c (otherBranch (firstVisitedBranch s.2.1 c)))
        then (1 : ℝ) else -1) = 1 :=
  actualComponent_exposed_whitney s.2.1 C
    (supportingRootGeometry_actualRootVertexHalfplane s p q hs C)

namespace PolygonDrawingBridge
open ExposedOpenPrimitive

theorem positivePolygon_history_exposed_whitney
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : LeftExposed q ⟨0,by have := hq.size_ge_three;omega⟩)
    (t : MarkedParentState)
    (h : MarkedParentTrace
      ⟨positivePolygonEventDiagram q hq,initialAnchorTraversal q hq,
        ProcessedParentMarks.initial _ _ (positivePolygonEventDiagram_connected q hq)⟩ t)
    (C : diagramComponent t.1) :
    (componentTurnInteger t.1 C : ℝ) +
      (∑ c ∈ actualComponentSelfCrossings t.2.1 C,
        if 0 < complexDet (crossingVector t.1 c (firstVisitedBranch t.2.1 c))
            (crossingVector t.1 c (otherBranch (firstVisitedBranch t.2.1 c)))
        then (1 : ℝ) else -1) = 1 := by
  exact supportingRootGeometry_exposed_whitney t _ _
    (positivePolygon_history_supporting_root q hq he t h) C

end PolygonDrawingBridge
end DirectGLSSW.HOMFLY

#check @DirectGLSSW.HOMFLY.supportingRootGeometry_actualRootVertexHalfplane

#check @DirectGLSSW.HOMFLY.supportingRootGeometry_exposed_whitney

#check @DirectGLSSW.HOMFLY.PolygonDrawingBridge.positivePolygon_history_exposed_whitney

