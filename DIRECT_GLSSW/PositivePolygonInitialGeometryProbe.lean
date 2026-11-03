import PositivePolygonInitialExposure
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open PermutationOrbits ExposedOpenPrimitive

theorem positivePolygon_history_supporting_root
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : LeftExposed q ⟨0,by have := hq.size_ge_three;omega⟩)
    (t : MarkedParentState)
    (h : MarkedParentTrace
      ⟨positivePolygonEventDiagram q hq,initialAnchorTraversal q hq,
        ProcessedParentMarks.initial _ _ (positivePolygonEventDiagram_connected q hq)⟩ t) :
    SupportingRootGeometry t
      ((positivePolygonEventDiagram q hq).vertexPoint
        ((positivePolygonEventDiagram q hq).arcSource (eventFin q (initialAnchor q hq))))
      ((positivePolygonEventDiagram q hq).vertexPoint
        ((positivePolygonEventDiagram q hq).arcTarget (eventFin q (initialAnchor q hq)))) := by
  let C0 := componentOf (positivePolygonEventDiagram q hq).continuation
    (eventFin q (initialAnchor q hq))
  have hg := h.supportingRootGeometry _ _
    (initial_supportingRootGeometry (positivePolygonEventDiagram q hq)
      (initialAnchorTraversal q hq) (positivePolygonEventDiagram_connected q hq) C0
      (initialAnchorTraversal_supporting q hq he C0))
  simpa only [initialAnchorTraversal_baseArc] using hg
end DirectGLSSW.HOMFLY.PolygonDrawingBridge

#check @DirectGLSSW.HOMFLY.PolygonDrawingBridge.positivePolygonEventDiagram_connected

#check @DirectGLSSW.HOMFLY.PolygonDrawingBridge.positivePolygonEventDiagram_vertex_halfplane

#check @DirectGLSSW.HOMFLY.PolygonDrawingBridge.positivePolygonEventDiagram_supporting_anchor

#check @DirectGLSSW.HOMFLY.PolygonDrawingBridge.initialAnchorTraversal_supporting

#check @DirectGLSSW.HOMFLY.PolygonDrawingBridge.positivePolygon_history_supporting_root

