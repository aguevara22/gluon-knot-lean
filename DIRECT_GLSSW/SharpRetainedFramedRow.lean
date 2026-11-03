import SharpRetainedEvaluator
import SharpRetainedWrithe
import SharpRetainedTurn
import FramingActualRelations
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge
  SmoothingCornerGeometry Coefficients PrincipalTurning
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))

/-- Writhe and degree have already been transported on the actual history.
This helper isolates the remaining evaluator comparison for the existing row. -/
theorem detached_retained_framedRow_of_evaluator_eq
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hEval : H R.diagram R.nonempty =
      H (historicalRetainedDiagram q hq h c hc R he hAux)
        (historicalRetainedDiagram_nArc_pos q hq he h c hc R hAux))
    (C : diagramComponent R.diagram)
    (E : diagramComponent (historicalRetainedDiagram q hq h c hc R he hAux)) :
    framedKnotRow H R.diagram R.nonempty C =
      framedKnotRow H (historicalRetainedDiagram q hq h c hc R he hAux)
        (historicalRetainedDiagram_nArc_pos q hq he h c hc R hAux) E := by
  have hr := componentTurnInteger_eq_total_of_connected R.diagram
    R.continuation_sameCycle C
  have he' := componentTurnInteger_eq_total_of_connected
    (historicalRetainedDiagram q hq h c hc R he hAux)
    (fun x y => (polygonEventDiagram_isCycleOn _
      (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux)).2
      (Set.mem_univ x) (Set.mem_univ y)) E
  unfold framedKnotRow
  rw [hr, he', hEval]
  have hw : diagramWrithe R.diagram =
      diagramWrithe (historicalRetainedDiagram q hq h c hc R he hAux) :=
    detached_retained_writhe q hq he h c hc R hAux
  have ht : turnInteger R.diagram =
      turnInteger (historicalRetainedDiagram q hq h c hc R he hAux) :=
    detached_retained_turnInteger q hq he h c hc R hAux
  rw [hw, ht]

#check @detached_retained_framedRow_of_evaluator_eq

end DirectGLSSW.HOMFLY.ProcessedExposedChild
