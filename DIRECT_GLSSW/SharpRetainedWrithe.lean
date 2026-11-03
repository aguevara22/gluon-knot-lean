import ProcessedSharpPolygonEquiv
import HistoricalSharpEvaluatorBase
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
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _) (firstVisitedBranch t.2.1 c) (Sum.inl true)))
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))

/-- Complete crossing correspondence preserves signed writhe; all these
surviving crossings are positive in both actual diagrams. -/
theorem detached_retained_writhe :
    diagramWrithe R.diagram =
      diagramWrithe (positivePolygonEventDiagram (historicalSharpPolygon q hq h c hc R)
        (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux)) := by
  unfold diagramWrithe
  apply Fintype.sum_equiv ((detachedSharpPolygonCrossingEquiv q hq h c hc R he hAux).trans
    (crossingFin (historicalSharpPolygon q hq h c hc R)))
  intro d
  unfold writheSign
  rw [h.detachedCrossingOrigin_sign c hc R d]
  simp only [positivePolygonMarkedState,positivePolygonEventDiagram_crossingSign]

#check @detached_retained_writhe

end DirectGLSSW.HOMFLY.ProcessedExposedChild
