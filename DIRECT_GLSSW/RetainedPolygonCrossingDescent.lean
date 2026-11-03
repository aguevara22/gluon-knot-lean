import ProcessedSharpPolygonEquiv
import ComponentRestrictionCrossingBound

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.HOMFLY.ProcessedExposedChild

open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry

attribute [local instance] Classical.propDecidable

variable {n : ℕ} (q : Fin (n + 2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace
      (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

/-- The actual retained sharp diagram has exactly the crossings of the
extracted smoothed component. -/
theorem historicalSharpDiagram_nCrossing_eq_R :
    (historicalSharpDiagram q hq h c hc R).nCrossing = R.diagram.nCrossing := by
  have hcard := Fintype.card_congr (historicalSharpCrossingEquiv q hq h c hc R)
  simpa only [Fintype.card_fin] using hcard.symm

/-- The actual retained sharp polygon has exactly the crossings of the
extracted smoothed component. -/
theorem historicalSharpPolygon_crossing_count_eq_R
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary
      (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq)) :
    Fintype.card (PolygonCrossing (historicalSharpPolygon q hq h c hc R)) =
      R.diagram.nCrossing := by
  have hcard := Fintype.card_congr
    (detachedSharpPolygonCrossingEquiv q hq h c hc R he hAux).symm
  simpa only [Fintype.card_fin] using hcard

/-- The actual retained sharp polygon has strictly fewer crossings than the
current parent diagram. The only strict descent input is the real smoothing
component restriction theorem. -/
theorem historicalSharpPolygon_crossing_count_lt_parent
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary
      (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq)) :
    Fintype.card (PolygonCrossing (historicalSharpPolygon q hq h c hc R)) <
      t.1.nCrossing := by
  rw [historicalSharpPolygon_crossing_count_eq_R q hq h c hc R he hAux]
  exact R.nCrossing_lt_before_smoothing t.1 c _





end DirectGLSSW.HOMFLY.ProcessedExposedChild
