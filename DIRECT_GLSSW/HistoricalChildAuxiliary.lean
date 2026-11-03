import HistoricalChildNestedWords
import HistoricalRefinedGenericity
import CanonicalRecursiveChild
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry
open DaughterFirstReturn
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))




variable (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))


/-- Actual historical child AUX inheritance from the original fixed opening.
Every support and every root is covered; no new genericity certificate is assumed. -/
theorem historicalSharpPolygon_auxiliaryGenericity :
    GeometricSmoothingWeights.auxiliaryGenericity (historicalSharpPolygon q hq h c hc R)
      (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux) := by
  intro S hS x
  have hU := historicalChildLift_nonalternating q hq h c hc R he hAux S hS
  have hg := historical_refined_daughter_cyclicGeneric q hq h c hc R he hAux
    (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S) hU Finset.subset_union_left
    (retainedEventMap q hq h c hc R x) (retainedEventMap_mem q hq h c hc R x)
  have hw := historicalChild_daughterPointList_nested_eq q hq h c hc R he hAux S hS x
  exact DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated
    ⟨0,by simpa only [List.rotate_zero] using hw.symm⟩ hg

/-- The actual extraction witness is produced internally by the accepted
canonical component constructor. -/
theorem canonical_historical_child_auxiliaryGenericity :
    GeometricSmoothingWeights.auxiliaryGenericity
      (historicalSharpPolygon q hq h c hc (canonicalDetachedRestriction t c))
      (originalSingleton_daughter_cyclicGeneric q hq he h c hc (canonicalDetachedRestriction t c) hAux) :=
  historicalSharpPolygon_auxiliaryGenericity q hq h c hc (canonicalDetachedRestriction t c) he hAux
end DirectGLSSW.HOMFLY.ProcessedExposedChild
