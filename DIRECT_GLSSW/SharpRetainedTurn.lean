import SharpDaughterTurns
import PolygonRotationSum
import ProcessedSharpPolygonCrossings
import HistoricalSharpTurnComparison
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge
  SmoothingCornerGeometry PrincipalTurning DaughterFirstReturn
attribute [local instance] Classical.propDecidable

/-- The retained polygon's literal corner sum is the sharp subdivision's
already characterized total turn. The generic polygon certificate is explicit. -/
theorem sharpDaughter_totalTurn_eq_retainedPolygon {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
    (root : PolygonEvent q) (hroot : retainedCorner q S root)
    (hP : CyclicGeneric (daughterVertex q hq.g2 S root)) :
    totalTurn (SharpDaughter.sharpDaughterDiagram q hq S
      (componentOf (SharpDaughter.P q hq S) root) hNA) =
    totalTurn (positivePolygonEventDiagram (daughterVertex q hq.g2 S root) hP) := by
  rw [SharpDaughterRotation.totalTurn_eq_cornerTotalTurn_root q hq S hNA root hroot,
    positivePolygonEventDiagram_totalTurn]
  rfl

namespace ProcessedExposedChild
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _) (firstVisitedBranch t.2.1 c) (Sum.inl true)))
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))

/-- Actual retained polygon genericity comes from the original fixed opening. -/
theorem historicalSharp_retained_totalTurn :
    totalTurn (historicalSharpDiagram q hq h c hc R) =
      totalTurn (positivePolygonEventDiagram (historicalSharpPolygon q hq h c hc R)
        (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux)) :=
  sharpDaughter_totalTurn_eq_retainedPolygon q hq (sharpSupport q hq h c)
    (sharpSupport_nonalternating q hq h c) _ (sharpInterval_root_retained q hq h c hc R)
    (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux)

theorem historicalSharp_retained_turnInteger :
    turnInteger (historicalSharpDiagram q hq h c hc R) =
      turnInteger (positivePolygonEventDiagram (historicalSharpPolygon q hq h c hc R)
        (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux)) := by
  apply turnInteger_unique
  rw [historicalSharp_retained_totalTurn q hq he h c hc R hAux]
  exact totalTurn_eq_turnInteger _

/-- Whole actual child-to-retained-polygon degree comparison. -/
theorem detached_retained_turnInteger :
    turnInteger R.diagram =
      turnInteger (positivePolygonEventDiagram (historicalSharpPolygon q hq h c hc R)
        (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux)) :=
  (historicalSharp_turnInteger_eq q hq h c hc R).trans
    (historicalSharp_retained_turnInteger q hq he h c hc R hAux)

#check @historicalSharp_retained_totalTurn
#check @detached_retained_turnInteger




end ProcessedExposedChild
end DirectGLSSW.HOMFLY
