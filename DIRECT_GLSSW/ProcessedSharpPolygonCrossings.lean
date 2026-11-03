import DaughterInteriorCarrier
import ProcessedSharpCrossingComparison
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

/-- The historical first old arc is the actual selected outgoing visit, hence
its polygon event is a retained corner of the original singleton. -/
theorem sharpInterval_root_retained :
    DaughterFirstReturn.retainedCorner q (sharpSupport q hq h c)
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) := by
  unfold sharpIntervalEvent
  rw [h.detachedOriginalArc_first c hc R]
  change DaughterFirstReturn.retainedCorner q (sharpSupport q hq h c)
    ((eventFin q).symm ((positivePolygonEventDiagram q hq).outgoing (h.crossingOrigin c)
      ((positivePolygonEventDiagram q hq).through (h.crossingOrigin c) (firstVisitedBranch t.2.1 c))))
  rw [SharpDaughter.outgoing_event]
  change DaughterFirstReturn.retainedCorner q (sharpSupport q hq h c)
    (PolygonDrawing.visit q ((crossingFin q).symm (h.crossingOrigin c)) (firstVisitedBranch t.2.1 c))
  generalize firstVisitedBranch t.2.1 c = i
  fin_cases i <;> simp [PolygonDrawing.visit,DaughterFirstReturn.retainedCorner,sharpSupport]

def historicalSharpPolygon := DaughterFirstReturn.daughterVertex q hq.g2
  (sharpSupport q hq h c) (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)

/-- Every sharp daughter side is an actual positive original subsegment. -/
theorem historicalSharpPolygon_edge_interior
    (i : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 (sharpSupport q hq h c)
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩))))
    (x : PlanarPoint ℝ) (hx : edgeInterior (historicalSharpPolygon q hq h c hc R) i x) :
    edgeInterior q (DaughterFirstReturn.daughterCarrier q hq.g2 (sharpSupport q hq h c)
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) i) x :=
  DaughterClosedContainment.daughter_interior_on_parent q hq (sharpSupport q hq h c) _
    (sharpInterval_root_retained q hq h c hc R) i x hx

def historicalSharpPolygonCrossingMap
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) : PolygonCrossing q :=
  Classical.choose (DaughterClosedContainment.daughter_crossing_original_pair q hq
    (sharpSupport q hq h c) _ (sharpInterval_root_retained q hq h c hc R)
    (sharpSupport_nonalternating q hq h c) d)

theorem historicalSharpPolygonCrossingMap_point
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) :
    crossingPoint q (historicalSharpPolygonCrossingMap q hq h c hc R d) =
      crossingPoint (historicalSharpPolygon q hq h c hc R) d :=
  (Classical.choose_spec (DaughterClosedContainment.daughter_crossing_original_pair q hq
    (sharpSupport q hq h c) _ (sharpInterval_root_retained q hq h c hc R)
    (sharpSupport_nonalternating q hq h c) d)).2

/-- The produced map is injective on the original fixed-opening AUX domain;
no daughter G1 is supplied as a separate premise. -/
theorem historicalSharpPolygonCrossingMap_injective
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq)) :
    Function.Injective (historicalSharpPolygonCrossingMap q hq h c hc R) := by
  intro d e hde
  apply crossingPoint_injective (historicalSharpPolygon q hq h c hc R)
    (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux).g2
  rw [←historicalSharpPolygonCrossingMap_point q hq h c hc R d,
    ←historicalSharpPolygonCrossingMap_point q hq h c hc R e,hde]
end DirectGLSSW.HOMFLY.ProcessedExposedChild
