import DaughterSideEventMembership
import ProcessedSharpCrossingPreimages
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

/-- Every sharp-polygon crossing has both original visits in the actual
selected interval. The carrier pair may occur in either order. -/
theorem historicalSharpPolygonCrossingMap_visits
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) (b : Bool) :
    componentOf (DaughterFirstReturn.DartPerm q hq.g2 (sharpSupport q hq h c))
      (Sum.inr (historicalSharpPolygonCrossingMap q hq h c hc R d,b)) =
        sharpIntervalComponent q hq h c hc R := by
  let Q := historicalSharpPolygon q hq h c hc R
  let f := DaughterFirstReturn.daughterCarrier q hq.g2 (sharpSupport q hq h c)
    (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)
  let z := historicalSharpPolygonCrossingMap q hq h c hc R d
  have hm (i : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 (sharpSupport q hq h c)
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩))))
      (he : crossingVisitEdge q (z,b)=f i)
      (hi : edgeInterior Q i (crossingPoint Q d)) :
      componentOf (DaughterFirstReturn.DartPerm q hq.g2 (sharpSupport q hq h c))
        (Sum.inr (z,b)) = sharpIntervalComponent q hq h c hc R := by
    apply DaughterClosedContainment.daughter_side_event_membership q hq (sharpSupport q hq h c)
      _ (sharpInterval_root_retained q hq h c hc R) i (Sum.inr (z,b)) he
    change edgeInterior Q i (crossingPoint q z)
    rw [historicalSharpPolygonCrossingMap_point]
    exact hi
  rcases historicalSharpPolygonCrossingMap_carriers q hq h c hc R d with hp | hp
  · cases b
    · exact hm d.val.1 hp.1 (crossingPoint_mem_left Q d)
    · exact hm d.val.2 hp.2 (crossingPoint_mem_right Q d)
  · cases b
    · exact hm d.val.2 hp.1 (crossingPoint_mem_right Q d)
    · exact hm d.val.1 hp.2 (crossingPoint_mem_left Q d)

/-- Actual map into the historical sharp crossing carrier, with selected
crossings excluded by the proved nonalternating singleton geometry. -/
def historicalSharpPolygonToCrossing
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) :
    SharpDaughter.Crossing q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R) := by
  let z := crossingFin q (historicalSharpPolygonCrossingMap q hq h c hc R d)
  have hm : ∀ i : Fin 2, componentOf (SharpDaughter.P q hq (sharpSupport q hq h c))
      ((eventFin q).symm ((SharpDaughter.Parent q hq).outgoing z i)) =
        sharpIntervalComponent q hq h c hc R := by
    intro i
    fin_cases i
    · simpa only [z,SharpDaughter.outgoing_event,Equiv.symm_apply_apply,PolygonDrawing.visit,ite_true]
        using historicalSharpPolygonCrossingMap_visits q hq h c hc R d false
    · simpa only [z,SharpDaughter.outgoing_event,Equiv.symm_apply_apply,PolygonDrawing.visit,ite_false]
        using historicalSharpPolygonCrossingMap_visits q hq h c hc R d true
  exact ⟨z,SharpDaughter.both_visits_not_selected q hq (sharpSupport q hq h c)
    (sharpIntervalComponent q hq h c hc R) (sharpSupport_nonalternating q hq h c) z hm,hm⟩

theorem historicalSharpPolygonToCrossing_val
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) :
    (historicalSharpPolygonToCrossing q hq h c hc R d).val =
      crossingFin q (historicalSharpPolygonCrossingMap q hq h c hc R d) := rfl
end DirectGLSSW.HOMFLY.ProcessedExposedChild
