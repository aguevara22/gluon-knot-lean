import DaughterUnselectedCrossing
import ProcessedSharpPolygonCarriers
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

/-- Every crossing of the actual historical sharp subdivision is realized by
a crossing of its exact retained polygon, on the original opening AUX domain. -/
theorem historicalSharp_crossing_has_polygon_preimage
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))
    (d : SharpDaughter.Crossing q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R)) :
    ∃ z : PolygonCrossing (historicalSharpPolygon q hq h c hc R),
      historicalSharpPolygonCrossingMap q hq h c hc R z = (crossingFin q).symm d.val := by
  have hvis : ∀ b : Bool,
      componentOf (DaughterFirstReturn.DartPerm q hq.g2 (sharpSupport q hq h c))
        (Sum.inr ((crossingFin q).symm d.val,b)) = sharpIntervalComponent q hq h c hc R := by
    intro b
    cases b
    · simpa only [SharpDaughter.outgoing_event,PolygonDrawing.visit,ite_true] using d.property.2 0
    · simpa only [SharpDaughter.outgoing_event,PolygonDrawing.visit,ite_false] using d.property.2 1
  obtain ⟨z,hz⟩ := DaughterClosedContainment.unselected_crossing_in_daughter q hq
    (sharpSupport q hq h c) _ (sharpInterval_root_retained q hq h c hc R)
    ((crossingFin q).symm d.val) d.property.1 hvis
    (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux)
  refine ⟨z,?_⟩
  apply crossingPoint_injective q hq.g2
  exact (historicalSharpPolygonCrossingMap_point q hq h c hc R z).trans hz

/-- Actual extracted-child crossings therefore have produced sharp-polygon
preimages with the same original crossing ancestry; no surjectivity premise. -/
theorem detached_crossing_has_sharp_polygon_preimage
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))
    (d : Fin R.diagram.nCrossing) :
    ∃ z : PolygonCrossing (historicalSharpPolygon q hq h c hc R),
      crossingFin q (historicalSharpPolygonCrossingMap q hq h c hc R z) =
        h.detachedCrossingOrigin c R d := by
  let ds := (sharpCrossingIntervalEquiv q hq h c hc R).symm (h.detachedCrossingEquiv c hc R d)
  obtain ⟨z,hz⟩ := historicalSharp_crossing_has_polygon_preimage q hq h c hc R he hAux ds
  exact ⟨z,by rw [hz,Equiv.apply_symm_apply];rfl⟩
end DirectGLSSW.HOMFLY.ProcessedExposedChild
