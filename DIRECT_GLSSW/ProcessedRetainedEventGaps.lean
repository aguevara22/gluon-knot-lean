import ProcessedRetainedEventMap
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

open DaughterFirstReturn
/-- Every mapped event lies in the precise finite gap indexed by its actual
retained-polygon outgoing edge. -/
theorem retainedEventMap_in_gap
    (x : PolygonEvent (historicalSharpPolygon q hq h c hc R)) :
    ∃ k : ℕ,
      k < cornerGap q hq.g2 (sharpSupport q hq h c)
        (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)
        (cornerEnumeration q hq.g2 (sharpSupport q hq h c)
          (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) (polygonEventEdge _ x)).val
        (cornerSuccessor q hq.g2 (sharpSupport q hq h c)
          (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)
          (cornerEnumeration q hq.g2 (sharpSupport q hq h c)
            (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) (polygonEventEdge _ x))).val ∧
      retainedEventMap q hq h c hc R x =
        (DartPerm q hq.g2 (sharpSupport q hq h c)^k)
          (orbitEventAt q hq.g2 (sharpSupport q hq h c)
            (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)
            (cornerEnumeration q hq.g2 (sharpSupport q hq h c)
              (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) (polygonEventEdge _ x)).val) := by
  let S := sharpSupport q hq h c
  let root := sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩
  have hr := sharpInterval_root_retained q hq h c hc R
  rcases x with i | ⟨d,b⟩
  · exact ⟨0,(cornerSuccessor_is_firstReturn q hq.g2 S hq.size_ge_three root hr
      (cornerEnumeration q hq.g2 S root i)).1,rfl⟩
  · obtain ⟨j,k,hk0,hk,hx⟩ := nonretained_event_in_cornerGap q hq.g2 S root hr
      (retainedEventMap q hq h c hc R (Sum.inr (d,b)))
      (retainedEventMap_mem q hq h c hc R _) (retainedEventMap_visit_nonretained q hq h c hc R d b)
    have hjedge := (orbitPrefix_edge_parameter q hq.g2 S hq.size_ge_three root hr
      (cornerEnumeration q hq.g2 S root j) k hk).1
    have hj : daughterCarrier q hq.g2 S root j = daughterCarrier q hq.g2 S root
        (polygonEventEdge _ (Sum.inr (d,b))) := by
      change polygonEventEdge q (orbitEventAt q hq.g2 S root (cornerEnumeration q hq.g2 S root j).val) = _
      rw [←hjedge,←hx]
      exact retainedEventMap_carrier q hq h c hc R _
    have hji := daughterCarrier_injective q hq.g2 S hq.size_ge_three
      (sharpSupport_nonalternating q hq h c) root hj
    subst j
    exact ⟨k,hk,hx⟩
end DirectGLSSW.HOMFLY.ProcessedExposedChild
