import HistoricalChildFirstReturn
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry
open ActualLocalSupports LocalCoordinates DaughterFirstReturn
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


include he hAux in
theorem historicalChildLift_map_mem_iff
    (S : Finset (PolygonCrossing (historicalSharpPolygon q hq h c hc R)))
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) :
    historicalSharpPolygonCrossingMap q hq h c hc R d ∈ historicalChildLift q hq h c hc R S ↔ d∈S := by
  constructor
  · intro hd
    obtain ⟨e,heS,hed⟩ := Finset.mem_image.mp hd
    have hed' := historicalSharpPolygonCrossingMap_injective q hq h c hc R he hAux hed
    exact hed' ▸ heS
  · intro hd
    exact Finset.mem_image.mpr ⟨d,hd,rfl⟩

include he hAux in
theorem retainedEventMap_retained_iff
    (S : Finset (PolygonCrossing (historicalSharpPolygon q hq h c hc R)))
    (x : PolygonEvent (historicalSharpPolygon q hq h c hc R)) :
    retainedCorner q (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S)
      (retainedEventMap q hq h c hc R x) ↔
    retainedCorner (historicalSharpPolygon q hq h c hc R) S x := by
  rcases x with i | ⟨d,b⟩
  · have hr := (cornerEnumeration q hq.g2 (sharpSupport q hq h c)
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) i).property
    change retainedCorner q _ (orbitEventAt q hq.g2 (sharpSupport q hq h c) _ _) ↔ True
    refine ⟨fun _ => trivial,fun _ => ?_⟩
    generalize hz : orbitEventAt q hq.g2 (sharpSupport q hq h c)
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)
      (cornerEnumeration q hq.g2 (sharpSupport q hq h c)
        (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) i).val=z at hr ⊢
    cases z with
    | inl a => trivial
    | inr v => exact Finset.mem_union_left _ hr
  · have hn := retainedEventMap_visit_nonretained q hq h c hc R d b
    simp only [retainedEventMap,PolygonDrawing.visit] at hn ⊢
    split_ifs at hn ⊢ <;> simp only [retainedCorner] at hn ⊢ <;>
      simpa only [Finset.mem_union,hn,false_or] using
        historicalChildLift_map_mem_iff q hq h c hc R he hAux S d

theorem retained_refinement_event_in_range
    (S : Finset (PolygonCrossing (historicalSharpPolygon q hq h c hc R)))
    (x : PolygonEvent q)
    (hx : componentOf (smoothingDartPermutation q hq.g2 (sharpSupport q hq h c)) x =
      sharpIntervalComponent q hq h c hc R)
    (hr : retainedCorner q (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S) x) :
    x ∈ Set.range (retainedEventMap q hq h c hc R) := by
  rcases x with i | ⟨d,b⟩
  · obtain ⟨j,hj⟩ := retainedEventMap_oldCorner_preimage q hq h c hc R (Sum.inl i) hx trivial
    exact ⟨Sum.inl j,hj⟩
  · rcases Finset.mem_union.mp hr with hd | hd
    · obtain ⟨j,hj⟩ := retainedEventMap_oldCorner_preimage q hq h c hc R (Sum.inr (d,b)) hx hd
      exact ⟨Sum.inl j,hj⟩
    · obtain ⟨e,heS,hed⟩ := Finset.mem_image.mp hd
      refine ⟨PolygonDrawing.visit _ e (historicalSharpBranchPermutation q hq h c hc R e
        (if b then 1 else 0)),?_⟩
      rw [retainedEventMap_matched_visit,hed]
      cases b <;> simp only [PolygonDrawing.visit,ite_false,ite_true] <;> norm_num
end DirectGLSSW.HOMFLY.ProcessedExposedChild
