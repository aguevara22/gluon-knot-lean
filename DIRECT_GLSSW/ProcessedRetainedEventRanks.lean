import ProcessedRetainedEventGaps
import RetainedGapRank
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
def retainedEventCoordinate
    (x : PolygonEvent (historicalSharpPolygon q hq h c hc R)) :
    OrbitCoord q hq.g2 (sharpSupport q hq h c)
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) :=
  (orbitEnumeration (DartPerm q hq.g2 (sharpSupport q hq h c))
    (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)).symm
      ⟨retainedEventMap q hq h c hc R x,retainedEventMap_mem q hq h c hc R x⟩

theorem retainedEventCoordinate_gap
    (x : PolygonEvent (historicalSharpPolygon q hq h c hc R)) :
    let j := cornerEnumeration q hq.g2 (sharpSupport q hq h c)
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) (polygonEventEdge _ x)
    ∃ k : ℕ,
      k < cornerGap q hq.g2 (sharpSupport q hq h c)
        (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) j.val
        (cornerSuccessor q hq.g2 (sharpSupport q hq h c)
          (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) j).val ∧
      retainedEventMap q hq h c hc R x =
        (DartPerm q hq.g2 (sharpSupport q hq h c)^k)
          (orbitEventAt q hq.g2 (sharpSupport q hq h c)
            (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) j.val) ∧
      (retainedEventCoordinate q hq h c hc R x).val = j.val.val+k := by
  obtain ⟨k,hk,hx⟩ := retainedEventMap_in_gap q hq h c hc R x
  refine ⟨k,hk,hx,?_⟩
  have hh := (cornerGap_offset_rank q hq.g2 (sharpSupport q hq h c) _
    (sharpInterval_root_retained q hq h c hc R) _ k hk).2
  have heq : (⟨retainedEventMap q hq h c hc R x,retainedEventMap_mem q hq h c hc R x⟩ :
      Fibre (DartPerm q hq.g2 (sharpSupport q hq h c)) (sharpIntervalComponent q hq h c hc R)) =
      cornerGap_offset_fibre q hq.g2 (sharpSupport q hq h c) _
        (cornerEnumeration q hq.g2 (sharpSupport q hq h c)
          (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) (polygonEventEdge _ x)) k :=
    Subtype.ext hx
  unfold retainedEventCoordinate
  rw [heq]
  exact hh
end DirectGLSSW.HOMFLY.ProcessedExposedChild
