import ProcessedRetainedEventRanks
import ProcessedRetainedParameters
import DaughterGapParameterOrder
import DaughterGapOrderBounds
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

theorem retainedEventCoordinate_lt_of_edge_lt
    (x y : PolygonEvent (historicalSharpPolygon q hq h c hc R))
    (hxy : polygonEventEdge _ x<polygonEventEdge _ y) :
    retainedEventCoordinate q hq h c hc R x < retainedEventCoordinate q hq h c hc R y := by
  obtain ⟨k,hk,_,hrx⟩ := retainedEventCoordinate_gap q hq h c hc R x
  obtain ⟨l,_,_,hry⟩ := retainedEventCoordinate_gap q hq h c hc R y
  have hj := (cornerEnumeration q hq.g2 (sharpSupport q hq h c)
    (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)).strictMono hxy
  have hh := cornerGap_offset_lt_later q hq.g2 (sharpSupport q hq h c) _ _ _ hj k hk
  change (retainedEventCoordinate q hq h c hc R x).val < (retainedEventCoordinate q hq h c hc R y).val
  rw [hrx,hry]
  omega

/-- The physical event map preserves and reflects the full original dart
rank order. This is produced from actual gap membership and affine parameter
order, not supplied as a correspondence hypothesis. -/
theorem retainedEventCoordinate_order
    (x y : PolygonEvent (historicalSharpPolygon q hq h c hc R)) :
    retainedEventCoordinate q hq h c hc R x < retainedEventCoordinate q hq h c hc R y ↔
      polygonEventEdge _ x<polygonEventEdge _ y ∨
      (polygonEventEdge _ x=polygonEventEdge _ y ∧ polygonEventParameter _ x<polygonEventParameter _ y) := by
  rcases lt_trichotomy (polygonEventEdge _ x) (polygonEventEdge _ y) with hlt | he | hgt
  · exact ⟨fun _ => Or.inl hlt,fun _ => retainedEventCoordinate_lt_of_edge_lt q hq h c hc R x y hlt⟩
  · obtain ⟨k,hk,hx,hrx⟩ := retainedEventCoordinate_gap q hq h c hc R x
    obtain ⟨l,hl,hy,hry⟩ := retainedEventCoordinate_gap q hq h c hc R y
    rw [←he] at hl hy hry
    have hp := retainedEventMap_same_edge_parameter_lt_iff q hq h c hc R x y he
    rw [hx,hy] at hp
    have hgap := DaughterClosedContainment.gap_offset_parameter_lt_iff q hq (sharpSupport q hq h c)
      _ (sharpInterval_root_retained q hq h c hc R) _ k l hk hl
    have hkl : k<l ↔ polygonEventParameter _ x<polygonEventParameter _ y := hgap.symm.trans hp
    constructor
    · intro hh
      refine Or.inr ⟨he,hkl.mp ?_⟩
      change (retainedEventCoordinate q hq h c hc R x).val < (retainedEventCoordinate q hq h c hc R y).val at hh
      rw [hrx,hry] at hh
      omega
    · intro hh
      rcases hh with hbad | ⟨_,hh⟩
      · exact ((ne_of_lt hbad) he).elim
      · have hh' := hkl.mpr hh
        change (retainedEventCoordinate q hq h c hc R x).val < (retainedEventCoordinate q hq h c hc R y).val
        rw [hrx,hry]
        omega
  · constructor
    · intro hh
      exact ((not_lt_of_ge (retainedEventCoordinate_lt_of_edge_lt q hq h c hc R y x hgt).le) hh).elim
    · intro hh
      rcases hh with hbad | ⟨hbad,_⟩
      · exact (lt_asymm hbad hgt).elim
      · exact ((ne_of_lt hgt) hbad.symm).elim
end DirectGLSSW.HOMFLY.ProcessedExposedChild
