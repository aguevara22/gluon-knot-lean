import ProcessedSharpPolygonCrossings
set_option autoImplicit false
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

theorem historicalSharpPolygonCrossingMap_carriers
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) :
    let f := DaughterFirstReturn.daughterCarrier q hq.g2 (sharpSupport q hq h c)
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)
    ((historicalSharpPolygonCrossingMap q hq h c hc R d).val.1 = f d.val.1 ∧
     (historicalSharpPolygonCrossingMap q hq h c hc R d).val.2 = f d.val.2) ∨
    ((historicalSharpPolygonCrossingMap q hq h c hc R d).val.1 = f d.val.2 ∧
     (historicalSharpPolygonCrossingMap q hq h c hc R d).val.2 = f d.val.1) :=
  (Classical.choose_spec (DaughterClosedContainment.daughter_crossing_original_pair q hq
    (sharpSupport q hq h c) _ (sharpInterval_root_retained q hq h c hc R)
    (sharpSupport_nonalternating q hq h c) d)).1

theorem historicalSharpPolygon_tangent_positive
    (i : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 (sharpSupport q hq h c)
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)))) :
    ∃ a : ℝ, 0 < a ∧ cyclicTangent (historicalSharpPolygon q hq h c hc R) i =
      a • cyclicTangent q (DaughterFirstReturn.daughterCarrier q hq.g2 (sharpSupport q hq h c)
        (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) i) := by
  obtain ⟨ha,hv⟩ := DaughterFirstReturn.daughterSide_positive_multiple q hq.g2
    (sharpSupport q hq h c) hq.size_ge_three _ (sharpInterval_root_retained q hq h c hc R) i
  exact ⟨_,ha,hv⟩
end DirectGLSSW.HOMFLY.ProcessedExposedChild
