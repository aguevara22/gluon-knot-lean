import ProcessedSharpBranchData
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

/-- Literal retained-polygon event to the original singleton dart event.
Crossing visits use the produced inverse branch permutation. -/
def retainedEventMap : PolygonEvent (historicalSharpPolygon q hq h c hc R) → PolygonEvent q
  | Sum.inl i => DaughterFirstReturn.orbitEventAt q hq.g2 (sharpSupport q hq h c)
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)
      (DaughterFirstReturn.cornerEnumeration q hq.g2 (sharpSupport q hq h c)
        (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) i).val
  | Sum.inr (d,b) => PolygonDrawing.visit q (historicalSharpPolygonCrossingMap q hq h c hc R d)
      ((historicalSharpBranchPermutation q hq h c hc R d).symm (if b then 1 else 0))

theorem retainedEventMap_visit
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) (i : Fin 2) :
    retainedEventMap q hq h c hc R (PolygonDrawing.visit _ d i) =
      PolygonDrawing.visit q (historicalSharpPolygonCrossingMap q hq h c hc R d)
        ((historicalSharpBranchPermutation q hq h c hc R d).symm i) := by
  fin_cases i <;> simp [PolygonDrawing.visit,retainedEventMap]

theorem retainedEventMap_matched_visit
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) (i : Fin 2) :
    retainedEventMap q hq h c hc R
      (PolygonDrawing.visit _ d (historicalSharpBranchPermutation q hq h c hc R d i)) =
      PolygonDrawing.visit q (historicalSharpPolygonCrossingMap q hq h c hc R d) i := by
  rw [retainedEventMap_visit,Equiv.symm_apply_apply]

theorem retainedEventMap_carrier
    (x : PolygonEvent (historicalSharpPolygon q hq h c hc R)) :
    polygonEventEdge q (retainedEventMap q hq h c hc R x) =
      DaughterFirstReturn.daughterCarrier q hq.g2 (sharpSupport q hq h c)
        (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)
        (polygonEventEdge _ x) := by
  rcases x with i | ⟨d,b⟩
  · rfl
  · have hh := historicalSharpBranchPermutation_carrier q hq h c hc R d
      ((historicalSharpBranchPermutation q hq h c hc R d).symm (if b then 1 else 0))
    rw [Equiv.apply_symm_apply] at hh
    cases b <;> simpa [retainedEventMap,PolygonDrawing.visit,polygonEventEdge,crossingVisitEdge] using hh.symm

theorem retainedEventMap_point
    (x : PolygonEvent (historicalSharpPolygon q hq h c hc R)) :
    polygonEventPoint q (retainedEventMap q hq h c hc R x) =
      polygonEventPoint (historicalSharpPolygon q hq h c hc R) x := by
  rcases x with i | ⟨d,b⟩
  · rfl
  · simp only [retainedEventMap,PolygonDrawing.visit]
    split_ifs <;> exact historicalSharpPolygonCrossingMap_point q hq h c hc R d

theorem retainedEventMap_mem
    (x : PolygonEvent (historicalSharpPolygon q hq h c hc R)) :
    componentOf (DaughterFirstReturn.DartPerm q hq.g2 (sharpSupport q hq h c))
      (retainedEventMap q hq h c hc R x) = sharpIntervalComponent q hq h c hc R := by
  rcases x with i | ⟨d,b⟩
  · exact (orbitEnumeration (DaughterFirstReturn.DartPerm q hq.g2 (sharpSupport q hq h c))
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)
      (DaughterFirstReturn.cornerEnumeration q hq.g2 (sharpSupport q hq h c)
        (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) i).val).property
  · simp only [retainedEventMap,PolygonDrawing.visit]
    split_ifs <;> exact historicalSharpPolygonCrossingMap_visits q hq h c hc R d _

theorem retainedEventMap_visit_nonretained
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) (b : Bool) :
    ¬DaughterFirstReturn.retainedCorner q (sharpSupport q hq h c)
      (retainedEventMap q hq h c hc R (Sum.inr (d,b))) := by
  have hn := (historicalSharpPolygonToCrossing q hq h c hc R d).property.1
  change (crossingFin q).symm (crossingFin q (historicalSharpPolygonCrossingMap q hq h c hc R d)) ∉ _ at hn
  rw [Equiv.symm_apply_apply] at hn
  simp only [retainedEventMap,PolygonDrawing.visit]
  split_ifs <;> exact hn
end DirectGLSSW.HOMFLY.ProcessedExposedChild
