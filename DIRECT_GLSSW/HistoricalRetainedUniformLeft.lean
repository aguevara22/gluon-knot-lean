import HistoricalIntervalLeft
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

open DaughterFirstReturn

theorem historicalSharpPolygon_turn_nonneg
    (hleft : ∀ i : Fin (n+2),0<planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (i : Fin (Fintype.card (CornerCoord q hq.g2 (sharpSupport q hq h c)
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)))) :
    0≤planarDet (cyclicTangent (historicalSharpPolygon q hq h c hc R) i)
      (cyclicTangent (historicalSharpPolygon q hq h c hc R) (cyclicSuccessor i)) := by
  let S := sharpSupport q hq h c
  let root := sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩
  let j := cornerEnumeration q hq.g2 S root i
  let z := lastDartStart q hq.g2 S root j
  have hr := sharpInterval_root_retained q hq h c hc R
  obtain ⟨hd,hnext,_,_,_,_⟩ := cornerSuccessor_is_firstReturn q hq.g2 S hq.size_ge_three root hr j
  have hzmem : componentOf (SharpDaughter.P q hq S) z = sharpIntervalComponent q hq h c hc R := by
    change componentOf (DartPerm q hq.g2 S) ((DartPerm q hq.g2 S ^ _) (orbitEventAt q hq.g2 S root j.val)) = _
    rw [componentOf_pow_apply]
    exact (orbitEnumeration (DartPerm q hq.g2 S) root j.val).property
  have hh := historical_dart_carrier_nonneg q hq h c hc R hleft z hzmem
  have he : polygonEventEdge q z = daughterCarrier q hq.g2 S root i :=
    (orbitPrefix_edge_parameter q hq.g2 S hq.size_ge_three root hr j
      (cornerGap q hq.g2 S root j.val (cornerSuccessor q hq.g2 S root j).val-1) (by omega)).1
  have hn : polygonEventEdge q (SharpDaughter.P q hq S z) =
      daughterCarrier q hq.g2 S root (cyclicSuccessor i) := by
    change polygonEventEdge q (nextDartStart q hq.g2 S z) = _
    rw [hnext]
    change polygonEventEdge q (orbitEventAt q hq.g2 S root (cornerSuccessor q hq.g2 S root j).val) = _
    rw [←cornerEnumeration_successor]
    rfl
  change 0≤planarDet (cyclicTangent q (polygonEventEdge q z))
    (cyclicTangent q (polygonEventEdge q (SharpDaughter.P q hq S z))) at hh
  rw [he,hn] at hh
  obtain ⟨a,ha,hva⟩ := historicalSharpPolygon_tangent_positive q hq h c hc R i
  obtain ⟨b,hb,hvb⟩ := historicalSharpPolygon_tangent_positive q hq h c hc R (cyclicSuccessor i)
  rw [hva,hvb]
  have heq : planarDet
      (a • cyclicTangent q (daughterCarrier q hq.g2 S root i))
      (b • cyclicTangent q (daughterCarrier q hq.g2 S root (cyclicSuccessor i))) =
      (a*b)*planarDet (cyclicTangent q (daughterCarrier q hq.g2 S root i))
        (cyclicTangent q (daughterCarrier q hq.g2 S root (cyclicSuccessor i))) := by
    simp [planarDet];ring
  rw [heq]
  exact mul_nonneg (mul_pos ha hb).le hh

/-- The exact historical retained polygon is uniformly left-turning after
arbitrary actual processed history. Strictness uses only its already-derived
original-opening AUX genericity; no replacement polygon is introduced. -/
theorem historicalSharpPolygon_uniform_left
    (hleft : ∀ i : Fin (n+2),0<planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq)) :
    ∀ i : Fin (Fintype.card (CornerCoord q hq.g2 (sharpSupport q hq h c)
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩))),
      0<planarDet (cyclicTangent (historicalSharpPolygon q hq h c hc R) i)
        (cyclicTangent (historicalSharpPolygon q hq h c hc R) (cyclicSuccessor i)) := by
  intro i
  have hQ := originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux
  exact lt_of_le_of_ne (historicalSharpPolygon_turn_nonneg q hq h c hc R hleft i)
    (Ne.symm (cyclic_turn_det_ne_zero hQ.size_ge_three _ hQ.g1 i))
end DirectGLSSW.HOMFLY.ProcessedExposedChild
