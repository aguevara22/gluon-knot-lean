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
/-- On each retained edge, actual event parameters are related to the original
carrier parameters by a produced strictly increasing affine map. -/
theorem retainedEventMap_parameter_affine
    (i : Fin (Fintype.card (CornerCoord q hq.g2 (sharpSupport q hq h c)
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)))) :
    ∃ s t : ℝ, s<t ∧ ∀ x : PolygonEvent (historicalSharpPolygon q hq h c hc R),
      polygonEventEdge _ x=i →
      polygonEventParameter q (retainedEventMap q hq h c hc R x) =
        (1-polygonEventParameter _ x)*s+polygonEventParameter _ x*t := by
  let Q := historicalSharpPolygon q hq h c hc R
  let e := daughterCarrier q hq.g2 (sharpSupport q hq h c)
    (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) i
  obtain ⟨s,t,_,hst,_,hs,ht⟩ := DaughterClosedContainment.daughterSide_endpoint_parameters q hq.g2
    (sharpSupport q hq h c) hq.size_ge_three _ (sharpInterval_root_retained q hq h c hc R) i
  refine ⟨s,t,hst,?_⟩
  intro x he
  have hxedge : polygonEventEdge q (retainedEventMap q hq h c hc R x)=e := by
    rw [retainedEventMap_carrier,he]
  have hab : q e≠q (cyclicSuccessor e) := by
    intro hh
    exact (cyclicSuccessor_ne_self (by have := hq.size_ge_three;omega) e)
      ((cyclicNoncollinear_injective hq.size_ge_three q hq.g1 hh).symm)
  apply affinePoint_injective (q e) (q (cyclicSuccessor e)) hab
  have hm := polygonEventPoint_eq_affine q (retainedEventMap q hq h c hc R x)
  rw [hxedge] at hm
  rw [←hm,retainedEventMap_point,polygonEventPoint_eq_affine Q x,he]
  change Q i = affinePoint (q e) (q (cyclicSuccessor e)) s at hs
  change Q (cyclicSuccessor i) = affinePoint (q e) (q (cyclicSuccessor e)) t at ht
  rw [hs,ht]
  ext <;> simp [affinePoint] <;> ring

theorem retainedEventMap_same_edge_parameter_lt_iff
    (x y : PolygonEvent (historicalSharpPolygon q hq h c hc R))
    (he : polygonEventEdge _ x=polygonEventEdge _ y) :
    polygonEventParameter q (retainedEventMap q hq h c hc R x) <
      polygonEventParameter q (retainedEventMap q hq h c hc R y) ↔
    polygonEventParameter _ x < polygonEventParameter _ y := by
  obtain ⟨s,t,hst,hf⟩ := retainedEventMap_parameter_affine q hq h c hc R (polygonEventEdge _ y)
  rw [hf x he,hf y rfl]
  constructor <;> intro hh <;> nlinarith
end DirectGLSSW.HOMFLY.ProcessedExposedChild
