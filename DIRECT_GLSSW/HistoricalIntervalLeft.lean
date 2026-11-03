import ProcessedSelectedOriginalOver
import PositivePolygonTurns
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

/-- Every literal turn in the original detached interval is nonnegative.
Only its final turn differs from original continuation, and it is the actual
positive over-to-under selected corner. -/
theorem historical_interval_det_nonneg
    (hleft : ∀ i : Fin (n+2),0<planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (j : Fin (detachedOrbitSize t c R-1)) :
    0≤planarDet
      (arcVector (positivePolygonEventDiagram q hq) (h.detachedOriginalArc c hc R j))
      (arcVector (positivePolygonEventDiagram q hq) (h.detachedOriginalArc c hc R (cyclicSuccessor j))) := by
  by_cases hj : j=detachedLastOldIndex c R
  · subst j
    have hz : cyclicSuccessor (detachedLastOldIndex c R)=⟨0,detachedOldOrbitSize_pos c R⟩ := by
      apply Fin.ext
      change (detachedOrbitSize t c R-2+1) % (detachedOrbitSize t c R-1)=0
      have he : detachedOrbitSize t c R-2+1=detachedOrbitSize t c R-1 := by
        have := detachedOldOrbitSize_pos c R;omega
      rw [he,Nat.mod_self]
    rw [hz,h.detachedOriginalArc_last,h.detachedOriginalArc_first]
    apply le_of_lt
    apply positive_crossing_exchange_left _ _ _ _ (positivePolygonEventDiagram_crossingSign q hq _)
    have hover : t.1.overBranch c=(positivePolygonEventDiagram q hq).overBranch (h.crossingOrigin c) :=
      h.bad_crossing_original_over c hc
    rw [←hover]
    exact hc
  · have hlt : j.val+1<detachedOrbitSize t c R-1 := by
      have hn := j.isLt
      have hne : j.val≠detachedOrbitSize t c R-2 := fun he => hj (Fin.ext he)
      omega
    have hs : (cyclicSuccessor j).val=j.val+1 := Nat.mod_eq_of_lt hlt
    have hstep := h.detachedOriginalArc_successor c hc R j (cyclicSuccessor j) hs
    rw [←hstep]
    exact positivePolygonEventDiagram_turn_nonneg_of_uniform_left q hq hleft _

/-- The original dart transition on the actual detached interval has
nonnegative carrier determinant. Straight subdivisions are permitted. -/
theorem historical_dart_carrier_nonneg
    (hleft : ∀ i : Fin (n+2),0<planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (x : PolygonEvent q)
    (hx : componentOf (SharpDaughter.P q hq (sharpSupport q hq h c)) x =
      sharpIntervalComponent q hq h c hc R) :
    0≤planarDet (cyclicTangent q (polygonEventEdge q x))
      (cyclicTangent q (polygonEventEdge q (SharpDaughter.P q hq (sharpSupport q hq h c) x))) := by
  obtain ⟨j,hj⟩ := (sharpInterval_mem_iff q hq h c hc R x).mp hx
  have hxj : x=sharpIntervalEvent q hq h c hc R j := by
    apply (eventFin q).injective
    simpa only [sharpIntervalEvent,Equiv.apply_symm_apply] using hj.symm
  have hh := historical_interval_det_nonneg q hq h c hc R hleft j
  have ha : h.detachedOriginalArc c hc R j=eventFin q x := hj
  have hb : h.detachedOriginalArc c hc R (cyclicSuccessor j)=
      eventFin q (SharpDaughter.P q hq (sharpSupport q hq h c) x) := by
    rw [hxj,sharpIntervalEvent_step]
    simp only [sharpIntervalEvent,Equiv.apply_symm_apply]
  rw [ha,hb,positivePolygonEventDiagram_arcVector,positivePolygonEventDiagram_arcVector] at hh
  have he : planarDet
      (PolygonDrawing.stepScale q hq x • cyclicTangent q (polygonEventEdge q x))
      (PolygonDrawing.stepScale q hq (SharpDaughter.P q hq (sharpSupport q hq h c) x) •
        cyclicTangent q (polygonEventEdge q (SharpDaughter.P q hq (sharpSupport q hq h c) x))) =
      (PolygonDrawing.stepScale q hq x * PolygonDrawing.stepScale q hq (SharpDaughter.P q hq (sharpSupport q hq h c) x)) *
        planarDet (cyclicTangent q (polygonEventEdge q x))
          (cyclicTangent q (polygonEventEdge q (SharpDaughter.P q hq (sharpSupport q hq h c) x))) := by
    simp [planarDet];ring
  rw [he] at hh
  exact (mul_nonneg_iff_of_pos_left (mul_pos (PolygonDrawing.stepScale_pos q hq x)
    (PolygonDrawing.stepScale_pos q hq _))).mp hh
end DirectGLSSW.HOMFLY.ProcessedExposedChild
