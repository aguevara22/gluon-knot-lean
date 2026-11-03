import GeometricCursorCrossingEquiv
import PhysicalCursorEvent
import PhysicalParentFutureFilter
import PositivePolygonInitialEncounter
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open PermutationOrbits PolygonDrawingBridge PolygonDrawing SmoothingCornerGeometry EventSegmentGeometry
open ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable

/-- The first physical event has no earlier bad crossing in the actual stored
knot traversal. This is derived in the forward direction from the complete
common crossing map and the actual minimum physical parameter. -/
theorem GeometricCursor.first_good_before {n m : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q) (he : LeftExposed q 0)
    (p : Fin (m+2) → PlanarPoint ℝ) (t : MarkedParentState)
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (C : GeometricCursor q hq p t h) (c : ActiveArc.Crossing p)
    (hc : ActiveArc.Cursor.FirstCrossing p c) :
    MarkedG.GoodBefore t ((C.crossingEquiv he) c).val := by
  letI : LinearOrder (Fin (n+2) ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq.g2
  rcases C with ⟨a,B,A,hs,θ,hθ0,hθ1,hcarrier,hlo,hhi,rfl⟩
  let P := ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) A m hs) θ
  let F := boundaryPhysicalCrossingEquiv q hq he h a B A m hs θ hcarrier hlo hhi
  let Z (z : ActiveArc.Crossing P) :=
    (ActiveArc.Split.suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq)
      A m hs θ hθ0 hθ1 z).val
  let D (z : ActiveArc.Crossing P) := exposedCrossingEquiv q 0 hq he (Z z)
  have horigin (z : ActiveArc.Crossing P) : h.crossingOrigin (F z).val=crossingFin q (D z) :=
    boundaryPhysicalCrossingEquiv_origin q hq he h a B A m hs θ hcarrier hlo hhi z
  have hfirst (z : ActiveArc.Crossing P) : firstVisitedBranch t.2.1 (F z).val=0 := by
    rw [h.boundaryCrossing_firstVisitedBranch a B (F z),horigin z]
    exact initialAnchorTraversal_firstVisitedBranch q hq (D z)
  change MarkedG.GoodBefore t (F c).val
  intro d hbefore hd
  let d' : SuffixCrossing t a := B.badSuffix d hd
  let z : ActiveArc.Crossing P := F.symm d'
  have hz : (F z).val=d := congrArg Subtype.val (F.apply_symm_apply d')
  rw [← hz,hfirst z,hfirst c] at hbefore
  have hpos := (marked_rankBefore_iff t _ _).mp hbefore
  have hold := (h.boundaryCrossing_visit_order a B (F z) (F c) 0 0).mp hpos
  rw [horigin z,horigin c] at hold
  have hvisit : visit q (D z) 0 < visit q (D c) 0 :=
    (PhysicalParentHistory.initial_incoming_strict_order q hq (D z) (D c) 0 0).mp hold
  have hedge (w : ActiveArc.Crossing P) :
      (polygonEventEdge q (visit q (D w) 0)).val=A+w.val.1.val+1 := by
    change (D w).val.1.val=_
    rw [exposedCrossing_firstEdge]
    have hh := ActiveArc.Split.suffixWordCrossingEquiv_left_label
      (cutArc q 0) (cutArc_regular q 0 hq) A m hs θ hθ0 hθ1 w
    change (Z w).val.1.val=A+w.val.1.val at hh
    rw [hh]
  have hc0 : c.val.1.val=0 := congrArg Fin.val hc.1
  rcases (polygonEvent_lt_iff q hq.g2 _ _).mp hvisit with hedgeLt|⟨hedgeEq,hparam⟩
  · have hv := hedgeLt
    change (polygonEventEdge q (visit q (D z) 0)).val <
      (polygonEventEdge q (visit q (D c) 0)).val at hv
    rw [hedge z,hedge c,hc0] at hv
    omega
  · have hv := congrArg Fin.val hedgeEq
    rw [hedge z,hedge c,hc0] at hv
    have hz0 : z.val.1=0 := Fin.ext (by simpa only [Fin.val_zero] using (show z.val.1.val=0 by omega))
    have hzp := (physical_first_original_event q hq he A hs θ hθ0 hθ1 z hz0).2
    have hcp := (physical_first_original_event q hq he A hs θ hθ0 hθ1 c hc.1).2
    change polygonEventParameter q (visit q (D z) 0)=θ+(1-θ)*ActiveArc.leftParameter P z at hzp
    change polygonEventParameter q (visit q (D c) 0)=θ+(1-θ)*ActiveArc.leftParameter P c at hcp
    rw [hzp,hcp] at hparam
    have hmin := hc.2 z hz0
    have hmul := mul_le_mul_of_nonneg_left hmin (sub_nonneg.mpr (le_of_lt hθ1))
    linarith


end DirectGLSSW.HOMFLY.PhysicalCursorComparison
