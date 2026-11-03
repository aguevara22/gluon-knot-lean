import ActiveArcCompatibleRightGap
import DirectGLSSW.HorizontalShortEdge

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW Cursor RetainedWords PhysicalSegments Split SingletonWords
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (hAux : Primitive.ClosedAuxiliary q hR)
variable (S : {S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
  PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
    (child_noTriple q hR c hc.1 hcut) S})
variable (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut))
include hAux

/-- The actual retained crossed side has the canonical sign of the original
right crossing edge, because its two endpoints form a positively oriented
subsegment. The retained gap is derived from the actual compatible support. -/
theorem compatible_crossed_side_sign :
    let U : Primitive.Support q hR := ⟨pieceSelections q hR c hc hcut S.val T.val,
      (pieceSelections_nonalternating_iff q hR c hc hcut S.val T.val).mpr ⟨S.property,T.property⟩⟩
    let k := (DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0)).length-1
    scalarSignValue (planarDet (q 1-q 0)
      (Primitive.eventOpenWord q hR U c (k+1)-Primitive.eventOpenWord q hR U c k)) =
    scalarSignValue (planarDet (q 1-q 0) (q c.val.2.succ-q c.val.2.castSucc)) := by
  intro U k
  obtain ⟨hk,hkn,hv0,hv1⟩ := compatible_right_visit_gap q hR c hc hcut hAux S T
  change 0<k at hk
  change k+1<openCount q hR U.val at hkn
  let i : Fin (openCount q hR U.val) := ⟨k,by omega⟩
  let z := enumeration q hR U.val (start q) i
  have hz : eventAt q hR U.val (start q) z.val ≠ terminal q :=
    open_nonlast_ne_terminal q hR U.val i hkn
  have hv1' : (eventOrder q hR.noTriple).lt (Sum.inr (c,true))
      (eventAt q hR U.val (start q) (nextCorner q hR U.val (start q) z).val) := by
    rw [open_nextCorner_event q hR U.val i hkn]
    exact hv1
  obtain ⟨s,t,hs,hst,ht,hpa,hpb⟩ := retained_visit_interval_subsegment q hR U.val (start q) z hz
    (c,true) hv0 hv1'
  rw [open_nextCorner_event q hR U.val i hkn] at hpb
  have hpa' : Primitive.eventOpenWord q hR U c k = affinePoint (q c.val.2.castSucc) (q c.val.2.succ) s :=
    (Primitive.eventOpenWord_pos q hR U c k hk (by omega)).trans hpa
  have hpb' : Primitive.eventOpenWord q hR U c (k+1) = affinePoint (q c.val.2.castSucc) (q c.val.2.succ) t :=
    (Primitive.eventOpenWord_pos q hR U c (k+1) (by omega) hkn).trans hpb
  have he : planarDet (q 1-q 0)
      (Primitive.eventOpenWord q hR U c (k+1)-Primitive.eventOpenWord q hR U c k) =
      (t-s)*planarDet (q 1-q 0) (q c.val.2.succ-q c.val.2.castSucc) := by
    rw [hpa',hpb']
    simp only [planarDet,affinePoint,Prod.fst_sub,Prod.snd_sub]
    ring
  rw [he]
  exact HorizontalShortEdge.scalarSignValue_positive_mul _ _ (sub_pos.mpr hst)

end DirectGLSSW.ActiveArc.CompatibleWords
