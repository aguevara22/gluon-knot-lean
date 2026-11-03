import ActiveArcEventFirstDirection
import ActiveArcRetainedVisitEdge

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords PhysicalSegments

/-- Actual event-word boundary geometry from the finite right-visit gap.
The two explicit order hypotheses are the remaining combinatorial producer
obligation; no side-incidence or transversality conclusion is assumed. -/
theorem eventOpenWord_genuine_side_of_right_visit_interval
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (U : Support q hR) (hu : c ∉ U.val)
    (k : ℕ) (hk : 0<k) (hkn : k+1<openCount q hR U.val)
    (hv0 : (eventOrder q hR.noTriple).lt
      (pairing q U.val (cornerEvent q hR U.val (start q) ⟨k,by change k<openCount q hR U.val; omega⟩)) (Sum.inr (c,true)))
    (hv1 : (eventOrder q hR.noTriple).lt (Sum.inr (c,true))
      (cornerEvent q hR U.val (start q) ⟨k+1,hkn⟩)) :
    (∃ s : ℝ, 0<s ∧ s<1 ∧ eventOpenWord q hR U c 0 =
      affinePoint (eventOpenWord q hR U c k) (eventOpenWord q hR U c (k+1)) s) ∧
    planarDet (eventOpenWord q hR U c 1-eventOpenWord q hR U c 0)
      (eventOpenWord q hR U c (k+1)-eventOpenWord q hR U c k) ≠ 0 := by
  let i : Fin (openCount q hR U.val) := ⟨k,by omega⟩
  let z := enumeration q hR U.val (start q) i
  have hz : eventAt q hR U.val (start q) z.val ≠ terminal q :=
    open_nonlast_ne_terminal q hR U.val i hkn
  have hv1' : (eventOrder q hR.noTriple).lt (Sum.inr (c,true))
      (eventAt q hR U.val (start q) (nextCorner q hR U.val (start q) z).val) := by
    rw [open_nextCorner_event q hR U.val i hkn]
    exact hv1
  obtain ⟨s,hs0,hs1,hcross⟩ := retained_visit_interval_interior q hR U.val (start q) z hz
    (c,true) hv0 hv1'
  obtain ⟨a,b,ha,hab,hb,hpa,hpb⟩ := retained_visit_interval_subsegment q hR U.val (start q) z hz
    (c,true) hv0 hv1'
  rw [open_nextCorner_event q hR U.val i hkn] at hcross hpb
  have hWk := eventOpenWord_pos q hR U c k hk (by omega)
  have hWk1 := eventOpenWord_pos q hR U c (k+1) (by omega) hkn
  have hpa' : eventOpenWord q hR U c k = affinePoint (q c.val.2.castSucc) (q c.val.2.succ) a :=
    hWk.trans hpa
  have hpb' : eventOpenWord q hR U c (k+1) = affinePoint (q c.val.2.castSucc) (q c.val.2.succ) b :=
    hWk1.trans hpb
  constructor
  · refine ⟨s,hs0,hs1,?_⟩
    rw [eventOpenWord_zero,hWk,hWk1]
    exact hcross
  · exact eventOpenWord_crossed_subsegment_transverse q hR c hc U hu k a b hab hpa' hpb'

end DirectGLSSW.ActiveArc.Primitive
