import FirstDetachedChildCrossingEquiv

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open HOMFLY.PolygonDrawing HOMFLY.PolygonDrawingBridge
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hQ : CyclicGeneric q) (hR : Regular q)

/-- Same-edge polygon inclusion preserves every actual physical visit comparison. -/
theorem polygonArcVisit_lt_iff (v w : Visit q) :
    (polygonEventOrder q hQ.g2).lt
      (Sum.inr (polygonCrossingOfArc q v.1,v.2)) (Sum.inr (polygonCrossingOfArc q w.1,w.2)) ↔
    (eventOrder q hR.noTriple).lt (Sum.inr v) (Sum.inr w) := by
  rw [polygonEvent_lt_iff,event_lt_iff]
  change (crossingVisitEdge q (polygonCrossingOfArc q v.1,v.2) < crossingVisitEdge q (polygonCrossingOfArc q w.1,w.2) ∨
    crossingVisitEdge q (polygonCrossingOfArc q v.1,v.2) = crossingVisitEdge q (polygonCrossingOfArc q w.1,w.2) ∧
    crossingVisitParameter q (polygonCrossingOfArc q v.1,v.2) < crossingVisitParameter q (polygonCrossingOfArc q w.1,w.2)) ↔ _
  rw [polygonCrossingOfArc_visitParameter q hQ hR v.1 v.2,polygonCrossingOfArc_visitParameter q hQ hR w.1 w.2]
  rcases v with ⟨d,z⟩;rcases w with ⟨e,u⟩
  cases z <;> cases u <;>
    simp only [crossingVisitEdge,polygonCrossingOfArc,edgeTag,parameter,visitEdge,
      Bool.false_eq_true,eq_self_iff_true,if_false,if_true,Fin.castSucc_inj,Fin.lt_iff_val_lt_val,Fin.val_inj] <;> rfl

/-- Actual original polygon incoming ports have exactly the sharp child's visit order. -/
theorem child_original_incoming_lt_iff
    (c : Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a)
    (d e : PolygonCrossing (child q hR c hfirst hcut)) (i j : Fin 2) :
    (polygonEventOrder q hQ.g2).lt
      (HOMFLY.PolygonDrawing.incoming q hQ (polygonCrossingOfArc q (childCrossingToOriginal q hR c hfirst hcut d)) i)
      (HOMFLY.PolygonDrawing.incoming q hQ (polygonCrossingOfArc q (childCrossingToOriginal q hR c hfirst hcut e)) j) ↔
    (polygonEventOrder (child q hR c hfirst hcut) (child_noTriple q hR c hfirst hcut)).lt
      (visit (child q hR c hfirst hcut) d i) (visit (child q hR c hfirst hcut) e j) := by
  rw [polygon_incoming_lt_iff_visit_lt]
  exact (polygonArcVisit_lt_iff q hQ hR
    (childVisitMap q hR c hfirst hcut (d,if i=0 then false else true))
    (childVisitMap q hR c hfirst hcut (e,if j=0 then false else true))).trans
    (childVisitMap_lt q hR c hfirst hcut (d,if i=0 then false else true) (e,if j=0 then false else true))
end DirectGLSSW.ActiveArc.Split
