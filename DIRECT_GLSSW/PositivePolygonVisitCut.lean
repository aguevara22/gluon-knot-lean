import PositivePolygonCutComponent

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW PermutationOrbits PolygonDrawing Equiv
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

theorem polygon_incoming_lt_visit (c : PolygonCrossing q) (i : Fin 2) :
    letI := polygonEventOrder q hq.g2
    incoming q hq c i < visit q c i := by
  letI := polygonEventOrder q hq.g2
  rcases orderedCyclicSuccessor_order_spec (PolygonEvent q) (incoming q hq c i) with ⟨h,_⟩|⟨_,h⟩
  · exact (show incoming q hq c i < polygonEventSuccessor q hq.g2 (incoming q hq c i) from h).trans_le
      (le_of_eq (incoming_successor q hq c i))
  · have hm := h (Sum.inl (polygonEventEdge q (visit q c i)))
    change polygonEventSuccessor q hq.g2 (incoming q hq c i) ≤ _ at hm
    rw [incoming_successor] at hm
    have hl := polygonEvent_anchor_lt_visit q hq.g2 (c,if i=0 then false else true)
    exact False.elim ((not_lt_of_ge hm) hl)

/-- Predecessors of actual crossing visits preserve their strict physical order;
none crosses the wrap because its same-edge anchor is earlier. -/
theorem polygon_incoming_lt_iff_visit_lt (c d : PolygonCrossing q) (i j : Fin 2) :
    letI := polygonEventOrder q hq.g2
    incoming q hq c i < incoming q hq d j ↔ visit q c i < visit q d j := by
  letI := polygonEventOrder q hq.g2
  have hnext (e : PolygonCrossing q) (k : Fin 2) (x : PolygonEvent q)
      (hx : incoming q hq e k < x) : visit q e k ≤ x := by
    rcases orderedCyclicSuccessor_order_spec (PolygonEvent q) (incoming q hq e k) with ⟨_,h⟩|⟨h,_⟩
    · have hh:=h x hx
      change polygonEventSuccessor q hq.g2 (incoming q hq e k) ≤ x at hh
      simpa only [incoming_successor] using hh
    · exact False.elim ((not_lt_of_ge (h x)) hx)
  constructor
  · intro h; exact (hnext c i _ h).trans_lt (polygon_incoming_lt_visit q hq d j)
  · intro h
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with hl|he
    · exact (not_lt_of_gt ((hnext d j _ hl).trans_lt (polygon_incoming_lt_visit q hq c i))) h
    · have hh := congrArg (polygonEventSuccessor q hq.g2) he
      simp only [incoming_successor] at hh
      exact (ne_of_lt h) hh.symm

/-- The component test expressed directly in actual crossing visits. -/
theorem smooth_child_component_incoming_iff (c d : PolygonCrossing q) (i : Fin 2) :
    letI := polygonEventOrder q hq.g2
    componentOf (smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)).continuation
      (smoothArcEquiv (positivePolygonEventDiagram q hq) (Sum.inl (eventFin q (incoming q hq d i)))) =
    componentOf (smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)).continuation
      (smoothArcEquiv (positivePolygonEventDiagram q hq) (Sum.inr (1 : Fin 2))) ↔
      visit q c 0 < visit q d i ∧ visit q d i ≤ visit q c 1 := by
  letI := polygonEventOrder q hq.g2
  rw [smooth_child_component_old_arc_iff,polygon_incoming_lt_iff_visit_lt]
  simp only [←not_lt,polygon_incoming_lt_iff_visit_lt]

end DirectGLSSW.HOMFLY.PolygonDrawingBridge
