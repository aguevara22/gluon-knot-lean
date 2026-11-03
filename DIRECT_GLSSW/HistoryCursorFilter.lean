import PolygonCursorFilter
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PolygonDrawingBridge PolygonDrawing SmoothingCornerGeometry EventSegmentGeometry
attribute [local instance] Classical.propDecidable

/-- On the actual initial-root history, the selected physical carrier is the
original lower-labelled carrier; no global branch-transport premise is supplied. -/
theorem history_selected_branch_zero {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) : firstVisitedBranch t.2.1 c = 0 := by
  have hinit : firstVisitedBranch (initialAnchorTraversal q hq) (h.crossingOrigin c) = 0 := by
    simpa only [Equiv.apply_symm_apply] using
      initialAnchorTraversal_firstVisitedBranch q hq ((crossingFin q).symm (h.crossingOrigin c))
  exact (h.selectedSuffix_firstVisitedBranch c hc).trans hinit

/-- The physical future filter is derived at the actual moving cursor, on the
original polygon carriers. This is the input to literal cutArc/suffix/moveStart. -/
theorem historyCursorPoint_future_filter {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    let d0 := (crossingFin q).symm (h.crossingOrigin c)
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      historyCursorPoint t c ξ = affinePoint (q d0.val.1) (q (cyclicSuccessor d0.val.1)) θ ∧
      (∀ z : PolygonEvent q, polygonEventEdge q z = d0.val.1 → polygonEventParameter q z ≠ θ) ∧
      ∀ d : PolygonCrossing q,
        (∀ i : Fin 2,
          visitPosition (initialAnchorTraversal q hq)
            ((positivePolygonEventDiagram q hq).incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) ≤
          visitPosition (initialAnchorTraversal q hq)
            ((positivePolygonEventDiagram q hq).incoming (crossingFin q d) i)) ↔
        ∀ i : Fin 2, d0.val.1 < polygonEventEdge q (visit q d i) ∨
          (d0.val.1 = polygonEventEdge q (visit q d i) ∧ θ < polygonEventParameter q (visit q d i)) := by
  dsimp only
  let d0 := (crossingFin q).symm (h.crossingOrigin c)
  have hb := history_selected_branch_zero q hq h c hc
  obtain ⟨θ,hlo,hhi,h0,h1,hpoint,hno⟩ := historyCursorPoint_parameter q hq (initialAnchorTraversal q hq) h c ξ hξ0 hξ1
  rw [hb] at hlo hhi hpoint hno
  rw [incoming_terminal_parameter] at hhi
  rw [PolygonDrawing.incoming_edge] at hpoint hno
  refine ⟨θ,h0,h1,?_,?_,?_⟩
  · simpa only [incoming_edge,visit,polygonEventEdge,crossingVisitEdge,Fin.isValue,ite_true] using hpoint
  · simpa only [incoming_edge,visit,polygonEventEdge,crossingVisitEdge,Fin.isValue,ite_true] using hno
  · intro d
    rw [hb]
    have H (i : Fin 2) := initial_incoming_cursor_filter q hq d0 d 0 i θ hlo hhi
    simp only [d0,Equiv.apply_symm_apply,visit,polygonEventEdge,crossingVisitEdge,Fin.isValue,ite_true] at H
    exact forall_congr' H

end DirectGLSSW.HOMFLY
