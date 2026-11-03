import FutureCrossingData
import UniformLeftHistoryChildTurns
import ProcessedArcSubsegmentTrace
import PolygonDrawingPorts
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits SmoothingCornerGeometry PolygonDrawingBridge EventSegmentGeometry
attribute [local instance] Classical.propDecidable

/-- An actual moving cursor in the incoming arc of the selected current crossing. -/
def historyCursorPoint (t : MarkedParentState) (c : Fin t.1.nCrossing) (ξ : ℝ) : PlanarPoint ℝ :=
  affinePoint (t.1.vertexPoint (t.1.arcSource (t.1.incoming c (firstVisitedBranch t.2.1 c))))
    (t.1.vertexPoint (t.1.arcTarget (t.1.incoming c (firstVisitedBranch t.2.1 c)))) ξ

/-- A literal interior cursor stays inside the corresponding original polygon
event interval. The carrier parameter and absence of skipped events are derived
from actual historical subsegments, not assumed as a physical correspondence. -/
theorem historyCursorPoint_parameter {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (T : BasedTraversal (positivePolygonEventDiagram q hq)) {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq T) t)
    (c : Fin t.1.nCrossing) (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    let x := PolygonDrawing.incoming q hq ((crossingFin q).symm (h.crossingOrigin c))
      (firstVisitedBranch t.2.1 c)
    ∃ θ : ℝ, polygonEventParameter q x < θ ∧
      θ < polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three x ∧
      0 < θ ∧ θ < 1 ∧
      historyCursorPoint t c ξ = affinePoint (q (polygonEventEdge q x))
        (q (cyclicSuccessor (polygonEventEdge q x))) θ ∧
      ∀ z : PolygonEvent q, polygonEventEdge q z = polygonEventEdge q x →
        polygonEventParameter q z ≠ θ := by
  dsimp only
  let x := PolygonDrawing.incoming q hq ((crossingFin q).symm (h.crossingOrigin c))
    (firstVisitedBranch t.2.1 c)
  obtain ⟨u,v,hu,huv,hv,hs,ht⟩ := h.arcOrigin_subsegment
    (t.1.incoming c (firstVisitedBranch t.2.1 c))
    ((positivePolygonEventDiagram q hq).incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c))
    (h.crossingOrigin_incoming c (firstVisitedBranch t.2.1 c))
  have hs' : t.1.vertexPoint (t.1.arcSource (t.1.incoming c (firstVisitedBranch t.2.1 c))) =
      affinePoint (PolygonDrawing.vertexPoint q (PolygonDrawing.arcSource q x))
        (PolygonDrawing.vertexPoint q (PolygonDrawing.arcTarget q hq x)) u := by
    simpa only [positivePolygonMarkedState,positivePolygonEventDiagram,positiveDiagram,
      polygonEventDiagram,incomingIndex,coordinate,sourceIndex,targetIndex,Equiv.symm_apply_apply] using hs
  have ht' : t.1.vertexPoint (t.1.arcTarget (t.1.incoming c (firstVisitedBranch t.2.1 c))) =
      affinePoint (PolygonDrawing.vertexPoint q (PolygonDrawing.arcSource q x))
        (PolygonDrawing.vertexPoint q (PolygonDrawing.arcTarget q hq x)) v := by
    simpa only [positivePolygonMarkedState,positivePolygonEventDiagram,positiveDiagram,
      polygonEventDiagram,incomingIndex,coordinate,sourceIndex,targetIndex,Equiv.symm_apply_apply] using ht
  let r := u+(v-u)*ξ
  have hr0 : 0 < r := by dsimp [r];nlinarith [mul_pos (sub_pos.mpr huv) hξ0]
  have hr1 : r < 1 := by
    have hm := mul_lt_mul_of_pos_left hξ1 (sub_pos.mpr huv)
    dsimp [r]
    nlinarith
  have hp : historyCursorPoint t c ξ = affinePoint
      (PolygonDrawing.vertexPoint q (PolygonDrawing.arcSource q x))
      (PolygonDrawing.vertexPoint q (PolygonDrawing.arcTarget q hq x)) r := by
    unfold historyCursorPoint
    rw [hs',ht']
    ext <;> simp only [affinePoint,r] <;> ring
  let θ := PolygonDrawing.subarcParameter q hq x r
  obtain ⟨hlo,hhi,h0,h1⟩ := PolygonDrawing.subarcParameter_bounds q hq x r hr0 hr1
  refine ⟨θ,hlo,hhi,h0,h1,?_,?_⟩
  · exact hp.trans (PolygonDrawing.subarcPoint_eq q hq x r)
  · intro z hz he
    have hlow : polygonEventParameter q x < polygonEventParameter q z := by rw [he];exact hlo
    have hhigh : polygonEventParameter q z <
        polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three x := by rw [he];exact hhi
    exact PolygonDrawing.no_event_in_subarc q hq x z hz hlow hhigh

end DirectGLSSW.HOMFLY
