import PolygonPositiveDiagram
import SmoothingCornerTurns
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open PolygonDrawing SmoothingCornerGeometry EventSegmentGeometry
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

theorem positivePolygonEventDiagram_arcVector (x : PolygonEvent q) :
    arcVector (positivePolygonEventDiagram q hq) (eventFin q x) =
      stepScale q hq x • cyclicTangent q (polygonEventEdge q x) := by
  change (polygonEventDiagram q hq).vertexPoint
    ((polygonEventDiagram q hq).arcTarget (eventFin q x)) -
    (polygonEventDiagram q hq).vertexPoint
    ((polygonEventDiagram q hq).arcSource (eventFin q x)) = _
  rw [polygonEventDiagram_arcTarget,polygonEventDiagram_arcSource,
    polygonEventDiagram_vertexPoint,polygonEventDiagram_vertexPoint]
  exact arc_vector_eq q hq x

theorem positivePolygonEventDiagram_turn_factor (x : PolygonEvent q) :
    turnDet (positivePolygonEventDiagram q hq) (eventFin q x) =
      (stepScale q hq x * stepScale q hq (polygonEventSuccessor q hq.g2 x)) *
        planarDet (cyclicTangent q (polygonEventEdge q x))
          (cyclicTangent q (polygonEventEdge q (polygonEventSuccessor q hq.g2 x))) := by
  unfold turnDet
  have hs : (positivePolygonEventDiagram q hq).continuation (eventFin q x) =
      eventFin q (polygonEventSuccessor q hq.g2 x) :=
    polygonEventDiagram_continuation q hq x
  rw [hs,positivePolygonEventDiagram_arcVector,positivePolygonEventDiagram_arcVector]
  simp only [planarDet,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

theorem positivePolygonEventDiagram_turn_nonneg
    (hleft : ∀ i : Fin n, 0 ≤ planarDet (cyclicTangent q i)
      (cyclicTangent q (cyclicSuccessor i)))
    (e : Fin (positivePolygonEventDiagram q hq).nArc) :
    0 ≤ turnDet (positivePolygonEventDiagram q hq) e := by
  obtain ⟨x,rfl⟩ := (eventFin q).surjective e
  rw [positivePolygonEventDiagram_turn_factor]
  apply mul_nonneg (mul_nonneg (stepScale_pos q hq x).le (stepScale_pos q hq _).le)
  rcases polygonEventSuccessor_sameEdge_next_or_nextAnchor q hq.g2 hq.size_ge_three x with
    ⟨he,_,_⟩ | ⟨he,_⟩
  · rw [he]
    simp [planarDet,mul_comm]
  · rw [he]
    exact hleft (polygonEventEdge q x)

theorem positivePolygonEventDiagram_turn_nonneg_of_uniform_left
    (hleft : ∀ i : Fin n, 0 < planarDet (cyclicTangent q i)
      (cyclicTangent q (cyclicSuccessor i))) :
    ∀ e : Fin (positivePolygonEventDiagram q hq).nArc,
      0 ≤ turnDet (positivePolygonEventDiagram q hq) e :=
  positivePolygonEventDiagram_turn_nonneg q hq (fun i => (hleft i).le)
end DirectGLSSW.HOMFLY.PolygonDrawingBridge

#check @DirectGLSSW.HOMFLY.PolygonDrawingBridge.positivePolygonEventDiagram_arcVector

#check @DirectGLSSW.HOMFLY.PolygonDrawingBridge.positivePolygonEventDiagram_turn_factor

#check @DirectGLSSW.HOMFLY.PolygonDrawingBridge.positivePolygonEventDiagram_turn_nonneg

#check @DirectGLSSW.HOMFLY.PolygonDrawingBridge.positivePolygonEventDiagram_turn_nonneg_of_uniform_left

