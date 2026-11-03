import PositivePolygonTurns
import PositivePolygonAnchorTraversal
import ExposedEdgeGeometry
import ProcessedRootExposureProbe
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open PolygonDrawing SmoothingCornerGeometry ExposedOpenPrimitive PermutationOrbits
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

theorem positivePolygonEventDiagram_connected :
    ∀ x y : Fin (positivePolygonEventDiagram q hq).nArc,
      (positivePolygonEventDiagram q hq).continuation.SameCycle x y := by
  intro x y
  exact (polygonEventDiagram_isCycleOn q hq).2 (Set.mem_univ _) (Set.mem_univ _)

theorem positivePolygonEventDiagram_vertex_halfplane
    (e : Fin n) (he : LeftExposed q e) :
    ∀ v, 0 ≤ planarDet (cyclicTangent q e)
      ((positivePolygonEventDiagram q hq).vertexPoint v-q e) := by
  intro v
  change 0 ≤ planarDet (cyclicTangent q e)
    (PolygonDrawing.vertexPoint q ((vertexFin q).symm v)-q e)
  cases hv : (vertexFin q).symm v with
  | inl i => exact leftExposed_vertex_nonneg q e he i
  | inr c => exact leftExposed_event_nonneg q e he (Sum.inr (c,false))

theorem positivePolygonEventDiagram_supporting_anchor
    (e : Fin n) (he : LeftExposed q e) :
    ∀ v, 0 ≤ planarDet
      ((positivePolygonEventDiagram q hq).vertexPoint
        ((positivePolygonEventDiagram q hq).arcTarget (eventFin q (Sum.inl e))) -
       (positivePolygonEventDiagram q hq).vertexPoint
        ((positivePolygonEventDiagram q hq).arcSource (eventFin q (Sum.inl e))))
      ((positivePolygonEventDiagram q hq).vertexPoint v-
       (positivePolygonEventDiagram q hq).vertexPoint
        ((positivePolygonEventDiagram q hq).arcSource (eventFin q (Sum.inl e)))) := by
  intro v
  have hs : (positivePolygonEventDiagram q hq).vertexPoint
      ((positivePolygonEventDiagram q hq).arcSource (eventFin q (Sum.inl e))) = q e := by
    change (polygonEventDiagram q hq).vertexPoint
      ((polygonEventDiagram q hq).arcSource (eventFin q (Sum.inl e))) = q e
    rw [polygonEventDiagram_arcSource,polygonEventDiagram_vertexPoint]
    rfl
  change 0 ≤ planarDet (arcVector (positivePolygonEventDiagram q hq) (eventFin q (Sum.inl e))) _
  rw [positivePolygonEventDiagram_arcVector,hs]
  have heq : planarDet
      (stepScale q hq (Sum.inl e) • cyclicTangent q (polygonEventEdge q (Sum.inl e)))
      ((positivePolygonEventDiagram q hq).vertexPoint v-q e) =
      stepScale q hq (Sum.inl e) * planarDet (cyclicTangent q e)
        ((positivePolygonEventDiagram q hq).vertexPoint v-q e) := by
    simp only [polygonEventEdge,planarDet,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    ring
  rw [heq]
  exact mul_nonneg (stepScale_pos q hq _).le (positivePolygonEventDiagram_vertex_halfplane q hq e he v)

theorem initialAnchorTraversal_supporting
    (he : LeftExposed q ⟨0,by have := hq.size_ge_three;omega⟩)
    (C : diagramComponent (positivePolygonEventDiagram q hq)) :
    ∀ v, 0 ≤ planarDet
      ((positivePolygonEventDiagram q hq).vertexPoint
        ((positivePolygonEventDiagram q hq).arcTarget ((initialAnchorTraversal q hq).baseArc C).val)-
       (positivePolygonEventDiagram q hq).vertexPoint
        ((positivePolygonEventDiagram q hq).arcSource ((initialAnchorTraversal q hq).baseArc C).val))
      ((positivePolygonEventDiagram q hq).vertexPoint v-
       (positivePolygonEventDiagram q hq).vertexPoint
        ((positivePolygonEventDiagram q hq).arcSource ((initialAnchorTraversal q hq).baseArc C).val)) := by
  rw [initialAnchorTraversal_baseArc]
  exact positivePolygonEventDiagram_supporting_anchor q hq _ he
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
