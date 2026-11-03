import SplitCircleJoined

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SplitCircleConstructor
open DirectGLSSW

/-- The coordinate-bound-selected separator. -/
private def diagramVerticesNonempty (D : PLLinkDiagram) (hD : 0 < D.nArc) :
    (Finset.univ : Finset (Fin D.nVertex)).Nonempty :=
  ⟨D.arcSource ⟨0, hD⟩, Finset.mem_univ _⟩

def chosenRightBound (D : PLLinkDiagram) (hD : 0 < D.nArc) : ℝ :=
  (Finset.univ : Finset (Fin D.nVertex)).sup'
    (diagramVerticesNonempty D hD) (fun v => (D.vertexPoint v).1) + 1

theorem chosenRightBound_left (D : PLLinkDiagram) (hD : 0 < D.nArc) :
    ∀ v : Fin D.nVertex, (D.vertexPoint v).1 < chosenRightBound D hD :=
  by
    intro v
    have hv : (D.vertexPoint v).1 ≤
        (Finset.univ : Finset (Fin D.nVertex)).sup'
          (diagramVerticesNonempty D hD) (fun w => (D.vertexPoint w).1) :=
      Finset.le_sup' (fun w : Fin D.nVertex => (D.vertexPoint w).1) (Finset.mem_univ v)
    unfold chosenRightBound
    linarith

theorem chosenRightBound_triangle (D : PLLinkDiagram) (hD : 0 < D.nArc) :
    ∀ v : Fin (rightTriangle (chosenRightBound D hD)).nVertex,
      chosenRightBound D hD <
        ((rightTriangle (chosenRightBound D hD)).vertexPoint v).1 := by
  intro v
  have hv : 0 ≤ (triangleUnknot.vertexPoint v).1 := by
    fin_cases v <;>
      (first | change (0 : ℝ) ≤ 0 | change (0 : ℝ) ≤ 1) <;> norm_num
  change chosenRightBound D hD <
    chosenRightBound D hD + 1 + (triangleUnknot.vertexPoint v).1
  linarith

theorem chosenRightBound_old_edges (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (e : Fin D.nArc) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (affinePoint (D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcTarget e)) t).1 < chosenRightBound D hD :=
  affine_x_lt (chosenRightBound_left D hD _)
    (chosenRightBound_left D hD _) ht0 ht1

theorem chosenRightBound_triangle_edges (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (e : Fin (rightTriangle (chosenRightBound D hD)).nArc)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    chosenRightBound D hD <
      (affinePoint
        ((rightTriangle (chosenRightBound D hD)).vertexPoint
          ((rightTriangle (chosenRightBound D hD)).arcSource e))
        ((rightTriangle (chosenRightBound D hD)).vertexPoint
          ((rightTriangle (chosenRightBound D hD)).arcTarget e)) t).1 :=
  affine_x_gt (chosenRightBound_triangle D hD _)
    (chosenRightBound_triangle D hD _) ht0 ht1

/-- Actual disjoint-circle diagram: the added triangle lies strictly to the
right of every vertex and whole arc of the original drawing. -/
def splitCircleDiagram (D : PLLinkDiagram) (hD : 0 < D.nArc) : PLLinkDiagram :=
  joinedDiagram D (chosenRightBound D hD)
    (chosenRightBound_left D hD) (chosenRightBound_triangle D hD)

theorem splitCircle_arc_count (D : PLLinkDiagram) (hD : 0 < D.nArc) :
    (splitCircleDiagram D hD).nArc = D.nArc + 3 := rfl

theorem splitCircle_crossing_count (D : PLLinkDiagram) (hD : 0 < D.nArc) :
    (splitCircleDiagram D hD).nCrossing = D.nCrossing := rfl

end DirectGLSSW.HOMFLY.SplitCircleConstructor

