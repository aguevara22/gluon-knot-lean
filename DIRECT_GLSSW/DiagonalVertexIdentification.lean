import DiagonalVertexSides

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

/-- An actual bottom staircase side ending at an original vertex is its
canonical bottom witness. Adjacency determines all three relevant cells. -/
theorem diagonalBottomSide_eq_vertex {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C)
    (hdiag : rectangleDiagonalNeighbour e) (hs : e.2=0)
    (k : Fin (componentArcLength D (T.baseArc C).val))
    (hp : e.1.val.1.2=(k.val : ℝ)+1/2) :
    e=actualDiagonalVertexSide T C (k,1) := by
  have hc := retainedRectangle_axis_cells e.1
  have hm := ((rectangleDiagonalNeighbour_exact T C e).mp hdiag).2
  let q := actualDiagonalCornerData T C k
  have ha : e.1.val.1.1=q.a := secantAxisAdjacent_right_unique T C _ _ _
    (by simpa only [hp] using hc.1) q.ha
  have hb : e.1.val.2.1=q.b := secantAxisAdjacent_left_unique T C _ _ _
    (by simpa only [hp] using hm) q.hb
  have h1 : e.1.val.2.2=q.b1 := secantAxisAdjacent_left_unique T C _ _ _
    (by simpa only [hb] using hc.2) q.h1
  simp only [actualDiagonalVertexSide,show (1 : Fin 2)≠0 by decide,ite_false]
  apply Prod.ext
  · apply Subtype.ext
    change e.1.val=((q.a,(k.val : ℝ)+1/2),(q.b,q.b1))
    exact Prod.ext (Prod.ext ha hp) (Prod.ext hb h1)
  · simpa [actualDiagonalVertexSide,diagonalCornerBottomSide] using hs

/-- The corresponding actual right staircase side is also uniquely indexed. -/
theorem diagonalRightSide_eq_vertex {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C)
    (hdiag : rectangleDiagonalNeighbour e) (hs : e.2=1)
    (k : Fin (componentArcLength D (T.baseArc C).val))
    (hp : e.1.val.2.1=(k.val : ℝ)+1/2) :
    e=actualDiagonalVertexSide T C (k,0) := by
  have hc := retainedRectangle_axis_cells e.1
  have hm := ((rectangleDiagonalNeighbour_exact T C e).mp hdiag).2
  let q := actualDiagonalCornerData T C k
  have ha : e.1.val.1.2=q.a := secantAxisAdjacent_right_unique T C _ _ _
    (by simpa only [hp] using hm) q.ha
  have h0 : e.1.val.1.1=q.a0 := secantAxisAdjacent_right_unique T C _ _ _
    (by simpa only [ha] using hc.1) q.h0
  have hb : e.1.val.2.2=q.b := secantAxisAdjacent_left_unique T C _ _ _
    (by simpa only [hp] using hc.2) q.hb
  simp only [actualDiagonalVertexSide,ite_true]
  apply Prod.ext
  · apply Subtype.ext
    change e.1.val=((q.a0,q.a),((k.val : ℝ)+1/2,q.b))
    exact Prod.ext (Prod.ext h0 ha) (Prod.ext hp hb)
  · simpa [actualDiagonalVertexSide,diagonalCornerRightSide] using hs

end
end DirectGLSSW.HOMFLY.PrincipalTurning


