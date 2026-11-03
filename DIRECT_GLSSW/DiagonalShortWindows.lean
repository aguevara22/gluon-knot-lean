import DiagonalNeighbourGeometry

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The full parameter span at a diagonal staircase rectangle is at most
three actual axis cells, each of width at most one quarter. -/
theorem rectangleDiagonalNeighbour_short {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C)
    (h : rectangleDiagonalNeighbour e) : e.1.val.2.2-e.1.val.1.1≤3/4 := by
  have hc := retainedRectangle_axis_cells e.1
  have hm := ((rectangleDiagonalNeighbour_exact T C e).mp h).2
  have hx := secantAxisAdjacent_width T C _ _ hc.1
  have hy := secantAxisAdjacent_width T C _ _ hc.2
  have hz := secantAxisAdjacent_width T C _ _ hm
  linarith

/-- All original uniform vertices have half-integer times. The actual
short staircase window contains at most one, so its secants use at most
two consecutive source arc vectors. -/
theorem rectangleDiagonalNeighbour_vertex_unique {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C)
    (h : rectangleDiagonalNeighbour e) (k l : ℤ)
    (hk : (k : ℝ)+1/2 ∈ Set.Icc e.1.val.1.1 e.1.val.2.2)
    (hl : (l : ℝ)+1/2 ∈ Set.Icc e.1.val.1.1 e.1.val.2.2) : k=l := by
  have hlen := rectangleDiagonalNeighbour_short T C e h
  have hkl : (k : ℝ)<(l : ℝ)+1 := by linarith [hk.2,hl.1]
  have hlk : (l : ℝ)<(k : ℝ)+1 := by linarith [hl.2,hk.1]
  have hkl' : k<l+1 := by exact_mod_cast hkl
  have hlk' : l<k+1 := by exact_mod_cast hlk
  omega

end
end DirectGLSSW.HOMFLY.PrincipalTurning


