import DiagonalNeighbourGeometry

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every literal three-cell staircase rectangle is retained. The intervening
cell has width at most1/4, while actual crossing windows have gap greater
than1/2; the periodic corner also cannot meet this short staircase. -/
theorem diagonalStaircaseRectangle_retained {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b u v : ℝ)
    (hx : secantAxisAdjacent T C a b) (hm : secantAxisAdjacent T C b u)
    (hy : secantAxisAdjacent T C u v) :
    ((a,b),(u,v)) ∈ secantRetainedRectangles T C := by
  have hwidth := secantAxisAdjacent_width T C b u hm
  have hp := basedComponent_period_positive T C
  have hnat : 0<componentArcLength D (T.baseArc C).val := by exact_mod_cast hp
  have hnat1 : 1≤componentArcLength D (T.baseArc C).val := by omega
  have hperiod : (1 : ℝ)≤(componentArcLength D (T.baseArc C).val : ℝ) := by exact_mod_cast hnat1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hm.2.2.1,?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx.1,hx.2.1⟩,hx⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy.1,hy.2.1⟩,hy⟩
  · rintro ⟨hb,hu⟩
    linarith
  · rintro ⟨c,i,j,hij,hi,hj,horder,hla,hbr,hlu,hvr⟩
    have hgap := orderedVisitWindows_gap T c i j hij (hi.trans hj.symm) horder
    linarith

end
end DirectGLSSW.HOMFLY.PrincipalTurning

