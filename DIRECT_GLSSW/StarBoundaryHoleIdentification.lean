import FixedBoundaryFourReasons
import StarCellHoleIdentification

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Literal star-side adjacency is exactly adjacency to an actual component hole. -/
theorem rectangleStarNeighbour_iff_actual_hole {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C) :
    rectangleStarNeighbour e ↔ ∃ c ∈ actualComponentSelfCrossings T C,
      rectangleTouchesCrossingHole T C c (firstVisitedBranch T c)
        (otherBranch (firstVisitedBranch T c)) e := by
  have hc := retainedRectangle_axis_cells e.1
  rcases e with ⟨r,s⟩
  fin_cases s
  · simp [rectangleStarNeighbour,rectangleTouchesCrossingHole]
    constructor
    · rintro ⟨w,hw,hstar⟩
      obtain ⟨c,hc',hcell⟩ :=
        (secantRectangleInsideStar_iff_hole_cell T C r.val.1.1 r.val.1.2 w r.val.2.1 hc.1 hw).mp hstar
      exact ⟨c,hc',w,hw,hcell⟩
    · rintro ⟨c,hc',w,hw,hcell⟩
      refine ⟨w,hw,?_⟩
      exact (secantRectangleInsideStar_iff_hole_cell T C r.val.1.1 r.val.1.2 w r.val.2.1 hc.1 hw).mpr
        ⟨c,hc',hcell⟩
  · simp [rectangleStarNeighbour,rectangleTouchesCrossingHole]
    constructor
    · rintro ⟨w,hw,hstar⟩
      obtain ⟨c,hc',hcell⟩ :=
        (secantRectangleInsideStar_iff_hole_cell T C r.val.1.2 w r.val.2.1 r.val.2.2 hw hc.2).mp hstar
      exact ⟨c,hc',w,hw,hcell⟩
    · rintro ⟨c,hc',w,hw,hcell⟩
      refine ⟨w,hw,?_⟩
      exact (secantRectangleInsideStar_iff_hole_cell T C r.val.1.2 w r.val.2.1 r.val.2.2 hw hc.2).mpr
        ⟨c,hc',hcell⟩
  · simp [rectangleStarNeighbour,rectangleTouchesCrossingHole]
    constructor
    · rintro ⟨w,hw,hstar⟩
      obtain ⟨c,hc',hcell⟩ :=
        (secantRectangleInsideStar_iff_hole_cell T C r.val.1.1 r.val.1.2 r.val.2.2 w hc.1 hw).mp hstar
      exact ⟨c,hc',w,hw,hcell⟩
    · rintro ⟨c,hc',w,hw,hcell⟩
      refine ⟨w,hw,?_⟩
      exact (secantRectangleInsideStar_iff_hole_cell T C r.val.1.1 r.val.1.2 r.val.2.2 w hc.1 hw).mpr
        ⟨c,hc',hcell⟩
  · simp [rectangleStarNeighbour,rectangleTouchesCrossingHole]
    constructor
    · rintro ⟨w,hw,hstar⟩
      obtain ⟨c,hc',hcell⟩ :=
        (secantRectangleInsideStar_iff_hole_cell T C w r.val.1.1 r.val.2.1 r.val.2.2 hw hc.2).mp hstar
      exact ⟨c,hc',w,hw,hcell⟩
    · rintro ⟨c,hc',w,hw,hcell⟩
      refine ⟨w,hw,?_⟩
      exact (secantRectangleInsideStar_iff_hole_cell T C w r.val.1.1 r.val.2.1 r.val.2.2 hw hc.2).mpr
        ⟨c,hc',hcell⟩

end
end DirectGLSSW.HOMFLY.PrincipalTurning

