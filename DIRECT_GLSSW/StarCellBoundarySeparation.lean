import FixedBoundaryFourReasons
import StarCellHoleIdentification

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

theorem secantStarCell_ordered_gap {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b u v : ℝ)
    (h : secantRectangleInsideStar T C a b u v) : b+1/2<u := by
  obtain ⟨c,i,j,hij,hi,hj,horder,_,hbr,hul,_⟩ := h
  have hg := orderedVisitWindows_gap T c i j hij (hi.trans hj.symm) horder
  linarith

theorem secantStarCell_quarter_margin {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b u v : ℝ)
    (h : secantRectangleInsideStar T C a b u v) :
    1/4<a ∧ v<(componentArcLength D (T.baseArc C).val : ℝ)-1/4 := by
  obtain ⟨c,i,j,_,hi,hj,_,hal,_,_,hvr⟩ := h
  have he := secantMeshEpsilon_positive D
  have hl := secantMesh_visit_window_inside_margin T c i (-secantMeshEpsilon D)
    ⟨le_rfl,by linarith⟩
  have hr := secantMesh_visit_window_inside_margin T c j (2*secantMeshEpsilon D)
    ⟨by linarith,le_rfl⟩
  have hleft : 1/4<secantVisitLeft T c i := by simpa only [secantVisitLeft] using hl.1
  have hright : secantVisitRight T c j<(componentArcLength D (T.baseArc C).val : ℝ)-1/4 := by
    have hrbound := hr.2
    rw [hj] at hrbound
    exact hrbound
  constructor <;> linarith

theorem rectangleStarNeighbour_not_exterior {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C)
    (hstar : rectangleStarNeighbour e) : ¬rectangleExteriorSide e := by
  intro hout
  rcases e with ⟨r,s⟩
  fin_cases s
  · simp [rectangleExteriorSide] at hout
  · simp [rectangleExteriorSide] at hout
  · simp [rectangleExteriorSide] at hout
    simp [rectangleStarNeighbour] at hstar
    obtain ⟨w,hw,hs⟩ := hstar
    have hmargin := secantStarCell_quarter_margin T C _ _ _ _ hs
    linarith [hw.2.2.1]
  · simp [rectangleExteriorSide] at hout
    simp [rectangleStarNeighbour] at hstar
    obtain ⟨l,hl,hs⟩ := hstar
    have hmargin := secantStarCell_quarter_margin T C _ _ _ _ hs
    linarith [hl.2.2.1]

theorem rectangleDiagonalNeighbour_not_exterior {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C)
    (hdiag : rectangleDiagonalNeighbour e) : ¬rectangleExteriorSide e := by
  have hs := ((rectangleDiagonalNeighbour_exact T C e).mp hdiag).1
  rcases hs with hs | hs <;>
    simp [rectangleExteriorSide,hs]

theorem rectangleStarNeighbour_not_diagonal {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C)
    (hstar : rectangleStarNeighbour e) : ¬rectangleDiagonalNeighbour e := by
  intro hdiag
  obtain ⟨hs,hcell⟩ := (rectangleDiagonalNeighbour_exact T C e).mp hdiag
  have hwidth := secantAxisAdjacent_width T C _ _ hcell
  rcases hs with hs | hs
  · have h : ∃ l, secantAxisAdjacent T C l e.1.val.2.1 ∧
        secantRectangleInsideStar T C e.1.val.1.1 e.1.val.1.2 l e.1.val.2.1 := by
      simpa only [rectangleStarNeighbour,hs,ite_true] using hstar
    obtain ⟨l,hl,hgap⟩ := h
    have hg := secantStarCell_ordered_gap T C _ _ _ _ hgap
    linarith [hl.2.2.1]
  · have h : ∃ w, secantAxisAdjacent T C e.1.val.1.2 w ∧
        secantRectangleInsideStar T C e.1.val.1.2 w e.1.val.2.1 e.1.val.2.2 := by
      simpa only [rectangleStarNeighbour,hs,show (1 : Fin 4) ≠ 0 by decide,
        ite_false,ite_true] using hstar
    obtain ⟨w,hw,hgap⟩ := h
    have hg := secantStarCell_ordered_gap T C _ _ _ _ hgap
    linarith [hw.2.2.1]

end
end DirectGLSSW.HOMFLY.PrincipalTurning






