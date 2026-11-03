import PeriodicBoundaryZero
import FixedRectangleSideExact

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Literal adjacency to an actual removed crossing-star cell. -/
def rectangleStarNeighbour {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} (e : RetainedRectangleSide T C) : Prop :=
  if e.2=0 then ∃ l, secantAxisAdjacent T C l e.1.val.2.1 ∧
    secantRectangleInsideStar T C e.1.val.1.1 e.1.val.1.2 l e.1.val.2.1
  else if e.2=1 then ∃ w, secantAxisAdjacent T C e.1.val.1.2 w ∧
    secantRectangleInsideStar T C e.1.val.1.2 w e.1.val.2.1 e.1.val.2.2
  else if e.2=2 then ∃ w, secantAxisAdjacent T C e.1.val.2.2 w ∧
    secantRectangleInsideStar T C e.1.val.1.1 e.1.val.1.2 e.1.val.2.2 w
  else ∃ l, secantAxisAdjacent T C l e.1.val.1.1 ∧
    secantRectangleInsideStar T C l e.1.val.1.1 e.1.val.2.1 e.1.val.2.2

theorem rectangleRemovedNeighbour_three_reasons {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C) :
    rectangleRemovedNeighbour e ↔ rectangleDiagonalNeighbour e ∨
      rectanglePeriodicNeighbour e ∨ rectangleStarNeighbour e := by
  rcases e with ⟨r,s⟩
  fin_cases s <;> simp [rectangleRemovedNeighbour,rectangleDiagonalNeighbour,
    rectanglePeriodicNeighbour,rectangleStarNeighbour,secantRemovedCellReason,
    and_or_left,exists_or]

/-- Exact source-defined four-way cover of the actual fixed boundary. -/
theorem fixedRectangleSide_four_reasons {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C) :
    rectangleSideReverse e=e ↔ rectangleExteriorSide e ∨ rectangleDiagonalNeighbour e ∨
      rectanglePeriodicNeighbour e ∨ rectangleStarNeighbour e := by
  rw [fixedRectangleSide_exact_classification,rectangleRemovedNeighbour_three_reasons]

end
end DirectGLSSW.HOMFLY.PrincipalTurning


