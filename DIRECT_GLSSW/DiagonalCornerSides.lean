import CornerSecantTurn
import DiagonalStaircaseRetention
import ActualRectangleBoundaryChain

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

def diagonalCornerRightSide {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a0 a p b : ℝ)
    (h0 : secantAxisAdjacent T C a0 a) (ha : secantAxisAdjacent T C a p)
    (hb : secantAxisAdjacent T C p b) : RetainedRectangleSide T C :=
  (⟨((a0,a),(p,b)),diagonalStaircaseRectangle_retained T C a0 a p b h0 ha hb⟩,1)

def diagonalCornerBottomSide {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a p b b1 : ℝ)
    (ha : secantAxisAdjacent T C a p) (hb : secantAxisAdjacent T C p b)
    (h1 : secantAxisAdjacent T C b b1) : RetainedRectangleSide T C :=
  (⟨((a,p),(b,b1)),diagonalStaircaseRectangle_retained T C a p b b1 ha hb h1⟩,0)

theorem diagonalCornerSides_diagonal {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a0 a p b b1 : ℝ)
    (h0 : secantAxisAdjacent T C a0 a) (ha : secantAxisAdjacent T C a p)
    (hb : secantAxisAdjacent T C p b) (h1 : secantAxisAdjacent T C b b1) :
    rectangleDiagonalNeighbour (diagonalCornerRightSide T C a0 a p b h0 ha hb) ∧
    rectangleDiagonalNeighbour (diagonalCornerBottomSide T C a p b b1 ha hb h1) := by
  constructor
  · apply (rectangleDiagonalNeighbour_exact T C _).mpr
    exact ⟨Or.inr rfl,ha⟩
  · apply (rectangleDiagonalNeighbour_exact T C _).mpr
    exact ⟨Or.inl rfl,hb⟩

/-- The literal retained right/bottom pair at an actual original vertex
contributes that source vertex's principal turn. -/
theorem diagonalCornerSides_sum {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (k : ℤ) (a0 a b b1 : ℝ)
    (h0 : secantAxisAdjacent T C a0 a)
    (ha : secantAxisAdjacent T C a ((k : ℝ)+1/2))
    (hb : secantAxisAdjacent T C ((k : ℝ)+1/2) b)
    (h1 : secantAxisAdjacent T C b b1) :
    rectangleSideIncrement (diagonalCornerRightSide T C a0 a ((k : ℝ)+1/2) b h0 ha hb) +
    rectangleSideIncrement (diagonalCornerBottomSide T C a ((k : ℝ)+1/2) b b1 ha hb h1) =
      turn D ((D.continuation ^ k) (T.baseArc C).val) := by
  have hwa := secantAxisAdjacent_width T C _ _ ha
  have hwb := secantAxisAdjacent_width T C _ _ hb
  have hleft : a ∈ Set.Ico ((k : ℝ)-1/2) ((k : ℝ)+1/2) :=
    ⟨by linarith,ha.2.2.1⟩
  have hright : b ∈ Set.Ioc ((k : ℝ)+1/2) ((k : ℝ)+3/2) :=
    ⟨hb.2.2.1,by linarith⟩
  simpa [rectangleSideIncrement,rectangleSideStart,rectangleSideFinish,
    diagonalCornerRightSide,diagonalCornerBottomSide] using
    basedUniformSecant_two_corner_increments T C k a b hleft hright

end
end DirectGLSSW.HOMFLY.PrincipalTurning


