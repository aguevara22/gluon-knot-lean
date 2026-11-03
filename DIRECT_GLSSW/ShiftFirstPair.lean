import GenericVirtualCursorWall
set_option autoImplicit false
namespace DirectGLSSW.CursorWallTransport
/-- Translate the cursor base and the first fixed vertex together. -/
def shiftFirstPair (W : ℕ → PlanarPoint ℝ) (w : PlanarPoint ℝ) (η : ℝ) (i : ℕ) : PlanarPoint ℝ :=
  if i=0 ∨ i=1 then W i+η • w else W i
end DirectGLSSW.CursorWallTransport
