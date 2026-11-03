import OpenFirstEdgeGeometry
import DirectGLSSW.EndpointActualRecurrence
import DirectGLSSW.OpenMarkedCurrent

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.OpenFirstEdgeGeometry

/-- The actual open marked current on every tail interval is literally unchanged. -/
theorem openMarkedCurrent_tail (q : ℕ → PlanarPoint ℝ) (ε : ℝ)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) :
    OpenMarkedCurrent.entry (polygonSignArray (approach q ε)) i j =
      OpenMarkedCurrent.entry (polygonSignArray q) i j := by
  unfold OpenMarkedCurrent.entry
  apply EndpointCurrent.weightedCutSum_congr_of_branch_eq _ hij
  intro a b hia hab hbj
  exact ordinaryCurrent_tail q ε _ (by omega) hab

end DirectGLSSW.OpenFirstEdgeGeometry
