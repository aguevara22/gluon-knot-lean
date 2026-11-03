import DaughterGapInterior
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DaughterClosedContainment
open DaughterFirstReturn
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
    (hroot : retainedCorner q S root)
include hroot

theorem gap_offset_parameter_lt_iff (c : CornerCoord q hq.g2 S root) (i j : ℕ)
    (hi : i < cornerGap q hq.g2 S root c.val (cornerSuccessor q hq.g2 S root c).val)
    (hj : j < cornerGap q hq.g2 S root c.val (cornerSuccessor q hq.g2 S root c).val) :
    polygonEventParameter q ((DartPerm q hq.g2 S ^ i) (orbitEventAt q hq.g2 S root c.val)) <
      polygonEventParameter q ((DartPerm q hq.g2 S ^ j) (orbitEventAt q hq.g2 S root c.val)) ↔ i<j := by
  constructor
  · intro h
    by_contra hh
    exact (not_lt_of_ge (gap_parameter_mono q hq S root hroot c i hi j (by omega))) h
  · intro hij
    exact (gap_parameter_step q hq S root hroot c i (by omega)).trans_le
      (gap_parameter_mono q hq S root hroot c j hj (i+1) (by omega))
end DirectGLSSW.DaughterClosedContainment
