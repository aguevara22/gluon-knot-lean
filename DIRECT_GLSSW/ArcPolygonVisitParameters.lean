import ActiveArcPositiveFirstCrossing
import ActiveArcChildVisitOrder

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc
open HOMFLY.PolygonDrawing
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hQ : CyclicGeneric q) (hR : Regular q)

private theorem cyclicSuccessor_castSucc (e : Fin (n+1)) :
    cyclicSuccessor e.castSucc = e.succ := by
  apply Fin.ext
  change (e.val+1+0)%(n+2)=e.val+1
  exact Nat.mod_eq_of_lt (by omega)

include hQ in
/-- Cyclic polygon and actual open arc labels identify the same physical crossing point. -/
theorem polygonCrossingOfArc_point (d : Crossing q) :
    DirectGLSSW.crossingPoint q (polygonCrossingOfArc q d) = crossingPoint q d := by
  symm
  apply DirectGLSSW.crossingPoint_eq_of_mem hQ.size_ge_three q hQ.g1
  · simpa only [polygonCrossingOfArc,DirectGLSSW.edgeInterior,cyclicSuccessor_castSucc,edgeInterior]
      using (crossingPoint_mem q d).1
  · simpa only [polygonCrossingOfArc,DirectGLSSW.edgeInterior,cyclicSuccessor_castSucc,edgeInterior]
      using (crossingPoint_mem q d).2

include hQ hR in
/-- The actual visit parameter is unchanged by the same-edge polygon inclusion. -/
theorem polygonCrossingOfArc_visitParameter (d : Crossing q) (z : Bool) :
    crossingVisitParameter q (polygonCrossingOfArc q d,z) = visitParameter q (d,z) := by
  have hp := (crossingVisitParameter_spec q (polygonCrossingOfArc q d,z)).2.2
  have ha := (visitParameter_spec q (d,z)).2.2
  change DirectGLSSW.crossingPoint q (polygonCrossingOfArc q d) = _ at hp
  rw [polygonCrossingOfArc_point q hQ] at hp
  cases z
  · apply edge_parameter_unique q hR d.val.1
    simpa [polygonCrossingOfArc,crossingVisitEdge,cyclicSuccessor_castSucc,visitEdge] using hp.symm.trans ha
  · apply edge_parameter_unique q hR d.val.2
    simpa [polygonCrossingOfArc,crossingVisitEdge,cyclicSuccessor_castSucc,visitEdge] using hp.symm.trans ha
end DirectGLSSW.ActiveArc
