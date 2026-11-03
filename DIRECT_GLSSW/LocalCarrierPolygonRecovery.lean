import LocalCarrierLineAlgebra
import DirectGLSSW.OrderedEventSuccessor

set_option autoImplicit false
namespace DirectGLSSW.AuxiliaryCarrierChart
open DirectGLSSW

/-- The actual directed edge and its scalar offset, not an incidence certificate. -/
def polygonCarrierCoordinates {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (e : Fin n) : CarrierLine :=
  (cyclicTangent q e, -planarDet (cyclicTangent q e) (q e))

/-- Intersect the actual predecessor and successor carriers at each vertex. -/
noncomputable def reconstructPolygon {n : ℕ} (L : Fin n → CarrierLine)
    (i : Fin n) : PlanarPoint ℝ :=
  lineIntersection (L ((cyclicSuccessorPerm n)⁻¹ i)) (L i)

theorem polygonCarrierDenominator_ne_zero {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (i : Fin n) :
    lineDenominator (polygonCarrierCoordinates q ((cyclicSuccessorPerm n)⁻¹ i))
      (polygonCarrierCoordinates q i) ≠ 0 := by
  have hi : cyclicSuccessor ((cyclicSuccessorPerm n)⁻¹ i)=i := by
    simpa only [cyclicSuccessorPerm_apply] using (cyclicSuccessorPerm n).apply_symm_apply i
  change planarDet (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i)) (cyclicTangent q i) ≠ 0
  simpa only [hi] using cyclic_turn_det_ne_zero hq.size_ge_three q hq.g1 ((cyclicSuccessorPerm n)⁻¹ i)

theorem polygonCarrierCoordinates_value_start {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (e : Fin n) :
    lineValue (polygonCarrierCoordinates q e) (q e)=0 := by
  simp [lineValue, polygonCarrierCoordinates]

theorem polygonCarrierCoordinates_value_successor {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (e : Fin n) :
    lineValue (polygonCarrierCoordinates q e) (q (cyclicSuccessor e))=0 := by
  simp only [lineValue, polygonCarrierCoordinates, cyclicTangent]
  unfold planarDet
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

theorem reconstructPolygon_polygonCarrierCoordinates {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    reconstructPolygon (polygonCarrierCoordinates q)=q := by
  funext i
  have hi : cyclicSuccessor ((cyclicSuccessorPerm n)⁻¹ i)=i := by
    simpa only [cyclicSuccessorPerm_apply] using (cyclicSuccessorPerm n).apply_symm_apply i
  change lineIntersection (polygonCarrierCoordinates q ((cyclicSuccessorPerm n)⁻¹ i))
    (polygonCarrierCoordinates q i) = q i
  symm
  apply lineIntersection_unique
    (polygonCarrierCoordinates q ((cyclicSuccessorPerm n)⁻¹ i))
    (polygonCarrierCoordinates q i)
    (q i)
    (polygonCarrierDenominator_ne_zero q hq i)
  · have hprev := polygonCarrierCoordinates_value_successor q ((cyclicSuccessorPerm n)⁻¹ i)
    rw [hi] at hprev
    exact hprev
  · exact polygonCarrierCoordinates_value_start q i

end DirectGLSSW.AuxiliaryCarrierChart



