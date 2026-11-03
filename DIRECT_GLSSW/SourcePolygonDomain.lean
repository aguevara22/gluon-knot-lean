import ImmersedGlobalRotationExistence
import OriginalLeftTurnLocality
import PolygonUniformity
import PolygonRotationSum

set_option autoImplicit false
namespace DirectGLSSW.SourcePolygonData
open DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW.OriginalLeftTurnLocality

theorem externalMomentum_eq {n : ℕ} (q : Fin n → PlanarPoint ℝ) (i : Fin n) :
    cyclicTangent q i = q (cyclicSuccessor i)-q i := rfl

theorem leftTurn_iff {n : ℕ} (q : Fin n → PlanarPoint ℝ) (i : Fin n) :
    0 < PolygonUniformity.turnDet q i ↔
      0 < planarDet (cyclicTangent q ((cyclicSuccessorPerm n).symm i)) (cyclicTangent q i) := Iff.rfl

theorem leftTurnCount_eq {n : ℕ} (q : Fin n → PlanarPoint ℝ) :
    leftTurnCount q = (Finset.univ.filter (fun i : Fin n =>
      0 < planarDet (cyclicTangent q ((cyclicSuccessorPerm n).symm i)) (cyclicTangent q i))).card := rfl

theorem uniform_iff {n : ℕ} (q : Fin n → PlanarPoint ℝ) :
    PolygonUniformity.PolygonUniform q ↔
      (∀ i : Fin n, 0 < planarDet
        (cyclicTangent q ((cyclicSuccessorPerm n).symm i)) (cyclicTangent q i)) ∨
      (∀ i : Fin n, planarDet
        (cyclicTangent q ((cyclicSuccessorPerm n).symm i)) (cyclicTangent q i) < 0) := Iff.rfl

theorem generic_edges_ne_zero {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (i : Fin n) : polygonEdgeVector q i ≠ 0 := by
  intro h
  apply cyclicTangent_ne_zero hq.size_ge_three q hq.g1 i
  apply Prod.ext
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

theorem generic_adjacent_ratio_slitPlane {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (i : Fin n) :
    polygonEdgeVector q i / polygonEdgeVector q ((cyclicSuccessorPerm n).symm i) ∈ Complex.slitPlane := by
  have hs : cyclicSuccessor ((cyclicSuccessorPerm n).symm i) = i :=
    Equiv.apply_symm_apply (cyclicSuccessorPerm n) i
  have hd := cyclic_turn_det_ne_zero hq.size_ge_three q hq.g1 ((cyclicSuccessorPerm n).symm i)
  rw [hs] at hd
  apply Complex.mem_slitPlane_iff.mpr
  right
  rw [Complex.div_im,← sub_div]
  apply div_ne_zero
  · simpa [polygonEdgeVector,planarDet,mul_comm] using hd
  · exact mt Complex.normSq_eq_zero.mp (generic_edges_ne_zero q hq _)

end DirectGLSSW.SourcePolygonData






