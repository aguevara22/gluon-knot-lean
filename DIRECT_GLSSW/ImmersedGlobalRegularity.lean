import ImmersedCyclicCurve
import IntegerCellDerivative

set_option autoImplicit false
namespace DirectGLSSW.ImmersedGlobalRounding
open DirectGLSSW.HOMFLY.PrincipalTurning DirectGLSSW.HOMFLY.PolygonDrawingBridge

theorem curve_hasDerivAt {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (base : Fin n) (δ : RoundingFraction) (t : ℝ) :
    HasDerivAt (curve q base δ) (curveVelocity q base δ t) t := by
  apply DirectGLSSW.HOMFLY.PrincipalTurning.integer_cell_hasDerivAt
    (fun k => polygonCell q (phase base k) δ)
    (fun k => polygonVelocity q (phase base k) δ)
  · intro k t
    exact cell_hasDerivAt _ _ _ δ t
  · intro k
    rw [← phase_previous base k]
    exact polygonCell_next_join q _ δ
  · intro k
    rw [(polygonVelocity_endpoints _ _ δ).2,(polygonVelocity_endpoints _ _ δ).1]
    unfold incoming
    rw [← phase_previous base k,Equiv.symm_apply_apply]

theorem curve_continuous {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (base : Fin n) (δ : RoundingFraction) : Continuous (curve q base δ) :=
  continuous_iff_continuousAt.mpr (fun t => (curve_hasDerivAt q base δ t).continuousAt)

/-- Complete literal positional-cell characterization, with no chosen curve. -/
theorem curve_eq_cells {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (base : Fin n) (δ : RoundingFraction) (t : ℝ) :
    curve q base δ t =
      cell (Complex.equivRealProd.symm (q (phase base (Int.floor t))))
        (polygonEdgeVector q ((cyclicSuccessorPerm n).symm (phase base (Int.floor t))))
        (polygonEdgeVector q (phase base (Int.floor t))) δ (Int.fract t) := rfl

theorem curveVelocity_eq_cells {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (base : Fin n) (δ : RoundingFraction) (t : ℝ) :
    curveVelocity q base δ t =
      velocity (polygonEdgeVector q ((cyclicSuccessorPerm n).symm (phase base (Int.floor t))))
        (polygonEdgeVector q (phase base (Int.floor t))) δ (Int.fract t) := rfl

end DirectGLSSW.ImmersedGlobalRounding




