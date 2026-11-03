import ActualPLHalfplaneIndexZero
import PLRootGerm

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex
open DirectGLSSW.HOMFLY.PrincipalTurning

/-- The occupied-side probe, with the same unnormalized normal scale as the
existing exterior probe. -/
def interiorRootProbe (p q : PlanarPoint ℝ) (τ ε : ℝ) : ℂ :=
  exteriorRootProbe p q τ (-ε)

theorem root_normal_affine_difference (p q : PlanarPoint ℝ) (τ t : ℝ) :
    supportingRootNormal p q *
      (Complex.equivRealProd.symm (affinePoint p q t) -
       Complex.equivRealProd.symm (affinePoint p q τ)) =
    ⟨0, ((q.1-p.1)^2+(q.2-p.2)^2)*(τ-t)⟩ := by
  apply Complex.ext <;>
    simp [supportingRootNormal, affinePoint, Complex.equivRealProd_symm_apply,
      Complex.mul_re, Complex.mul_im, Complex.real_smul] <;> ring

theorem root_normal_interior_probe (p q : PlanarPoint ℝ) (τ ε : ℝ) :
    supportingRootNormal p q *
      (interiorRootProbe p q τ ε -
       Complex.equivRealProd.symm (affinePoint p q τ)) =
      ⟨ε*((q.1-p.1)^2+(q.2-p.2)^2), 0⟩ := by
  apply Complex.ext <;>
    simp [interiorRootProbe, exteriorRootProbe, supportingRootNormal, affinePoint,
      Complex.equivRealProd_symm_apply, Complex.mul_re, Complex.mul_im,
      Complex.real_smul] <;> ring

theorem root_length_sq_pos (p q : PlanarPoint ℝ) (hpq : p ≠ q) :
    0 < (q.1-p.1)^2+(q.2-p.2)^2 := by
  by_contra hn
  have hx : (q.1-p.1)^2 = 0 := by nlinarith [sq_nonneg (q.1-p.1), sq_nonneg (q.2-p.2)]
  have hy : (q.2-p.2)^2 = 0 := by nlinarith [sq_nonneg (q.1-p.1), sq_nonneg (q.2-p.2)]
  have hx0 := sq_eq_zero_iff.mp hx
  have hy0 := sq_eq_zero_iff.mp hy
  apply hpq
  apply Prod.ext <;> linarith

end DirectGLSSW.HOMFLY.PositionalIndex




