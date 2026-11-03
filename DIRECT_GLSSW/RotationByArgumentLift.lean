import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic

set_option autoImplicit false
namespace DirectGLSSW.DescendingSpatial

theorem exp_mul_I_eq_of_angle_eq (θ φ : ℝ) (h : (θ : Real.Angle) = (φ : Real.Angle)) :
    Complex.exp ((θ:ℂ)*Complex.I) = Complex.exp ((φ:ℂ)*Complex.I) := by
  have hc : Real.cos θ = Real.cos φ := by
    simpa only [Real.Angle.cos_coe] using congrArg Real.Angle.cos h
  have hs : Real.sin θ = Real.sin φ := by
    simpa only [Real.Angle.sin_coe] using congrArg Real.Angle.sin h
  rw [Complex.exp_mul_I,Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos,← Complex.ofReal_sin,hc,hs]

theorem rotation_by_argument_lift (z : ℂ) (θ : ℝ)
    (h : (θ : Real.Angle) = (z.arg : Real.Angle)) :
    Complex.exp (-(θ:ℂ)*Complex.I)*z = (‖z‖:ℂ) := by
  have he := exp_mul_I_eq_of_angle_eq θ z.arg h
  have hz : (‖z‖:ℂ)*Complex.exp ((θ:ℂ)*Complex.I) = z := by
    rw [he]
    exact Complex.norm_mul_exp_arg_mul_I z
  calc
    Complex.exp (-(θ:ℂ)*Complex.I)*z =
        Complex.exp (-(θ:ℂ)*Complex.I)*((‖z‖:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) :=
      congrArg (fun w => Complex.exp (-(θ:ℂ)*Complex.I)*w) hz.symm
    _ = (‖z‖:ℂ) := by
      rw [show -(θ:ℂ)*Complex.I = -((θ:ℂ)*Complex.I) by ring,Complex.exp_neg]
      field_simp [Complex.exp_ne_zero]

end DirectGLSSW.DescendingSpatial


