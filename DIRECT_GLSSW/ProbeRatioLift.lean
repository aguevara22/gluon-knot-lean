import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.UnitInterval

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex

/-- A probe displacement smaller than the pointwise clearance keeps the
positional-vector ratio in the slit plane. -/
theorem positional_ratio_mem_slitPlane (x z w : ℂ) (hsmall : ‖w-z‖ < ‖x-z‖) :
    (x-w)/(x-z) ∈ Complex.slitPlane := by
  have hp : 0 < ‖x-z‖ := lt_of_le_of_lt (norm_nonneg _) hsmall
  have hnz : x-z ≠ 0 := norm_pos_iff.mp hp
  have hn : ‖(z-w)/(x-z)‖ < 1 := by
    rw [norm_div, div_lt_one hp]
    simpa only [norm_sub_rev] using hsmall
  have heq : (x-w)/(x-z) = 1+(z-w)/(x-z) := by
    field_simp [hnz]
  rw [heq]
  exact Complex.mem_slitPlane_of_norm_lt_one hn

/-- A nearby probe has a closed real argument correction. No index or winding
invariance is assumed in this geometric/analytic producer. -/
theorem exists_closed_probe_argument_correction (γ : C(I, ℂ))
    (hclosed : γ 1 = γ 0) (z w : ℂ)
    (hsmall : ∀ u, ‖w-z‖ < ‖γ u-z‖) :
    (∀ u, γ u ≠ z) ∧ (∀ u, γ u ≠ w) ∧
      ∃ ρ : C(I, ℝ), ρ 1 = ρ 0 ∧ ∀ u,
        (ρ u : Real.Angle) = ((γ u-w).arg : Real.Angle) - ((γ u-z).arg : Real.Angle) := by
  have hz (u : I) : γ u ≠ z := by
    apply sub_ne_zero.mp
    exact norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) (hsmall u))
  have hslit (u : I) : (γ u-w)/(γ u-z) ∈ Complex.slitPlane :=
    positional_ratio_mem_slitPlane _ _ _ (hsmall u)
  have hw (u : I) : γ u ≠ w := by
    intro heq
    have h := hslit u
    rw [heq,sub_self,zero_div] at h
    exact Complex.zero_not_mem_slitPlane h
  have hcont : Continuous (fun u : I => ((γ u-w)/(γ u-z)).arg) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    have hi : ContinuousAt (fun v : I => (γ v-w)/(γ v-z)) u :=
      ((γ.continuous.sub continuous_const).div (γ.continuous.sub continuous_const)
        (fun v => sub_ne_zero.mpr (hz v))).continuousAt
    exact ContinuousAt.comp' (f := fun v : I => (γ v-w)/(γ v-z))
      (g := Complex.arg) (x := u) (Complex.continuousAt_arg (hslit u)) hi
  refine ⟨hz,hw,⟨_,hcont⟩,?_,?_⟩
  · change ((γ 1-w)/(γ 1-z)).arg = ((γ 0-w)/(γ 0-z)).arg
    rw [hclosed]
  · intro u
    exact Complex.arg_div_coe_angle (sub_ne_zero.mpr (hw u)) (sub_ne_zero.mpr (hz u))

end DirectGLSSW.HOMFLY.PositionalIndex


