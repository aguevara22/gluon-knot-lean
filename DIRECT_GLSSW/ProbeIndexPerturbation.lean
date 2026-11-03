import UnitLoopPositionalIndex
import ProbeRatioLift

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex

/-- Pointwise clearance proves index equality by adding a closed argument
correction; no homotopy or invariance statement is an input. -/
theorem unitPositionalIndex_eq_of_small_displacement (γ : C(I, ℂ))
    (hclosed : γ 1 = γ 0) (z w : ℂ)
    (hz : ∀ u, γ u ≠ z) (hw : ∀ u, γ u ≠ w)
    (hsmall : ∀ u, ‖w-z‖ < ‖γ u-z‖) :
    unitPositionalIndex γ hclosed z hz = unitPositionalIndex γ hclosed w hw := by
  obtain ⟨_,_,ρ,hρclosed,hρ⟩ := exists_closed_probe_argument_correction γ hclosed z w hsmall
  obtain ⟨Γ,hΓ,hinc⟩ := unitPositionalIndex_characterization γ hclosed z hz
  let Λ : C(I, ℝ) := ⟨fun u => Γ u + ρ u, Γ.continuous.add ρ.continuous⟩
  have hΛ : ∀ u : I, (Λ u : Real.Angle) = ((γ u-w).arg : Real.Angle) := by
    intro u
    change (Γ u : Real.Angle) + (ρ u : Real.Angle) = ((γ u-w).arg : Real.Angle)
    rw [hΓ.2 u, hρ u]
    abel
  have hwinc := unitPositionalIndex_any_lift γ hclosed w hw Λ hΛ
  change Γ 1 + ρ 1 - (Γ 0 + ρ 0) =
    (unitPositionalIndex γ hclosed w hw : ℝ) * (2*Real.pi) at hwinc
  rw [hρclosed] at hwinc
  have heq : (unitPositionalIndex γ hclosed z hz : ℝ) * (2*Real.pi) =
      (unitPositionalIndex γ hclosed w hw : ℝ) * (2*Real.pi) := by linarith
  have hcast := mul_right_cancel₀
    (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero) heq
  exact_mod_cast hcast

/-- A distance-to-curve lower bound discharges the pointwise smallness condition.
This is the direct interface for a geometric clearance producer. -/
theorem unitPositionalIndex_eq_of_clearance (γ : C(I, ℂ))
    (hclosed : γ 1 = γ 0) (z w : ℂ)
    (hz : ∀ u, γ u ≠ z) (hw : ∀ u, γ u ≠ w)
    (r : ℝ) (hclear : ∀ u, r ≤ ‖γ u-z‖) (hsmall : ‖w-z‖ < r) :
    unitPositionalIndex γ hclosed z hz = unitPositionalIndex γ hclosed w hw :=
  unitPositionalIndex_eq_of_small_displacement γ hclosed z w hz hw
    (fun u => hsmall.trans_le (hclear u))

end DirectGLSSW.HOMFLY.PositionalIndex


