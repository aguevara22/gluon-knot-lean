import UnitLoopPositionalIndex

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex

/-- A literal nonzero complex affine coordinate change preserves positional index.
Both index-domain proofs are explicit; no topological invariance is assumed. -/
theorem unitPositionalIndex_affine_covariance
    (γ f : C(I, ℂ)) (hγclosed : γ 1 = γ 0) (hfclosed : f 1 = f 0)
    (z a : ℂ) (ha : a ≠ 0) (hγavoid : ∀ u, γ u ≠ z) (hfavoid : ∀ u, f u ≠ 0)
    (hformula : ∀ u, f u = a*(γ u-z)) :
    unitPositionalIndex f hfclosed 0 hfavoid = unitPositionalIndex γ hγclosed z hγavoid := by
  obtain ⟨Γ,hΓ,hinc⟩ := unitPositionalIndex_characterization γ hγclosed z hγavoid
  let Λ : C(I, ℝ) := ⟨fun u => Γ u+a.arg, Γ.continuous.add continuous_const⟩
  have hΛ : ∀ u : I, (Λ u : Real.Angle) = ((f u-0).arg : Real.Angle) := by
    intro u
    rw [sub_zero,hformula u,Complex.arg_mul_coe_angle ha (sub_ne_zero.mpr (hγavoid u))]
    change (Γ u : Real.Angle) + (a.arg : Real.Angle) =
      (a.arg : Real.Angle) + ((γ u-z).arg : Real.Angle)
    rw [hΓ.2 u,add_comm]
  have hfinc := unitPositionalIndex_any_lift f hfclosed 0 hfavoid Λ hΛ
  change Γ 1+a.arg-(Γ 0+a.arg) =
    (unitPositionalIndex f hfclosed 0 hfavoid : ℝ)*(2*Real.pi) at hfinc
  have heq : (unitPositionalIndex f hfclosed 0 hfavoid : ℝ)*(2*Real.pi) =
      (unitPositionalIndex γ hγclosed z hγavoid : ℝ)*(2*Real.pi) := by linarith
  have hcast := mul_right_cancel₀
    (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero) heq
  exact_mod_cast hcast

/-- The coordinate relation also produces the off-image proof for the original
probe from avoidance of zero in the transformed curve. -/
theorem avoids_probe_of_affine_position (γ f : C(I, ℂ)) (z a : ℂ)
    (hfavoid : ∀ u, f u ≠ 0) (hformula : ∀ u, f u = a*(γ u-z)) :
    ∀ u, γ u ≠ z := by
  intro u hu
  apply hfavoid u
  rw [hformula u,hu,sub_self,mul_zero]

end DirectGLSSW.HOMFLY.PositionalIndex


