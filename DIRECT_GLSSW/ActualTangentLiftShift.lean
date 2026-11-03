import ActualTangentLift

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Periodicity of the literal actual nonzero global tangent. -/
theorem roundedComponentVelocity_periodic (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) :
    Function.Periodic (roundedComponentVelocity D e δ) (componentArcLength D e : ℝ) := by
  intro t
  unfold roundedComponentVelocity
  rw [Int.floor_add_natCast, Int.fract_add_natCast, zpow_add, Equiv.Perm.mul_apply,
    zpow_natCast, continuation_pow_componentArcLength]

/-- Every starting time has the actual finite component turning increment.
This is derived from actual velocity periodicity and continuous lift uniqueness. -/
theorem actualTangentLift_shift (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) :
    actualTangentLift D e δ (t + (componentArcLength D e : ℝ)) -
      actualTangentLift D e δ t =
        componentTotalTurn D (PermutationOrbits.componentOf D.continuation e) := by
  let N : ℝ := componentArcLength D e
  have hf : Continuous (fun x : ℝ => actualTangentLift D e δ (x + N)) :=
    (actualTangentLift_continuous D e δ).comp (continuous_id.add continuous_const)
  have heq : ∀ x : ℝ, (actualTangentLift D e δ (x + N) : Real.Angle) =
      (actualTangentLift D e δ x : Real.Angle) := by
    intro x
    rw [actualTangentLift_coe, actualTangentLift_coe]
    rw [roundedComponentVelocity_periodic D e δ x]
  have h := continuous_angle_lifts_sub_constant
    (fun x : ℝ => actualTangentLift D e δ (x + N)) (actualTangentLift D e δ)
    hf (actualTangentLift_continuous D e δ) heq t 0
  simp only [zero_add] at h
  exact h.trans (actualTangentLift_period_increment D e δ)

end DirectGLSSW.HOMFLY.PrincipalTurning


