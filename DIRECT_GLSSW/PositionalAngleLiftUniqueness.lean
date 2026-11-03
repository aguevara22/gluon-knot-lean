import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Instances.AddCircle
import Mathlib.Topology.SeparatedMap

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PositionalIndex

/-- This uses the existing local homeomorphism, not an unproved covering-map assertion. -/
theorem angle_coe_locally_injective : IsLocallyInjective ((↑) : ℝ → Real.Angle) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  exact (AddCircle.isLocalHomeomorph_coe (2 * Real.pi)).isLocallyInjective

/-- Internal lift-comparison lemma. Existence of either lift is not asserted here. -/
theorem angle_lift_difference_constant {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    (θ ψ : A → ℝ)
    (hθ : Continuous θ) (hψ : Continuous ψ)
    (hangle : ∀ t, (θ t : Real.Angle) = (ψ t : Real.Angle)) (t s : A) :
    θ t - ψ t = θ s - ψ s := by
  apply (T2Space.isSeparatedMap ((↑) : ℝ → Real.Angle)).const_of_comp
    angle_coe_locally_injective (hθ.sub hψ)
  intro x y
  simp only [Real.Angle.coe_sub, hangle, sub_self]

/-- Any two continuous positional-argument lifts have the same period increment. -/
theorem positional_lift_increment_unique (γ : ℝ → ℂ) (z : ℂ) (T : ℝ)
    (θ ψ : ℝ → ℝ) (hθ : Continuous θ) (hψ : Continuous ψ)
    (hθarg : ∀ t, (θ t : Real.Angle) = ((γ t-z).arg : Real.Angle))
    (hψarg : ∀ t, (ψ t : Real.Angle) = ((γ t-z).arg : Real.Angle)) :
    θ T - θ 0 = ψ T - ψ 0 := by
  have h := angle_lift_difference_constant θ ψ hθ hψ
    (fun t => (hθarg t).trans (hψarg t).symm) T 0
  linarith

end DirectGLSSW.HOMFLY.PositionalIndex



