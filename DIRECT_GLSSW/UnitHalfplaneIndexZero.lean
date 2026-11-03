import UnitLoopPositionalIndex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex

/-- A closed unit loop whose displacement from the probe lies strictly in an
oriented half-plane has genuine positional index zero. The real argument lift
is constructed from the principal argument on the right half-plane. -/
theorem unitPositionalIndex_zero_of_strict_halfplane
    (γ : C(I, ℂ)) (hclosed : γ 1 = γ 0) (z a : ℂ)
    (hhalf : ∀ u : I, 0 < (a * (γ u - z)).re) :
    ∃ havoid : ∀ u : I, γ u ≠ z,
      unitPositionalIndex γ hclosed z havoid = 0 := by
  have ha : a ≠ 0 := by
    intro h
    have hp := hhalf 0
    rw [h, zero_mul, Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  have havoid : ∀ u : I, γ u ≠ z := by
    intro u h
    have hp := hhalf u
    rw [h, sub_self, mul_zero, Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  let θ : I → ℝ := fun u => (a * (γ u - z)).arg - a.arg
  have hcont : Continuous θ := by
    apply continuous_iff_continuousAt.mpr
    intro u
    have hinner : ContinuousAt (fun v : I => a * (γ v - z)) u :=
      (continuous_const.mul (γ.continuous.sub continuous_const)).continuousAt
    have houter : ContinuousAt Complex.arg (a * (γ u - z)) :=
      Complex.continuousAt_arg (Complex.mem_slitPlane_iff.mpr (Or.inl (hhalf u)))
    have harg : ContinuousAt (fun v : I => (a * (γ v - z)).arg) u :=
      ContinuousAt.comp' (f := fun v : I => a * (γ v - z))
        (g := Complex.arg) (x := u) houter hinner
    exact harg.sub continuousAt_const
  let Γ : C(I, ℝ) := ⟨θ, hcont⟩
  have hΓ : ∀ u : I, (Γ u : Real.Angle) = ((γ u - z).arg : Real.Angle) := by
    intro u
    dsimp [Γ, θ]
    rw [Complex.arg_mul_coe_angle ha (sub_ne_zero.mpr (havoid u))]
    abel
  have hΓclosed : Γ 1 = Γ 0 := by
    dsimp [Γ, θ]
    rw [hclosed]
  exact ⟨havoid, unitPositionalIndex_zero_of_closed_lift γ hclosed z havoid
    Γ hΓ hΓclosed⟩

end DirectGLSSW.HOMFLY.PositionalIndex


