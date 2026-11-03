import RoundedComponentRegularity
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- A positional argument lift for a closed curve separated from the probe by an
oriented affine line. The lift is explicit and periodic; no winding index is
assigned by fiat. This is a supporting geometric lemma, not the basepoint theorem. -/
theorem exists_periodic_positional_argument_of_halfplane
    (γ : ℝ → ℂ) (T : ℝ) (hγ : Continuous γ) (hperiod : Function.Periodic γ T)
    (a z : ℂ) (b : ℝ) (ha : a ≠ 0)
    (hhalf : ∀ t, b ≤ (a * γ t).re) (hz : (a * z).re < b) :
    (∀ t, γ t ≠ z) ∧ ∃ θ : ℝ → ℝ,
      Continuous θ ∧ Function.Periodic θ T ∧
      (∀ t, (θ t : Real.Angle) = ((γ t - z).arg : Real.Angle)) ∧
      θ T - θ 0 = 0 := by
  have hpos (t : ℝ) : 0 < (a * (γ t - z)).re := by
    rw [mul_sub, Complex.sub_re]
    linarith [hhalf t]
  have havoid (t : ℝ) : γ t ≠ z := by
    intro heq
    have hp := hpos t
    rw [heq, sub_self, mul_zero, Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  let θ : ℝ → ℝ := fun t => (a * (γ t - z)).arg - a.arg
  have hcont : Continuous θ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hinner : ContinuousAt (fun u : ℝ => a * (γ u - z)) t :=
      (continuous_const.mul (hγ.sub continuous_const)).continuousAt
    have houter : ContinuousAt Complex.arg (a * (γ t - z)) :=
      Complex.continuousAt_arg (Complex.mem_slitPlane_iff.mpr (Or.inl (hpos t)))
    have harg : ContinuousAt (fun u : ℝ => (a * (γ u - z)).arg) t :=
      ContinuousAt.comp' (f := fun u : ℝ => a * (γ u - z))
        (g := Complex.arg) (x := t) houter hinner
    exact harg.sub continuousAt_const
  have hp : Function.Periodic θ T := by
    intro t
    dsimp [θ]
    rw [hperiod t]
  refine ⟨havoid, θ, hcont, hp, ?_, ?_⟩
  · intro t
    dsimp [θ]
    rw [Complex.arg_mul_coe_angle ha (sub_ne_zero.mpr (havoid t))]
    abel
  · have h := hp 0
    simpa only [zero_add, sub_eq_zero] using h

/-- Literal actual-curve specialization. The half-plane geometry remains an
explicit input to be discharged by the supporting-root/rounding providers. -/
theorem actual_rounded_exists_periodic_positional_argument_of_halfplane
    (D : PLLinkDiagram) (e : Fin D.nArc) (δ : RoundingFraction)
    (a z : ℂ) (b : ℝ) (ha : a ≠ 0)
    (hhalf : ∀ t, b ≤ (a * roundedComponentCurve D e δ t).re)
    (hz : (a * z).re < b) :
    (∀ t, roundedComponentCurve D e δ t ≠ z) ∧ ∃ θ : ℝ → ℝ,
      Continuous θ ∧ Function.Periodic θ (componentArcLength D e : ℝ) ∧
      (∀ t, (θ t : Real.Angle) =
        ((roundedComponentCurve D e δ t - z).arg : Real.Angle)) ∧
      θ (componentArcLength D e : ℝ) - θ 0 = 0 :=
  exists_periodic_positional_argument_of_halfplane
    (roundedComponentCurve D e δ) (componentArcLength D e : ℝ)
    (roundedComponentCurve_continuous D e δ) (roundedComponentCurve_periodic D e δ)
    a z b ha hhalf hz

end DirectGLSSW.HOMFLY.PrincipalTurning



