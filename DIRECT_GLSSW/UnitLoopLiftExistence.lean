import AnglePathLift

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex

/-- The literal continuous unit-interval path has a unique normalized positional
argument lift. This carrier includes the existing actual componentPLLoop. -/
theorem existsUnique_unit_positional_lift (γ : C(I, ℂ)) (z : ℂ)
    (havoid : ∀ u, γ u ≠ z) :
    ∃! Γ : C(I, ℝ), Γ 0 = (γ 0-z).arg ∧
      ∀ u : I, (Γ u : Real.Angle) = ((γ u-z).arg : Real.Angle) := by
  have hcont : Continuous (fun u : I => ((γ u-z).arg : Real.Angle)) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    have hinner : ContinuousAt (fun v : I => γ v-z) u :=
      (γ.continuous.sub continuous_const).continuousAt
    have houter : ContinuousAt (fun w : ℂ => (w.arg : Real.Angle)) (γ u-z) :=
      Complex.continuousAt_arg_coe_angle (sub_ne_zero.mpr (havoid u))
    exact ContinuousAt.comp' (f := fun v : I => γ v-z)
      (g := fun w : ℂ => (w.arg : Real.Angle)) (x := u) houter hinner
  let α : C(I, Real.Angle) := ⟨_,hcont⟩
  exact existsUnique_angle_path_lift α (γ 0-z).arg rfl

/-- A closed literal path has a uniquely characterized integer positional increment.
There are no supplied lifts, integrality assumptions or rotation-number inputs. -/
theorem existsUnique_unit_positional_increment (γ : C(I, ℂ))
    (hclosed : γ 1 = γ 0) (z : ℂ) (havoid : ∀ u, γ u ≠ z) :
    ∃! n : ℤ, ∃ Γ : C(I, ℝ),
      (Γ 0 = (γ 0-z).arg ∧ ∀ u : I, (Γ u : Real.Angle) = ((γ u-z).arg : Real.Angle)) ∧
      Γ 1-Γ 0 = (n:ℝ)*(2*Real.pi) := by
  obtain ⟨Γ,hΓ,hunique⟩ := existsUnique_unit_positional_lift γ z havoid
  have hcoe : ((Γ 1-Γ 0 : ℝ) : Real.Angle) = 0 := by
    rw [Real.Angle.coe_sub, hΓ.2, hΓ.2, hclosed, sub_self]
  obtain ⟨n,hn⟩ := Real.Angle.coe_eq_zero_iff.mp hcoe
  have hn' : Γ 1-Γ 0 = (n:ℝ)*(2*Real.pi) := by
    simpa only [zsmul_eq_mul] using hn.symm
  refine ⟨n,⟨Γ,hΓ,hn'⟩,?_⟩
  rintro m ⟨Λ,hΛ,hm⟩
  have heq : Λ = Γ := hunique Λ hΛ
  subst Λ
  have hcast : (m:ℝ) = (n:ℝ) :=
    mul_right_cancel₀ (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero)
      (hm.symm.trans hn')
  exact_mod_cast hcast

end DirectGLSSW.HOMFLY.PositionalIndex


