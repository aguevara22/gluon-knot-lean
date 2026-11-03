import UnitLoopLiftExistence

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex

/-- Genuine positional winding integer of a continuous closed loop about an
excluded point, selected only from the independently audited unique increment. -/
noncomputable def unitPositionalIndex (γ : C(I, ℂ)) (hclosed : γ 1 = γ 0)
    (z : ℂ) (havoid : ∀ u, γ u ≠ z) : ℤ :=
  Classical.choose (existsUnique_unit_positional_increment γ hclosed z havoid)

/-- Complete defining characterization on the entire continuous closed-loop carrier. -/
theorem unitPositionalIndex_characterization (γ : C(I, ℂ)) (hclosed : γ 1 = γ 0)
    (z : ℂ) (havoid : ∀ u, γ u ≠ z) :
    ∃ Γ : C(I, ℝ),
      (Γ 0 = (γ 0-z).arg ∧ ∀ u : I, (Γ u : Real.Angle) = ((γ u-z).arg : Real.Angle)) ∧
      Γ 1-Γ 0 = (unitPositionalIndex γ hclosed z havoid : ℝ)*(2*Real.pi) :=
  (Classical.choose_spec (existsUnique_unit_positional_increment γ hclosed z havoid)).1

/-- The characterization determines the chosen integer uniquely. -/
theorem unitPositionalIndex_unique (γ : C(I, ℂ)) (hclosed : γ 1 = γ 0)
    (z : ℂ) (havoid : ∀ u, γ u ≠ z) (n : ℤ)
    (hn : ∃ Γ : C(I, ℝ),
      (Γ 0 = (γ 0-z).arg ∧ ∀ u : I, (Γ u : Real.Angle) = ((γ u-z).arg : Real.Angle)) ∧
      Γ 1-Γ 0 = (n:ℝ)*(2*Real.pi)) : n = unitPositionalIndex γ hclosed z havoid :=
  (Classical.choose_spec (existsUnique_unit_positional_increment γ hclosed z havoid)).2 n hn

theorem unitPositionalIndex_eq_iff (γ : C(I, ℂ)) (hclosed : γ 1 = γ 0)
    (z : ℂ) (havoid : ∀ u, γ u ≠ z) (n : ℤ) :
    unitPositionalIndex γ hclosed z havoid = n ↔
      ∃ Γ : C(I, ℝ),
        (Γ 0 = (γ 0-z).arg ∧ ∀ u : I, (Γ u : Real.Angle) = ((γ u-z).arg : Real.Angle)) ∧
        Γ 1-Γ 0 = (n:ℝ)*(2*Real.pi) := by
  constructor
  · intro h
    rw [← h]
    exact unitPositionalIndex_characterization γ hclosed z havoid
  · intro h
    exact (unitPositionalIndex_unique γ hclosed z havoid n h).symm

/-- Every continuous real argument lift, regardless of its initial value, has
exactly the index increment. No normalized-lift choice enters this conclusion. -/
theorem unitPositionalIndex_any_lift (γ : C(I, ℂ)) (hclosed : γ 1 = γ 0)
    (z : ℂ) (havoid : ∀ u, γ u ≠ z) (Γ : C(I, ℝ))
    (hΓ : ∀ u : I, (Γ u : Real.Angle) = ((γ u-z).arg : Real.Angle)) :
    Γ 1-Γ 0 = (unitPositionalIndex γ hclosed z havoid : ℝ)*(2*Real.pi) := by
  obtain ⟨Λ,hΛ,hinc⟩ := unitPositionalIndex_characterization γ hclosed z havoid
  have hd := angle_lift_difference_constant Γ Λ Γ.continuous Λ.continuous
    (fun u => (hΓ u).trans (hΛ.2 u).symm) (1:I) (0:I)
  linarith

/-- A closed continuous real positional argument forces genuine index zero. -/
theorem unitPositionalIndex_zero_of_closed_lift
    (γ : C(I, ℂ)) (hclosed : γ 1 = γ 0)
    (z : ℂ) (havoid : ∀ u, γ u ≠ z) (Γ : C(I, ℝ))
    (hΓ : ∀ u : I, (Γ u : Real.Angle) = ((γ u-z).arg : Real.Angle))
    (hΓclosed : Γ 1 = Γ 0) : unitPositionalIndex γ hclosed z havoid = 0 := by
  have hi := unitPositionalIndex_any_lift γ hclosed z havoid Γ hΓ
  rw [hΓclosed, sub_self] at hi
  have hzero : (unitPositionalIndex γ hclosed z havoid : ℝ) = 0 :=
    (mul_eq_zero.mp hi.symm).resolve_right
      (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero)
  exact_mod_cast hzero

end DirectGLSSW.HOMFLY.PositionalIndex






