import PrincipalTurning

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open scoped BigOperators
open DirectGLSSW.PermutationOrbits

/-- Total actual tangent turn on one actual continuation-orbit fibre. -/
noncomputable def componentTotalTurn (D : PLLinkDiagram) (C : Component D.continuation) : ℝ :=
  ∑ e : Fibre D.continuation C, turn D e.val

theorem componentTotalTurn_coe_angle_zero (D : PLLinkDiagram) (C : Component D.continuation) :
    (componentTotalTurn D C : Real.Angle) = 0 := by
  change Real.Angle.coeHom (∑ e : Fibre D.continuation C, turn D e.val) = 0
  rw [map_sum]
  simp only [Real.Angle.coe_coeHom, turn,
    Complex.arg_div_coe_angle (arcVector_ne_zero D _) (arcVector_ne_zero D _)]
  rw [Finset.sum_sub_distrib]
  have hs : (∑ e : Fibre D.continuation C, ((arcVector D (D.continuation e.val)).arg : Real.Angle)) =
      ∑ e : Fibre D.continuation C, ((arcVector D e.val).arg : Real.Angle) :=
    Fintype.sum_equiv (fibrePerm D.continuation C) _ _ (fun _ => rfl)
  rw [hs, sub_self]

theorem existsUnique_componentTurnInteger (D : PLLinkDiagram) (C : Component D.continuation) :
    ∃! r : ℤ, componentTotalTurn D C = (r : ℝ) * (2 * Real.pi) := by
  obtain ⟨r, hr⟩ := Real.Angle.coe_eq_zero_iff.mp (componentTotalTurn_coe_angle_zero D C)
  refine ⟨r, ?_, ?_⟩
  · simpa only [zsmul_eq_mul] using hr.symm
  · intro s hs
    have hr' : componentTotalTurn D C = (r : ℝ) * (2 * Real.pi) := by
      simpa only [zsmul_eq_mul] using hr.symm
    have hcast : (s : ℝ) = (r : ℝ) :=
      mul_right_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
        (hs.symm.trans hr')
    exact_mod_cast hcast

noncomputable def componentTurnInteger (D : PLLinkDiagram) (C : Component D.continuation) : ℤ :=
  Classical.choose (existsUnique_componentTurnInteger D C)

theorem componentTotalTurn_eq_integer (D : PLLinkDiagram) (C : Component D.continuation) :
    componentTotalTurn D C = (componentTurnInteger D C : ℝ) * (2 * Real.pi) :=
  (Classical.choose_spec (existsUnique_componentTurnInteger D C)).1

theorem totalTurn_eq_sum_components (D : PLLinkDiagram) :
    totalTurn D = ∑ C : Component D.continuation, componentTotalTurn D C := by
  unfold totalTurn componentTotalTurn
  rw [← Fintype.sum_equiv (fibresEquiv D.continuation)
    (fun x => turn D x.2.val) (fun e => turn D e) (fun _ => rfl)]
  exact Fintype.sum_sigma _

theorem turnInteger_eq_sum_components (D : PLLinkDiagram) :
    turnInteger D = ∑ C : Component D.continuation, componentTurnInteger D C := by
  apply turnInteger_unique
  calc
    totalTurn D = ∑ C : Component D.continuation, componentTotalTurn D C :=
      totalTurn_eq_sum_components D
    _ = ∑ C : Component D.continuation, (componentTurnInteger D C : ℝ) * (2 * Real.pi) := by
      apply Finset.sum_congr rfl
      intro C _
      exact componentTotalTurn_eq_integer D C
    _ = (∑ C : Component D.continuation, (componentTurnInteger D C : ℝ)) * (2 * Real.pi) :=
      (Finset.sum_mul _ _ _).symm
    _ = _ := by norm_cast

end DirectGLSSW.HOMFLY.PrincipalTurning



