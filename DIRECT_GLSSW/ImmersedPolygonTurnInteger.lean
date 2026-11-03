import PolygonPrincipalTurns

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open scoped BigOperators

/-- Angle telescoping needs only actual nonzero cyclic edges. Neither distant
incidence genericity nor nonzero corner determinant enters this statement. -/
theorem originalCornerTotalTurn_coe_zero_of_edges
    {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0) :
    (originalCornerTotalTurn q : Real.Angle) = 0 := by
  change Real.Angle.coeHom (∑ i : Fin n, originalCornerTurn q i) = 0
  rw [map_sum]
  simp only [Real.Angle.coe_coeHom, originalCornerTurn,
    Complex.arg_div_coe_angle (hedge _) (hedge _)]
  rw [Finset.sum_sub_distrib]
  have hs : (∑ i : Fin n,
      ((polygonEdgeVector q ((cyclicSuccessorPerm n).symm i)).arg : Real.Angle)) =
      ∑ i : Fin n, ((polygonEdgeVector q i).arg : Real.Angle) :=
    Fintype.sum_equiv (cyclicSuccessorPerm n).symm _ _ (fun _ => rfl)
  rw [hs,sub_self]

/-- Raw unique integer characterization on the full nonzero-edge domain.
No rotation integer is defined here, and no genericity is assumed. -/
theorem originalCornerTotalTurn_existsUnique_integer_of_edges
    {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0) :
    ∃! r : ℤ, originalCornerTotalTurn q = (r : ℝ)*(2*Real.pi) := by
  obtain ⟨r,hr⟩ := Real.Angle.coe_eq_zero_iff.mp
    (originalCornerTotalTurn_coe_zero_of_edges q hedge)
  have hr' : originalCornerTotalTurn q = (r : ℝ)*(2*Real.pi) := by
    simpa only [zsmul_eq_mul] using hr.symm
  refine ⟨r,hr',?_⟩
  intro s hs
  have hcast : (s:ℝ) = (r:ℝ) := mul_right_cancel₀
    (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero) (hs.symm.trans hr')
  exact_mod_cast hcast

end DirectGLSSW.HOMFLY.PolygonDrawingBridge


