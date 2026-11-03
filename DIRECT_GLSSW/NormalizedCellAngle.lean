import OrbitTurningPrimitive

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Actual corner angle, constant along the retained straight arc. The clamp
extends the cell outside [0,1] continuously without changing its actual part. -/
noncomputable def normalizedCellAngle (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) : ℝ :=
  cornerAngleLift D e (min 1 (max 0 (t / (2 * δ.val))))

theorem normalizedCellAngle_continuous (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) : Continuous (normalizedCellAngle D e δ) := by
  apply (cornerAngleLift_continuousOn D e).comp_continuous
    (continuous_const.min (continuous_const.max (continuous_id.div_const (2 * δ.val))))
  intro t
  exact ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩

theorem normalizedCellAngle_endpoints (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) :
    normalizedCellAngle D e δ 0 = 0 ∧ normalizedCellAngle D e δ 1 = turn D e := by
  constructor
  · simp [normalizedCellAngle, (cornerAngleLift_endpoints D e).1]
  · have hd : 1 ≤ max 0 (1 / (2 * δ.val)) :=
      (roundingStepDuration_gt_one δ).le.trans (le_max_right _ _)
    rw [normalizedCellAngle, min_eq_left hd, (cornerAngleLift_endpoints D e).2]

theorem turn_coe_angle (D : PLLinkDiagram) (e : Fin D.nArc) :
    (turn D e : Real.Angle) = (arcVector D (D.continuation e)).arg -
      (arcVector D e).arg :=
  Complex.arg_div_coe_angle (arcVector_ne_zero D _) (arcVector_ne_zero D _)

theorem normalizedCellAngle_actual_tangent (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    ((arcVector D e).arg + normalizedCellAngle D e δ t : Real.Angle) =
      ((normalizedRoundedVelocity D e δ t).arg : Real.Angle) := by
  have hp : 0 < 2 * δ.val := mul_pos (by norm_num) δ.property.1
  have hn : 0 ≤ t / (2 * δ.val) := div_nonneg ht.1 hp.le
  rw [normalizedRoundedVelocity, Complex.real_smul,
    Complex.arg_real_mul _ (one_div_pos.mpr hp)]
  by_cases h : t / (2 * δ.val) ≤ 1
  · rw [normalizedCellAngle, max_eq_right hn, min_eq_right h]
    simp only [roundedStepVelocity, h, if_true]
    have hv := roundedCorner_regular D e δ.val (t / (2 * δ.val)) δ.property.1 ⟨hn,h⟩
    have ha : (cornerAngleLift D e (t / (2 * δ.val)) : Real.Angle) =
        ((roundedCornerDerivative D e δ.val (t / (2 * δ.val))).arg : Real.Angle) -
          ((arcVector D e).arg : Real.Angle) := by
      rw [← roundedCorner_angleLift D e δ.val _ δ.property.1]
      exact Complex.arg_div_coe_angle hv (arcVector_ne_zero D e)
    rw [ha]
    abel
  · have hd : 1 ≤ max 0 (t / (2 * δ.val)) := (not_le.mp h).le.trans (le_max_right _ _)
    rw [normalizedCellAngle, min_eq_left hd, (cornerAngleLift_endpoints D e).2]
    simp only [roundedStepVelocity, h, if_false, Complex.real_smul]
    rw [Complex.arg_real_mul _ hp, turn_coe_angle]
    abel

end DirectGLSSW.HOMFLY.PrincipalTurning



