import ImmersedRoundingCells

set_option autoImplicit false
namespace DirectGLSSW.ImmersedGlobalRounding
open DirectGLSSW.HOMFLY.PrincipalTurning DirectGLSSW.ImmersedPolygonRotation
noncomputable def relative (v w : ℂ) (t : ℝ) : ℂ :=
  ((1-t:ℝ):ℂ)+(t:ℂ)*(w/v)
noncomputable def cellAngle (v w : ℂ) (δ : RoundingFraction) (t : ℝ) : ℝ :=
  (relative v w (min 1 (max 0 (t/(2*δ.val))))).arg

theorem relative_continuous (v w : ℂ) : Continuous (relative v w) := by
  unfold relative
  fun_prop

theorem cellAngle_continuous (v w : ℂ) (hshort : w/v ∈ Complex.slitPlane)
    (δ : RoundingFraction) : Continuous (cellAngle v w δ) := by
  have hlocal : ContinuousOn (fun t => (relative v w t).arg) (Set.Icc (0:ℝ) 1) := by
    intro t ht
    exact (ContinuousAt.comp' (f := relative v w) (g := Complex.arg) (x := t)
      (Complex.continuousAt_arg (relative_tangent_mem_slitPlane _ hshort t ht))
      (relative_continuous v w).continuousAt).continuousWithinAt
  apply hlocal.comp_continuous
    (continuous_const.min (continuous_const.max (continuous_id.div_const (2*δ.val))))
  intro t
  exact ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩

theorem cellAngle_endpoints (v w : ℂ) (δ : RoundingFraction) :
    cellAngle v w δ 0 = 0 ∧ cellAngle v w δ 1 = (w/v).arg := by
  constructor
  · simp [cellAngle,relative]
  · have hd : 1 ≤ max 0 (1/(2*δ.val)) :=
      (roundingStepDuration_gt_one δ).le.trans (le_max_right _ _)
    rw [cellAngle,min_eq_left hd]
    simp [relative]

theorem cellAngle_velocity (v w : ℂ) (hv : v ≠ 0) (hw : w ≠ 0)
    (hshort : w/v ∈ Complex.slitPlane) (δ : RoundingFraction)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ((v.arg+cellAngle v w δ t : ℝ) : Real.Angle) = (velocity v w δ t).arg := by
  have hp : 0 < 2*δ.val := mul_pos (by norm_num) δ.property.1
  have hn : 0 ≤ t/(2*δ.val) := div_nonneg ht.1 hp.le
  rw [velocity,Complex.real_smul,Complex.arg_real_mul _ (one_div_pos.mpr hp)]
  by_cases h : t/(2*δ.val) ≤ 1
  · rw [cellAngle,max_eq_right hn,min_eq_right h]
    simp only [stepVelocity,h,if_true,cornerVelocity,Complex.real_smul]
    rw [Complex.arg_real_mul _ hp]
    rw [← Complex.real_smul,← Complex.real_smul,bezier_tangent_factor v w hv]
    rw [Complex.arg_mul_coe_angle hv
      (Complex.slitPlane_ne_zero (relative_tangent_mem_slitPlane _ hshort _ ⟨hn,h⟩))]
    rfl
  · have hd : 1 ≤ max 0 (t/(2*δ.val)) := (not_le.mp h).le.trans (le_max_right _ _)
    rw [cellAngle,min_eq_left hd]
    simp only [relative,sub_self,Complex.ofReal_zero,Complex.ofReal_one,zero_add,one_mul]
    simp only [stepVelocity,h,if_false,Complex.real_smul]
    rw [Complex.arg_real_mul _ hp,Real.Angle.coe_add,Complex.arg_div_coe_angle hw hv]
    abel
end DirectGLSSW.ImmersedGlobalRounding



