import RoundedStep
import HOMFLYComponentPLPath

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open scoped Topology

noncomputable def roundedStepVelocity (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) : ℂ :=
  if t ≤ 1 then roundedCornerDerivative D e δ.val t
  else (2 * δ.val) • arcVector D (D.continuation e)

/-- Actual derivative everywhere on the corner/straight cell, including its join. -/
theorem roundedStep_hasDerivAt (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) :
    HasDerivAt (roundedStep D e δ) (roundedStepVelocity D e δ t) t := by
  rcases lt_trichotomy t 1 with ht | ht | ht
  · have h : HasDerivWithinAt (roundedStep D e δ)
        (roundedCornerDerivative D e δ.val t) (Set.Iic 1) t := by
      apply (roundedCorner_hasDerivAt D e δ.val t).hasDerivWithinAt.congr
      · intro x hx
        have hx' : x ≤ 1 := hx
        simp [roundedStep, hx']
      · simp [roundedStep, ht.le]
    simpa [roundedStepVelocity, ht.le] using h.hasDerivAt (Iic_mem_nhds ht)
  · subst t
    simpa [roundedStepVelocity, roundedStep_join_derivative] using
      roundedStep_hasDerivAt_join D e δ
  · have h : HasDerivWithinAt (roundedStep D e δ)
        ((2 * δ.val) • arcVector D (D.continuation e)) (Set.Ici 1) t := by
      apply (roundingStraight_hasDerivAt D e δ t).hasDerivWithinAt.congr
      · intro x hx
        by_cases hx' : x ≤ 1
        · have heq : x = 1 := le_antisymm hx' hx
          subst x
          simp only [roundedStep, le_refl, if_true]
          exact roundedStep_join D e δ
        · simp [roundedStep, hx']
      · simp [roundedStep, not_le.mpr ht]
    simpa [roundedStepVelocity, not_le.mpr ht] using h.hasDerivAt (Ici_mem_nhds ht)

noncomputable def normalizedRoundedCell (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) : ℂ :=
  roundedStep D e δ (t / (2 * δ.val))

noncomputable def normalizedRoundedVelocity (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) : ℂ :=
  (1 / (2 * δ.val)) • roundedStepVelocity D e δ (t / (2 * δ.val))

theorem normalizedRoundedCell_hasDerivAt (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) :
    HasDerivAt (normalizedRoundedCell D e δ) (normalizedRoundedVelocity D e δ t) t := by
  simpa only [normalizedRoundedCell, normalizedRoundedVelocity, one_div] using
    (roundedStep_hasDerivAt D e δ (t / (2 * δ.val))).scomp t
      ((hasDerivAt_id t).div_const (2 * δ.val))

theorem roundedStepVelocity_ne_zero (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) (ht : t ∈ Set.Icc 0 (roundingStepDuration δ)) :
    roundedStepVelocity D e δ t ≠ 0 := by
  unfold roundedStepVelocity
  split_ifs with h
  · exact roundedCorner_regular D e δ.val t δ.property.1 ⟨ht.1,h⟩
  · rw [Complex.real_smul]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (mul_pos (by norm_num) δ.property.1))) (arcVector_ne_zero D _)

theorem normalizedRoundedVelocity_ne_zero (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    normalizedRoundedVelocity D e δ t ≠ 0 := by
  have hp : 0 < 2 * δ.val := mul_pos (by norm_num) δ.property.1
  have hi : t / (2 * δ.val) ∈ Set.Icc 0 (roundingStepDuration δ) :=
    ⟨div_nonneg ht.1 hp.le, div_le_div_of_nonneg_right ht.2 hp.le⟩
  rw [normalizedRoundedVelocity, Complex.real_smul]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (one_div_pos.mpr hp)))
    (roundedStepVelocity_ne_zero D e δ _ hi)

theorem normalizedRoundedCell_join (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) :
    normalizedRoundedCell D e δ 1 = normalizedRoundedCell D (D.continuation e) δ 0 := by
  have hd := roundingStepDuration_gt_one δ
  simp only [normalizedRoundedCell, zero_div]
  rw [show 1 / (2 * δ.val) = roundingStepDuration δ from rfl]
  simp only [roundedStep, not_le.mpr hd, if_false, zero_le_one, if_true]
  exact roundedStep_next_join D e δ

theorem normalizedRoundedVelocity_endpoints (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) :
    normalizedRoundedVelocity D e δ 0 = arcVector D e ∧
    normalizedRoundedVelocity D e δ 1 = arcVector D (D.continuation e) := by
  have hp : 2 * δ.val ≠ 0 := ne_of_gt (mul_pos (by norm_num) δ.property.1)
  have hd := roundingStepDuration_gt_one δ
  have hc : (1 / (2 * δ.val)) * (2 * δ.val) = 1 := by field_simp
  constructor
  · simp only [normalizedRoundedVelocity, zero_div, roundedStepVelocity, zero_le_one,
      if_true, roundedCornerDerivative, cornerTangent, sub_zero, one_smul, zero_smul,
      add_zero, smul_smul, hc, one_smul]
  · simp only [normalizedRoundedVelocity, roundedStepVelocity,
      show ¬ 1 / (2 * δ.val) ≤ 1 from not_le.mpr hd, if_false,
      smul_smul, hc, one_smul]

/-- Uniform-time actual rounded component: each orbit cell has unit duration.
The orbit/period carrier is the same as the checked actual PL component loop. -/
noncomputable def roundedComponentCurve (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) : ℂ :=
  normalizedRoundedCell D ((D.continuation ^ Int.floor t) e) δ (Int.fract t)

theorem roundedComponentCurve_periodic (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) :
    Function.Periodic (roundedComponentCurve D e δ) (componentArcLength D e : ℝ) := by
  intro t
  unfold roundedComponentCurve
  rw [Int.floor_add_natCast, Int.fract_add_natCast, zpow_add, Equiv.Perm.mul_apply,
    zpow_natCast, continuation_pow_componentArcLength]

end DirectGLSSW.HOMFLY.PrincipalTurning






