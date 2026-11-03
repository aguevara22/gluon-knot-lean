import ClampedSpatialDifference

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY

theorem clampedTentScale_norm_identity (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : unitInterval) : clampedTentScale D e t *
      ‖splitMainComplex D e t - splitBeta D e t‖ = min t.val (1-t.val)/2 := by
  obtain ⟨ρ,hρ,hw,hr⟩ := split_difference_clamp_proportional D e t
  have hn : ‖clampedDifference D e t‖ ≠ 0 := norm_ne_zero_iff.mpr (clampedDifference_ne_zero D e t)
  calc
    clampedTentScale D e t * ‖splitMainComplex D e t - splitBeta D e t‖ =
        (min (splitClamp D e t).val (1-(splitClamp D e t).val)/2 / ‖clampedDifference D e t‖) *
          (ρ * ‖clampedDifference D e t‖) := by
      rw [clampedTentScale_apply,hw,norm_smul,Real.norm_eq_abs,abs_of_nonneg hρ]
    _ = ρ * (min (splitClamp D e t).val (1-(splitClamp D e t).val)/2) := by
      field_simp [hn] <;> ring
    _ = min t.val (1-t.val)/2 := hr.symm

theorem clamped_difference_positive_factor (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : unitInterval) (ht0 : 0 < t.val) (ht1 : t.val < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧
      splitMainComplex D e t - splitBeta D e t = ρ • clampedDifference D e t := by
  obtain ⟨ρ,hρ,hw,hr⟩ := split_difference_clamp_proportional D e t
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h,zero_smul] at hw
    exact sub_ne_zero.mpr (splitMain_avoids_beta D e t ht0 ht1) hw
  exact ⟨ρ,lt_of_le_of_ne hρ (Ne.symm hρ0),hw⟩

theorem clamped_difference_arg_eq (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : unitInterval) (ht0 : 0 < t.val) (ht1 : t.val < 1) :
    (splitMainComplex D e t - splitBeta D e t).arg = (clampedDifference D e t).arg := by
  obtain ⟨ρ,hρ,hw⟩ := clamped_difference_positive_factor D e t ht0 ht1
  rw [hw,Complex.real_smul]
  exact Complex.arg_real_mul _ hρ

theorem clamped_difference_normalized_eq (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : unitInterval) (ht0 : 0 < t.val) (ht1 : t.val < 1) :
    (splitMainComplex D e t - splitBeta D e t) /
      (‖splitMainComplex D e t - splitBeta D e t‖ : ℂ) =
    clampedDifference D e t / (‖clampedDifference D e t‖ : ℂ) := by
  obtain ⟨ρ,hρ,hw⟩ := clamped_difference_positive_factor D e t ht0 ht1
  have hρC : (ρ:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
  have hn : (‖clampedDifference D e t‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (clampedDifference_ne_zero D e t)
  rw [hw,norm_smul,Real.norm_eq_abs,abs_of_pos hρ,Complex.real_smul,Complex.ofReal_mul]
  field_simp
  ring


end DirectGLSSW.DescendingSpatial




