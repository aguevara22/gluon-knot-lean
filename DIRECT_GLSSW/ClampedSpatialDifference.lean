import SpatialInteriorClamp

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY

def clampedDifference (D : PLLinkDiagram) (e : Fin D.nArc) : C(unitInterval,ℂ) where
  toFun t := splitMainComplex D e (splitClamp D e t) - splitBeta D e (splitClamp D e t)
  continuous_toFun := by fun_prop

theorem clampedDifference_apply (D : PLLinkDiagram) (e : Fin D.nArc) (t : unitInterval) :
    clampedDifference D e t =
      splitMainComplex D e (splitClamp D e t) - splitBeta D e (splitClamp D e t) := rfl

theorem clampedDifference_ne_zero (D : PLLinkDiagram) (e : Fin D.nArc) (t : unitInterval) :
    clampedDifference D e t ≠ 0 := by
  exact sub_ne_zero.mpr (splitMain_avoids_beta D e _
    (splitClamp_interior D e t).1 (splitClamp_interior D e t).2)

/-- Literal tent-radius scale evaluated at the interior clamp. -/
def clampedTentScale (D : PLLinkDiagram) (e : Fin D.nArc) : C(unitInterval,ℝ) where
  toFun t := (min (splitClamp D e t).val (1-(splitClamp D e t).val)/2) / ‖clampedDifference D e t‖
  continuous_toFun := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t
      exact norm_ne_zero_iff.mpr (clampedDifference_ne_zero D e t)

theorem clampedTentScale_apply (D : PLLinkDiagram) (e : Fin D.nArc) (t : unitInterval) :
    clampedTentScale D e t =
      (min (splitClamp D e t).val (1-(splitClamp D e t).val)/2) / ‖clampedDifference D e t‖ := rfl

theorem clampedTentScale_pos (D : PLLinkDiagram) (e : Fin D.nArc) (t : unitInterval) :
    0 < clampedTentScale D e t := by
  rw [clampedTentScale_apply]
  have hi := splitClamp_interior D e t
  apply div_pos
  · exact div_pos (lt_min hi.1 (by linarith)) (by norm_num)
  · exact norm_pos_iff.mpr (clampedDifference_ne_zero D e t)

/-- The clamp changes only positive length, never the interior direction;
the same factor relates the literal triangle's tent radii. -/
theorem split_difference_clamp_proportional (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : unitInterval) : ∃ ρ : ℝ, 0 ≤ ρ ∧
      splitMainComplex D e t - splitBeta D e t = ρ • clampedDifference D e t ∧
      min t.val (1-t.val)/2 = ρ * (min (splitClamp D e t).val (1-(splitClamp D e t).val)/2) := by
  let a := splitClampWidth D e
  have ha : 0 < a := (splitClampWidth_bounds D e).1
  have ha' : a < 1/2 := (splitClampWidth_bounds D e).2.1
  have hNa : ((componentArcLength D e:ℝ)+1)*a = 1/2 := (splitClampWidth_bounds D e).2.2
  have hN : 0 < ((componentArcLength D e:ℝ)+1) := by positivity
  by_cases ht : t.val ≤ a
  · have hc : (splitClamp D e t).val = a := interiorClamp_left a ha ha' t ht
    have hfirst : ((componentArcLength D e:ℝ)+1)*t.val ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left ht hN.le
      linarith
    have hcfirst : ((componentArcLength D e:ℝ)+1)*(splitClamp D e t).val ≤ 1 := by rw [hc,hNa]; norm_num
    refine ⟨t.val/a,div_nonneg t.property.1 ha.le,?_,?_⟩
    · rw [clampedDifference_apply,split_difference_first D e t hfirst,
        split_difference_first D e _ hcfirst,hc,smul_smul]
      congr 1
      field_simp [ne_of_gt ha] <;> ring
    · rw [hc,min_eq_left (by linarith : t.val ≤ 1-t.val),min_eq_left (by linarith : a ≤ 1-a)]
      field_simp [ne_of_gt ha] <;> ring
  · by_cases ht' : 1-a ≤ t.val
    · have hc : (splitClamp D e t).val = 1-a := interiorClamp_right a ha ha' t ht'
      have hlast : (componentArcLength D e:ℝ) ≤ ((componentArcLength D e:ℝ)+1)*t.val := by
        have h := mul_le_mul_of_nonneg_left ht' hN.le
        nlinarith
      have hclast : (componentArcLength D e:ℝ) ≤
          ((componentArcLength D e:ℝ)+1)*(splitClamp D e t).val := by rw [hc]; nlinarith
      refine ⟨(1-t.val)/a,div_nonneg (by linarith [t.property.2]) ha.le,?_,?_⟩
      · rw [clampedDifference_apply,split_difference_last D e t hlast,
          split_difference_last D e _ hclast,hc,smul_smul]
        congr 1
        field_simp [ne_of_gt ha] <;> ring
      · rw [hc,min_eq_right (by linarith : 1-t.val ≤ t.val),
          min_eq_right (by linarith : 1-(1-a) ≤ 1-a)]
        field_simp [ne_of_gt ha] <;> ring
    · have hc : splitClamp D e t = t := interiorClamp_middle a ha ha' t (by linarith) (by linarith)
      refine ⟨1,by norm_num,?_,?_⟩
      · simp only [one_smul,clampedDifference_apply,hc]
      · simp only [hc,one_mul]

end DirectGLSSW.DescendingSpatial





