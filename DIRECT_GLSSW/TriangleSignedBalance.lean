import TriangleAngularBalance

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

def complexDet (a b : ℂ) : ℝ := a.re*b.im-a.im*b.re

theorem arg_pos_iff_im_pos_of_lt_pi (z : ℂ) (hπ : z.arg<Real.pi) :
    0<z.arg ↔ 0<z.im := by
  constructor
  · intro h
    have hs := Real.sin_pos_of_pos_of_lt_pi h hπ
    rw [Complex.sin_arg] at hs
    exact (div_pos_iff_of_pos_right (norm_pos_iff.mpr (by
      intro hz; simp [hz] at h))).mp hs
  · intro h
    have hn := Complex.arg_nonneg_iff.mpr h.le
    apply lt_of_le_of_ne hn
    intro he
    have him := (Complex.arg_eq_zero_iff.mp he.symm).2
    linarith

theorem quotient_im_det (a b : ℂ) : (b/a).im=complexDet a b/Complex.normSq a := by
  rw [Complex.div_im]
  unfold complexDet
  ring

theorem triangle_angle_positive_iff (a b : ℂ) (h : (0 : ℂ) ∉ segment ℝ a b) :
    0<Complex.arg (b/a) ↔ 0<complexDet a b := by
  have ha : a≠0 := fun he => h (he ▸ left_mem_segment ℝ a b)
  rw [arg_pos_iff_im_pos_of_lt_pi _ (segment_avoids_zero_arg_lt_pi a b h),quotient_im_det]
  exact div_pos_iff_of_pos_right (Complex.normSq_pos.mpr ha)

theorem triangle_angle_negative_iff (a b : ℂ) (h : (0 : ℂ) ∉ segment ℝ a b) :
    Complex.arg (b/a)<0 ↔ complexDet a b<0 := by
  have ha : a≠0 := fun he => h (he ▸ left_mem_segment ℝ a b)
  rw [Complex.arg_neg_iff,quotient_im_det]
  rw [div_lt_iff₀ (Complex.normSq_pos.mpr ha),zero_mul]

/-- Signed affine boundary-angle balance, with geometric edge-origin
orientation determinants. No angular sign or degree premise. -/
theorem triangle_signed_angle_balance (a b c : ℂ)
    (hab : (0 : ℂ) ∉ segment ℝ a b)
    (hbc : (0 : ℂ) ∉ segment ℝ b c)
    (hca : (0 : ℂ) ∉ segment ℝ c a) :
    Complex.arg (b/a)+Complex.arg (c/b)+Complex.arg (a/c) =
      if 0<complexDet a b ∧ 0<complexDet b c ∧ 0<complexDet c a
      then 2*Real.pi else
      if complexDet a b<0 ∧ complexDet b c<0 ∧ complexDet c a<0
      then -(2*Real.pi) else 0 := by
  rw [triangle_principal_angle_balance a b c hab hbc hca]
  simp only [
    triangle_angle_positive_iff a b hab,triangle_angle_positive_iff b c hbc,
    triangle_angle_positive_iff c a hca,triangle_angle_negative_iff a b hab,
    triangle_angle_negative_iff b c hbc,triangle_angle_negative_iff c a hca]

theorem complexDet_triangle_orientation (a b c : ℂ) :
    complexDet (b-a) (c-a) = complexDet a b+complexDet b c+complexDet c a := by
  simp only [complexDet,Complex.sub_re,Complex.sub_im]
  ring

/-- The degenerate affine-image case has zero boundary angular increment,
derived from boundary avoidance; no nondegeneracy hypothesis is added. -/
theorem degenerate_triangle_angle_balance (a b c : ℂ)
    (hab : (0 : ℂ) ∉ segment ℝ a b)
    (hbc : (0 : ℂ) ∉ segment ℝ b c)
    (hca : (0 : ℂ) ∉ segment ℝ c a)
    (hd : complexDet (b-a) (c-a)=0) :
    Complex.arg (b/a)+Complex.arg (c/b)+Complex.arg (a/c)=0 := by
  have hs := complexDet_triangle_orientation a b c
  rw [hd] at hs
  rw [triangle_signed_angle_balance a b c hab hbc hca]
  have hp : ¬(0<complexDet a b ∧ 0<complexDet b c ∧ 0<complexDet c a) := by
    rintro ⟨h1,h2,h3⟩; linarith
  have hn : ¬(complexDet a b<0 ∧ complexDet b c<0 ∧ complexDet c a<0) := by
    rintro ⟨h1,h2,h3⟩; linarith
  rw [if_neg hp,if_neg hn]

end DirectGLSSW.HOMFLY.PrincipalTurning





