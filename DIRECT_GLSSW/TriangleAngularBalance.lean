import PrincipalTurning
import Mathlib.Analysis.Convex.Hull

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Exact integer classification for three strict principal increments. -/
theorem three_angle_balance (x y z : ℝ)
    (hx : -Real.pi < x ∧ x < Real.pi) (hy : -Real.pi < y ∧ y < Real.pi)
    (hz : -Real.pi < z ∧ z < Real.pi)
    (ha : ((x+y+z : ℝ) : Real.Angle) = 0) :
    x+y+z = if 0<x ∧ 0<y ∧ 0<z then 2*Real.pi
      else if x<0 ∧ y<0 ∧ z<0 then -(2*Real.pi) else 0 := by
  obtain ⟨k,hk⟩ := Real.Angle.coe_eq_zero_iff.mp ha
  have hs : x+y+z = (k : ℝ)*(2*Real.pi) := by simpa only [zsmul_eq_mul] using hk.symm
  have hklo : (-2 : ℤ) < k := by
    have h : (-2 : ℝ) < (k : ℝ) := by nlinarith [Real.pi_pos]
    exact_mod_cast h
  have hkhi : k < (2 : ℤ) := by
    have h : (k : ℝ) < (2 : ℝ) := by nlinarith [Real.pi_pos]
    exact_mod_cast h
  have hp : k=1 ↔ 0<x ∧ 0<y ∧ 0<z := by
    constructor
    · intro h; subst k; norm_num at hs
      exact ⟨by linarith,by linarith,by linarith⟩
    · rintro ⟨h1,h2,h3⟩
      have h : (0 : ℝ)<(k : ℝ) := by nlinarith [Real.pi_pos]
      have hi : (0 : ℤ)<k := by exact_mod_cast h
      omega
  have hn : k= -1 ↔ x<0 ∧ y<0 ∧ z<0 := by
    constructor
    · intro h; subst k; norm_num at hs
      exact ⟨by linarith,by linarith,by linarith⟩
    · rintro ⟨h1,h2,h3⟩
      have h : (k : ℝ)<0 := by nlinarith [Real.pi_pos]
      have hi : k<(0 : ℤ) := by exact_mod_cast h
      omega
  split_ifs with hpos hneg
  · rw [← hp] at hpos; subst k; simpa using hs
  · rw [← hn] at hneg; subst k; simpa using hs
  · have h0 : k=0 := by
      have h1 : k≠1 := fun h => hpos (hp.mp h)
      have hm : k≠ -1 := fun h => hneg (hn.mp h)
      omega
    subst k; simpa using hs

theorem segment_avoids_zero_arg_lt_pi (a b : ℂ)
    (h : (0 : ℂ) ∉ segment ℝ a b) : Complex.arg (b/a) < Real.pi := by
  have ha : a≠0 := fun he => h (he ▸ left_mem_segment ℝ a b)
  apply lt_of_le_of_ne (Complex.arg_le_pi _)
  intro hp
  obtain ⟨hr,hi⟩ := Complex.arg_eq_pi_iff.mp hp
  let r : ℝ := (b/a).re
  have hb : b = r • a := by
    have he : b/a = (r : ℂ) := by apply Complex.ext <;> simp [r,hi]
    simpa only [Complex.real_smul] using (div_eq_iff ha).mp he
  have hd : 0<1-r := by dsimp [r]; linarith
  apply h
  refine ⟨-r/(1-r),1/(1-r),div_nonneg (by dsimp [r]; linarith) hd.le,
    (one_div_pos.mpr hd).le,?_,?_⟩
  · field_simp <;> ring
  · rw [hb,smul_smul,← add_smul]
    have hc : -r/(1-r)+(1/(1-r))*r=0 := by field_simp <;> ring
    rw [hc,zero_smul]

/-- Complete angular balance for a literal affine triangle avoiding zero on
all three boundary segments; determinant/interior identification follows. -/
theorem triangle_principal_angle_balance (a b c : ℂ)
    (hab : (0 : ℂ) ∉ segment ℝ a b)
    (hbc : (0 : ℂ) ∉ segment ℝ b c)
    (hca : (0 : ℂ) ∉ segment ℝ c a) :
    Complex.arg (b/a)+Complex.arg (c/b)+Complex.arg (a/c) =
      if 0<Complex.arg (b/a) ∧ 0<Complex.arg (c/b) ∧ 0<Complex.arg (a/c)
      then 2*Real.pi else
      if Complex.arg (b/a)<0 ∧ Complex.arg (c/b)<0 ∧ Complex.arg (a/c)<0
      then -(2*Real.pi) else 0 := by
  have ha : a≠0 := fun he => hab (he ▸ left_mem_segment ℝ a b)
  have hb : b≠0 := fun he => hbc (he ▸ left_mem_segment ℝ b c)
  have hc : c≠0 := fun he => hca (he ▸ left_mem_segment ℝ c a)
  apply three_angle_balance
    _ _ _ ⟨Complex.neg_pi_lt_arg _,segment_avoids_zero_arg_lt_pi a b hab⟩
    ⟨Complex.neg_pi_lt_arg _,segment_avoids_zero_arg_lt_pi b c hbc⟩
    ⟨Complex.neg_pi_lt_arg _,segment_avoids_zero_arg_lt_pi c a hca⟩
  rw [Real.Angle.coe_add,Real.Angle.coe_add,
    Complex.arg_div_coe_angle hb ha,Complex.arg_div_coe_angle hc hb,
    Complex.arg_div_coe_angle ha hc]
  abel

end DirectGLSSW.HOMFLY.PrincipalTurning



