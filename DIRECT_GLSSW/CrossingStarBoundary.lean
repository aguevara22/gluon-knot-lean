import CrossingStarWindow

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

theorem straight_side_arg_subdivision (a c : ℂ) (hd : complexDet a c ≠ 0)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    let b := ((1-t : ℝ) : ℂ)*a + (t : ℂ)*c
    Complex.arg (b/a) + Complex.arg (c/b) = Complex.arg (c/a) := by
  let b := ((1-t : ℝ) : ℂ)*a + (t : ℂ)*c
  have habdet : complexDet a b = t * complexDet a c := by
    simp [b, complexDet]; ring
  have hbcdet : complexDet b c = (1-t) * complexDet a c := by
    simp [b, complexDet]; ring
  have hcadet : complexDet c a = -complexDet a c := by unfold complexDet; ring
  have hab := zero_not_mem_segment_of_complexDet_ne_zero a b (by
    rw [habdet]; exact mul_ne_zero (ne_of_gt ht0) hd)
  have hbc := zero_not_mem_segment_of_complexDet_ne_zero b c (by
    rw [hbcdet]; exact mul_ne_zero (ne_of_gt (sub_pos.mpr ht1)) hd)
  have hca := zero_not_mem_segment_of_complexDet_ne_zero c a (by
    rw [hcadet]; exact neg_ne_zero.mpr hd)
  have harea : complexDet (b-a) (c-a) = 0 := by simp [b,complexDet]; ring
  have htriangle := degenerate_triangle_angle_balance a b c hab hbc hca harea
  have hreverse := reciprocal_turns_cancel_of_det c a (by
    change complexDet c a ≠ 0; rw [hcadet]; exact neg_ne_zero.mpr hd)
  change Complex.arg (b/a) + Complex.arg (c/b) = Complex.arg (c/a)
  linarith

/-- Boundary of the actual two-arc crossing-star rectangle, including all
four actual arc-grid side breakpoints. Radius and speeds are derived from D. -/
theorem actualStar_boundary_breakpoint_balance (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    let ε := crossingStarRadius D c
    let Z := crossingStarPullback D c
    Complex.arg (Z 0 (-ε) / Z (-ε) (-ε)) +
    Complex.arg (Z (2*ε) (-ε) / Z 0 (-ε)) +
    Complex.arg (Z (2*ε) 0 / Z (2*ε) (-ε)) +
    Complex.arg (Z (2*ε) (2*ε) / Z (2*ε) 0) +
    Complex.arg (Z 0 (2*ε) / Z (2*ε) (2*ε)) +
    Complex.arg (Z (-ε) (2*ε) / Z 0 (2*ε)) +
    Complex.arg (Z (-ε) 0 / Z (-ε) (2*ε)) +
    Complex.arg (Z (-ε) (-ε) / Z (-ε) 0) =
      if 0 < complexDet (crossingVector D c 0) (crossingVector D c 1)
      then -(2*Real.pi) else 2*Real.pi := by
  dsimp only
  simp only [crossingStarPullback_eq_linear]
  let ε := crossingStarRadius D c
  let A := starBoxA D c ε
  let B := starBoxB D c ε
  let C := starBoxC D c ε
  let V := starBoxD D c ε
  let E := crossingStarLinear D c 0 (-ε)
  let F := crossingStarLinear D c (2*ε) 0
  let G := crossingStarLinear D c 0 (2*ε)
  let H := crossingStarLinear D c (-ε) 0
  have hε : 0 < ε := crossingStarRadius_pos D c
  have hdet := crossingStar_actual_det_ne_zero D c
  have hkn : 3*ε^2*complexDet (crossingVector D c 0) (crossingVector D c 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt hε))) hdet
  have h6n : 6*ε^2*complexDet (crossingVector D c 0) (crossingVector D c 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt hε))) hdet
  obtain ⟨hAB,_,hVA,hBC,hCV,_⟩ := starBox_determinants D c ε
  have hbot : (((1-(1/3:ℝ)) : ℂ)*A + ((1/3:ℝ) : ℂ)*B) = E := by
    simp [A,B,E,starBoxA,starBoxB,crossingStarLinear]; ring
  have hright : (((1-(1/3:ℝ)) : ℂ)*B + ((1/3:ℝ) : ℂ)*C) = F := by
    simp [B,C,F,starBoxB,starBoxC,crossingStarLinear]; ring
  have htop : (((1-(2/3:ℝ)) : ℂ)*C + ((2/3:ℝ) : ℂ)*V) = G := by
    simp [C,V,G,starBoxC,starBoxD,crossingStarLinear]; ring
  have hleft : (((1-(2/3:ℝ)) : ℂ)*V + ((2/3:ℝ) : ℂ)*A) = H := by
    simp [V,A,H,starBoxD,starBoxA,crossingStarLinear]; ring
  have hb := straight_side_arg_subdivision A B (by rw [hAB]; exact neg_ne_zero.mpr hkn)
    (1/3) (by norm_num) (by norm_num)
  have hr := straight_side_arg_subdivision B C (by rw [hBC]; exact neg_ne_zero.mpr h6n)
    (1/3) (by norm_num) (by norm_num)
  have ht := straight_side_arg_subdivision C V (by rw [hCV]; exact neg_ne_zero.mpr h6n)
    (2/3) (by norm_num) (by norm_num)
  have hl := straight_side_arg_subdivision V A (by rw [hVA]; exact neg_ne_zero.mpr hkn)
    (2/3) (by norm_num) (by norm_num)
  dsimp only at hb hr ht hl
  simp only [Complex.ofReal_sub, Complex.ofReal_one] at hb hr ht hl
  rw [hbot] at hb
  rw [hright] at hr
  rw [htop] at ht
  rw [hleft] at hl
  have hbox := starBox_signed_boundary_balance D c ε hε
  change Complex.arg (B/A) + Complex.arg (C/B) + Complex.arg (V/C) + Complex.arg (A/V) = _ at hbox
  change Complex.arg (E/A) + Complex.arg (B/E) + Complex.arg (F/B) + Complex.arg (C/F) +
    Complex.arg (G/C) + Complex.arg (V/G) + Complex.arg (H/V) + Complex.arg (A/H) = _
  linarith

end DirectGLSSW.HOMFLY.PrincipalTurning


