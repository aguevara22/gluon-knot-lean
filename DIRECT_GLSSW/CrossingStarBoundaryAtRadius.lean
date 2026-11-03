import CrossingStarBoundary

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

theorem actualStar_boundary_breakpoint_balance_at_radius (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε : ℝ) (hε : 0 < ε) :
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
  let A := starBoxA D c ε
  let B := starBoxB D c ε
  let C := starBoxC D c ε
  let V := starBoxD D c ε
  let E := crossingStarLinear D c 0 (-ε)
  let F := crossingStarLinear D c (2*ε) 0
  let G := crossingStarLinear D c 0 (2*ε)
  let H := crossingStarLinear D c (-ε) 0
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

