import CrossingStarCoordinates

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

theorem zero_not_mem_segment_of_complexDet_ne_zero (a b : ℂ)
    (hd : complexDet a b ≠ 0) : (0 : ℂ) ∉ segment ℝ a b := by
  rintro ⟨α, β, _, _, hs, he⟩
  have hre : α*a.re + β*b.re = 0 := by
    simpa only [Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.zero_re] using congrArg Complex.re he
  have him : α*a.im + β*b.im = 0 := by
    simpa only [Complex.add_im, Complex.smul_im, smul_eq_mul, Complex.zero_im] using congrArg Complex.im he
  have hα : α * complexDet a b = 0 := by
    unfold complexDet
    linear_combination b.im * hre - b.re * him
  have hβ : β * complexDet a b = 0 := by
    unfold complexDet
    linear_combination a.re * him - a.im * hre
  have hα0 := (mul_eq_zero.mp hα).resolve_right hd
  have hβ0 := (mul_eq_zero.mp hβ).resolve_right hd
  subst α; subst β
  norm_num at hs

noncomputable def starBoxA (D : PLLinkDiagram) (c : Fin D.nCrossing) (ε : ℝ) : ℂ :=
  crossingStarLinear D c (-ε) (-ε)
noncomputable def starBoxB (D : PLLinkDiagram) (c : Fin D.nCrossing) (ε : ℝ) : ℂ :=
  crossingStarLinear D c (2*ε) (-ε)
noncomputable def starBoxC (D : PLLinkDiagram) (c : Fin D.nCrossing) (ε : ℝ) : ℂ :=
  crossingStarLinear D c (2*ε) (2*ε)
noncomputable def starBoxD (D : PLLinkDiagram) (c : Fin D.nCrossing) (ε : ℝ) : ℂ :=
  crossingStarLinear D c (-ε) (2*ε)

theorem starBox_determinants (D : PLLinkDiagram) (c : Fin D.nCrossing) (ε : ℝ) :
    let d := complexDet (crossingVector D c 0) (crossingVector D c 1)
    complexDet (starBoxA D c ε) (starBoxB D c ε) = -(3*ε^2*d) ∧
    complexDet (starBoxB D c ε) (starBoxD D c ε) = -(3*ε^2*d) ∧
    complexDet (starBoxD D c ε) (starBoxA D c ε) = -(3*ε^2*d) ∧
    complexDet (starBoxB D c ε) (starBoxC D c ε) = -(6*ε^2*d) ∧
    complexDet (starBoxC D c ε) (starBoxD D c ε) = -(6*ε^2*d) ∧
    complexDet (starBoxD D c ε) (starBoxB D c ε) = 3*ε^2*d := by
  dsimp [starBoxA, starBoxB, starBoxC, starBoxD, crossingStarLinear, complexDet]
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Actual signed-coordinate asymmetric box. All side/diagonal exclusions
and both triangle angle balances are derived from actual D transversality. -/
theorem starBox_signed_boundary_balance (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε : ℝ) (hε : 0 < ε) :
    Complex.arg (starBoxB D c ε / starBoxA D c ε) +
      Complex.arg (starBoxC D c ε / starBoxB D c ε) +
      Complex.arg (starBoxD D c ε / starBoxC D c ε) +
      Complex.arg (starBoxA D c ε / starBoxD D c ε) =
      if 0 < complexDet (crossingVector D c 0) (crossingVector D c 1)
      then -(2*Real.pi) else 2*Real.pi := by
  let A := starBoxA D c ε
  let B := starBoxB D c ε
  let C := starBoxC D c ε
  let V := starBoxD D c ε
  let d := complexDet (crossingVector D c 0) (crossingVector D c 1)
  have hd : d ≠ 0 := crossingStar_actual_det_ne_zero D c
  have hk : 0 < 3*ε^2 := mul_pos (by norm_num) (sq_pos_of_pos hε)
  have h6 : 0 < 6*ε^2 := mul_pos (by norm_num) (sq_pos_of_pos hε)
  obtain ⟨hAB,hBV,hVA,hBC,hCV,hVB⟩ := starBox_determinants D c ε
  change complexDet A B = -(3*ε^2*d) at hAB
  change complexDet B V = -(3*ε^2*d) at hBV
  change complexDet V A = -(3*ε^2*d) at hVA
  change complexDet B C = -(6*ε^2*d) at hBC
  change complexDet C V = -(6*ε^2*d) at hCV
  change complexDet V B = 3*ε^2*d at hVB
  have hkn : 3*ε^2*d ≠ 0 := mul_ne_zero (ne_of_gt hk) hd
  have h6n : 6*ε^2*d ≠ 0 := mul_ne_zero (ne_of_gt h6) hd
  have hab := zero_not_mem_segment_of_complexDet_ne_zero A B (hAB ▸ neg_ne_zero.mpr hkn)
  have hbv := zero_not_mem_segment_of_complexDet_ne_zero B V (hBV ▸ neg_ne_zero.mpr hkn)
  have hva := zero_not_mem_segment_of_complexDet_ne_zero V A (hVA ▸ neg_ne_zero.mpr hkn)
  have hbc := zero_not_mem_segment_of_complexDet_ne_zero B C (hBC ▸ neg_ne_zero.mpr h6n)
  have hcv := zero_not_mem_segment_of_complexDet_ne_zero C V (hCV ▸ neg_ne_zero.mpr h6n)
  have hvb := zero_not_mem_segment_of_complexDet_ne_zero V B (hVB ▸ hkn)
  have hin := triangle_signed_angle_balance A B V hab hbv hva
  have hout := triangle_signed_angle_balance B C V hbc hcv hvb
  have hcancel := reciprocal_turns_cancel_of_det B V (by
    change complexDet B V ≠ 0
    rw [hBV]
    exact neg_ne_zero.mpr hkn)
  rw [hAB,hBV,hVA] at hin
  rw [hBC,hCV,hVB] at hout
  change _ = if 0 < d then -(2*Real.pi) else 2*Real.pi
  by_cases hp : 0 < d
  · have hp3 : 0 < 3*ε^2*d := mul_pos hk hp
    have hp6 : 0 < 6*ε^2*d := mul_pos h6 hp
    have hnot : ¬ (0 < -(3*ε^2*d) ∧ 0 < -(3*ε^2*d) ∧ 0 < -(3*ε^2*d)) := by
      rintro ⟨h,_,_⟩; linarith
    rw [if_neg hnot, if_pos ⟨by linarith,by linarith,by linarith⟩] at hin
    rw [if_neg (by rintro ⟨h,_,_⟩; linarith),
      if_neg (by rintro ⟨_,_,h⟩; linarith)] at hout
    rw [if_pos hp]
    change Complex.arg (B/A) + Complex.arg (C/B) + Complex.arg (V/C) +
      Complex.arg (A/V) = -(2*Real.pi)
    linarith
  · have hn : d < 0 := lt_of_le_of_ne (le_of_not_gt hp) hd
    have hn3 : 3*ε^2*d < 0 := mul_neg_of_pos_of_neg hk hn
    have hn6 : 6*ε^2*d < 0 := mul_neg_of_pos_of_neg h6 hn
    rw [if_pos ⟨by linarith,by linarith,by linarith⟩] at hin
    rw [if_neg (by rintro ⟨_,_,h⟩; linarith),
      if_neg (by rintro ⟨h,_,_⟩; linarith)] at hout
    rw [if_neg hp]
    change Complex.arg (B/A) + Complex.arg (C/B) + Complex.arg (V/C) +
      Complex.arg (A/V) = 2*Real.pi
    linarith

end DirectGLSSW.HOMFLY.PrincipalTurning



