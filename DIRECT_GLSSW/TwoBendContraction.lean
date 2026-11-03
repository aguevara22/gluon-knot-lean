import SmoothingTurning
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PrincipalTurning

private theorem arg_between_zero_pi (z : ℂ) (hz : 0 < z.im) :
    0 < Complex.arg z ∧ Complex.arg z < Real.pi := by
  constructor
  · have hne : Complex.arg z ≠ 0 := fun h => hz.ne' (Complex.arg_eq_zero_iff.mp h).2
    exact lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.le) hne.symm
  · exact lt_of_le_of_ne (Complex.arg_le_pi z)
      (fun h => hz.ne' (Complex.arg_eq_pi_iff.mp h).2)

private theorem two_bends_of_det_pos (u v : ℂ)
    (hdet : 0 < u.re * v.im - u.im * v.re) :
    Complex.arg ((u+v)/u) + Complex.arg (v/(u+v)) = Complex.arg (v/u) := by
  have hu : u ≠ 0 := by intro he; subst u; simp at hdet
  have hv : v ≠ 0 := by intro he; subst v; simp at hdet
  have hdw : u.re * (u+v).im - u.im * (u+v).re = u.re*v.im-u.im*v.re := by
    simp only [Complex.add_re,Complex.add_im]; ring
  have hw : u+v ≠ 0 := by
    intro he
    rw [he] at hdw
    simp only [Complex.zero_re,Complex.zero_im,mul_zero,sub_self] at hdw
    exact hdet.ne' hdw.symm
  have ha : 0 < ((u+v)/u).im := by
    rw [Complex.div_im,←sub_div]
    apply div_pos _ (Complex.normSq_pos.mpr hu)
    simp only [Complex.add_re,Complex.add_im]
    nlinarith [hdet]
  have hb : 0 < (v/(u+v)).im := by
    rw [Complex.div_im,←sub_div]
    apply div_pos _ (Complex.normSq_pos.mpr hw)
    simp only [Complex.add_re,Complex.add_im]
    nlinarith [hdet]
  have hc : 0 < (v/u).im := by
    rw [Complex.div_im,←sub_div]
    apply div_pos _ (Complex.normSq_pos.mpr hu)
    nlinarith [hdet]
  obtain ⟨ha0,hapi⟩ := arg_between_zero_pi _ ha
  obtain ⟨hb0,hbpi⟩ := arg_between_zero_pi _ hb
  obtain ⟨hc0,hcpi⟩ := arg_between_zero_pi _ hc
  have he : ((Complex.arg ((u+v)/u) + Complex.arg (v/(u+v)) : ℝ) : Real.Angle) =
      (Complex.arg (v/u) : Real.Angle) := by
    rw [Real.Angle.coe_add,Complex.arg_div_coe_angle hw hu,
      Complex.arg_div_coe_angle hv hw,Complex.arg_div_coe_angle hv hu]
    abel
  obtain ⟨k,hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp he
  have hperiod : 0 < 2*Real.pi := by positivity
  have hkl : (-1:ℝ) < (k:ℝ) := (mul_lt_mul_left hperiod).mp (by nlinarith)
  have hku : (k:ℝ) < 1 := (mul_lt_mul_left hperiod).mp (by nlinarith)
  have hki : (-1:ℤ) < k ∧ k < 1 := by exact_mod_cast (And.intro hkl hku)
  have hk0 : k=0 := by omega
  rw [hk0,Int.cast_zero,mul_zero] at hk
  linarith

/-- A positive connector between transverse directions replaces their sharp
principal bend by two bends with exactly the same real total, without a 2π wrap. -/
theorem two_bend_contraction (u v : ℂ)
    (hdet : u.re*v.im-u.im*v.re ≠ 0) :
    Complex.arg ((u+v)/u) + Complex.arg (v/(u+v)) = Complex.arg (v/u) := by
  rcases lt_or_gt_of_ne hdet with hn | hp
  · have hswap : 0 < v.re*u.im-v.im*u.re := by nlinarith
    have h := two_bends_of_det_pos v u hswap
    rw [add_comm v u] at h
    have hu : u.re*(u+v).im-u.im*(u+v).re ≠ 0 := by
      have he : u.re*(u+v).im-u.im*(u+v).re = u.re*v.im-u.im*v.re := by
        simp only [Complex.add_re,Complex.add_im];ring
      rw [he];exact hdet
    have hv : v.re*(u+v).im-v.im*(u+v).re ≠ 0 := by
      have he : v.re*(u+v).im-v.im*(u+v).re = -(u.re*v.im-u.im*v.re) := by
        simp only [Complex.add_re,Complex.add_im];ring
      rw [he];exact neg_ne_zero.mpr hdet
    have h1 := reciprocal_turns_cancel_of_det u (u+v) hu
    have h2 := reciprocal_turns_cancel_of_det v (u+v) hv
    have h3 := reciprocal_turns_cancel_of_det u v hdet
    linarith
  · exact two_bends_of_det_pos u v hp

/-- The same identity for any strictly positive linear combination. -/
theorem positive_combination_two_bend_contraction (u v : ℂ) (a b : ℝ)
    (ha : 0<a) (hb : 0<b) (hdet : u.re*v.im-u.im*v.re ≠ 0) :
    Complex.arg (((a:ℂ)*u+(b:ℂ)*v)/u) +
      Complex.arg (v/((a:ℂ)*u+(b:ℂ)*v)) = Complex.arg (v/u) := by
  have hd : ((a:ℂ)*u).re*((b:ℂ)*v).im - ((a:ℂ)*u).im*((b:ℂ)*v).re ≠ 0 := by
    have he : ((a:ℂ)*u).re*((b:ℂ)*v).im - ((a:ℂ)*u).im*((b:ℂ)*v).re =
        (a*b)*(u.re*v.im-u.im*v.re) := by
      simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im];ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero ha.ne' hb.ne') hdet
  have h := two_bend_contraction ((a:ℂ)*u) ((b:ℂ)*v) hd
  have h1 := turn_positive_rescale u ((a:ℂ)*u+(b:ℂ)*v) 1 a (by norm_num) ha
  have h2 := turn_positive_rescale ((a:ℂ)*u+(b:ℂ)*v) v b 1 hb (by norm_num)
  have h3 := turn_positive_rescale u v b a hb ha
  simp only [Complex.ofReal_one,one_mul] at h1 h2
  rw [h1,h2,h3] at h
  exact h

/-- Literal actual smoothing: the incoming bend and following connector bend
sum to the single exchanged-strand principal turn, for either branch. -/
theorem two_smoothing_bends_eq_exchange (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) :
    turn (smoothCrossing D c) (smoothArcEquiv D (Sum.inl (D.incoming c i))) +
      turn (smoothCrossing D c) (smoothArcEquiv D (Sum.inr i)) =
      Complex.arg (crossingVector D c (otherBranch i) / crossingVector D c i) := by
  rw [turn_smooth_incoming D c (smoothCrossing_old_arcVector_positive D c),
    turn_smooth_connector D c (smoothCrossing_old_arcVector_positive D c)]
  fin_cases i
  · exact two_bend_contraction _ _ (D.crossing_transverse c)
  · rw [add_comm (crossingVector D c 0)]
    apply two_bend_contraction
    change (strandTangent D c 1).1*(strandTangent D c 0).2 -
      (strandTangent D c 1).2*(strandTangent D c 0).1 ≠ 0
    have h : (strandTangent D c 0).1*(strandTangent D c 1).2 -
        (strandTangent D c 0).2*(strandTangent D c 1).1 ≠ 0 := D.crossing_transverse c
    intro he
    apply h
    nlinarith
end DirectGLSSW.HOMFLY.PrincipalTurning
