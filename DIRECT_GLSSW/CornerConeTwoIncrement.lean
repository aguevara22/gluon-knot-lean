import CornerConeNormalization

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- The two actual diagonal-collar increments through one mixed secant
sum to the source principal turn. Positive coefficients are the literal
travel lengths to either side of the polygon vertex. -/
theorem cornerCone_two_increment (D : PLLinkDiagram) (e : Fin D.nArc)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    Complex.arg (((a : ℂ)*arcVector D e+(b : ℂ)*arcVector D (D.continuation e)) /
      ((a : ℂ)*arcVector D e)) +
    Complex.arg (((b : ℂ)*arcVector D (D.continuation e)) /
      ((a : ℂ)*arcVector D e+(b : ℂ)*arcVector D (D.continuation e))) = turn D e := by
  have h1 := cornerCone_ratio_arg D e a 0 a b ha.le (le_refl 0) ha.le hb.le
    (by simpa only [add_zero] using ha) (by linarith)
  have h2 := cornerCone_ratio_arg D e a b 0 b ha.le hb.le (le_refl 0) hb.le
    (by linarith) (by simpa only [zero_add] using hb)
  simp only [Complex.ofReal_zero,zero_mul,add_zero,zero_div,
    (cornerAngleLift_endpoints D e).1,sub_zero] at h1
  simp only [Complex.ofReal_zero,zero_mul,zero_add,div_self (ne_of_gt hb),
    (cornerAngleLift_endpoints D e).2] at h2
  linarith only [h1,h2]

end DirectGLSSW.HOMFLY.PrincipalTurning

