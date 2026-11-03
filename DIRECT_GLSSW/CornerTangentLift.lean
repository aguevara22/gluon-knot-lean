import PrincipalTurning
import HalfTurnExclusion

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Relative tangent of the explicit quadratic corner rounding. -/
noncomputable def cornerRelativeTangent (D : PLLinkDiagram) (e : Fin D.nArc) (t : ℝ) : ℂ :=
  ((1 - t : ℝ) : ℂ) + (t : ℂ) * (arcVector D (D.continuation e) / arcVector D e)

noncomputable def cornerAngleLift (D : PLLinkDiagram) (e : Fin D.nArc) (t : ℝ) : ℝ :=
  Complex.arg (cornerRelativeTangent D e t)

theorem cornerRelativeTangent_zero (D : PLLinkDiagram) (e : Fin D.nArc) :
    cornerRelativeTangent D e 0 = 1 := by simp [cornerRelativeTangent]

theorem cornerRelativeTangent_one (D : PLLinkDiagram) (e : Fin D.nArc) :
    cornerRelativeTangent D e 1 = arcVector D (D.continuation e) / arcVector D e := by
  simp [cornerRelativeTangent]

theorem cornerRelativeTangent_slitPlane (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    cornerRelativeTangent D e t ∈ Complex.slitPlane := by
  have hq : arcVector D (D.continuation e) / arcVector D e ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff_arg.mpr
    exact ⟨turn_ne_pi D e, div_ne_zero (arcVector_ne_zero D _) (arcVector_ne_zero D _)⟩
  by_cases ht0 : t = 0
  · subst t
    rw [cornerRelativeTangent_zero, Complex.mem_slitPlane_iff]
    left
    norm_num
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    rw [Complex.mem_slitPlane_iff] at hq ⊢
    rcases hq with hq | hq
    · left
      simp only [cornerRelativeTangent, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      nlinarith [ht.2]
    · right
      simp only [cornerRelativeTangent, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, zero_add]
      exact mul_ne_zero ht0 hq

theorem cornerRelativeTangent_continuous (D : PLLinkDiagram) (e : Fin D.nArc) :
    Continuous (cornerRelativeTangent D e) :=
  (Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).add
    ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)

/-- A genuine continuous relative-angle lift along every rounded corner. -/
theorem cornerAngleLift_continuousOn (D : PLLinkDiagram) (e : Fin D.nArc) :
    ContinuousOn (cornerAngleLift D e) (Set.Icc (0 : ℝ) 1) := by
  intro t ht
  exact ((Complex.continuousAt_arg (cornerRelativeTangent_slitPlane D e t ht)).comp
    (cornerRelativeTangent_continuous D e).continuousAt).continuousWithinAt

theorem cornerAngleLift_endpoints (D : PLLinkDiagram) (e : Fin D.nArc) :
    cornerAngleLift D e 0 = 0 ∧ cornerAngleLift D e 1 = turn D e := by
  simp [cornerAngleLift, cornerRelativeTangent_zero, cornerRelativeTangent_one, turn]

theorem cornerAngleLift_open_semicircle (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    -Real.pi < cornerAngleLift D e t ∧ cornerAngleLift D e t < Real.pi := by
  exact ⟨Complex.neg_pi_lt_arg _, lt_of_le_of_ne (Complex.arg_le_pi _)
    (Complex.slitPlane_arg_ne_pi (cornerRelativeTangent_slitPlane D e t ht))⟩

end DirectGLSSW.HOMFLY.PrincipalTurning




