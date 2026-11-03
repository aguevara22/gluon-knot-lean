import CornerConeAngle
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Nonnegative actual chord coefficients normalize into the corner interval. -/
theorem cornerConeParameter_bounds (a b : ℝ) (ha : 0≤a) (hb : 0≤b) (hp : 0<a+b) :
    b/(a+b) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg hb hp.le
  · exact (div_le_one hp).mpr (by linarith)

/-- Exact normalization of a positive actual consecutive-vector combination. -/
theorem cornerCone_normalization (D : PLLinkDiagram) (e : Fin D.nArc)
    (a b : ℝ) (hp : 0<a+b) :
    (a : ℂ)*arcVector D e + (b : ℂ)*arcVector D (D.continuation e) =
      ((a+b : ℝ) : ℂ)*arcVector D e*cornerRelativeTangent D e (b/(a+b)) := by
  have hm : (a : ℂ)+(b : ℂ) ≠ 0 := by
    simpa only [←Complex.ofReal_add] using Complex.ofReal_ne_zero.mpr (ne_of_gt hp)
  simp only [cornerRelativeTangent,Complex.ofReal_div,Complex.ofReal_add,
    Complex.ofReal_sub,Complex.ofReal_one]
  field_simp [hm,arcVector_ne_zero D e]
  ring

/-- Principal increments of actual positive cone vectors are exact lift
differences, including pure first/second-arc endpoint directions. -/
theorem cornerCone_ratio_arg (D : PLLinkDiagram) (e : Fin D.nArc)
    (a b a' b' : ℝ) (ha : 0≤a) (hb : 0≤b) (ha' : 0≤a') (hb' : 0≤b')
    (hp : 0<a+b) (hp' : 0<a'+b') :
    Complex.arg (((a' : ℂ)*arcVector D e + (b' : ℂ)*arcVector D (D.continuation e)) /
      ((a : ℂ)*arcVector D e + (b : ℂ)*arcVector D (D.continuation e))) =
      cornerAngleLift D e (b'/(a'+b'))-cornerAngleLift D e (b/(a+b)) := by
  have ht := cornerConeParameter_bounds a b ha hb hp
  have ht' := cornerConeParameter_bounds a' b' ha' hb' hp'
  have hm : ((a+b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hp)
  have hr : cornerRelativeTangent D e (b/(a+b)) ≠ 0 :=
    Complex.slitPlane_ne_zero (cornerRelativeTangent_slitPlane D e _ ht)
  rw [cornerCone_normalization D e a b hp,cornerCone_normalization D e a' b' hp']
  have heq : (((a'+b' : ℝ) : ℂ)*arcVector D e*cornerRelativeTangent D e (b'/(a'+b'))) /
      (((a+b : ℝ) : ℂ)*arcVector D e*cornerRelativeTangent D e (b/(a+b))) =
      (((a'+b')/(a+b) : ℝ) : ℂ) *
        (cornerRelativeTangent D e (b'/(a'+b'))/cornerRelativeTangent D e (b/(a+b))) := by
    rw [Complex.ofReal_div]
    calc
      _ = ((((a'+b' : ℝ) : ℂ)*cornerRelativeTangent D e (b'/(a'+b')))*arcVector D e) /
          ((((a+b : ℝ) : ℂ)*cornerRelativeTangent D e (b/(a+b)))*arcVector D e) := by
        congr 1 <;> ring
      _ = (((a'+b' : ℝ) : ℂ)*cornerRelativeTangent D e (b'/(a'+b'))) /
          (((a+b : ℝ) : ℂ)*cornerRelativeTangent D e (b/(a+b))) :=
        mul_div_mul_right _ _ (arcVector_ne_zero D e)
      _ = _ := (div_mul_div_comm _ _ _ _).symm
  rw [heq,Complex.arg_real_mul _ (div_pos hp' hp)]
  exact cornerRelativeTangent_ratio_arg D e _ _ ht ht'

end DirectGLSSW.HOMFLY.PrincipalTurning



