import PrincipalTurning
import HalfTurnExclusion
import CornerTangentLift
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- The actual complex point at which consecutive straight arcs meet. -/
def cornerCenter (D : PLLinkDiagram) (e : Fin D.nArc) : ℂ :=
  ⟨(D.vertexPoint (D.arcTarget e)).1, (D.vertexPoint (D.arcTarget e)).2⟩

/-- Explicit quadratic Bezier rounding: control points are center-delta*u,
center, center+delta*v, for the actual consecutive arc vectors u,v. -/
noncomputable def roundedCorner (D : PLLinkDiagram) (e : Fin D.nArc) (δ t : ℝ) : ℂ :=
  cornerCenter D e + δ •
    ((-((1 - t) ^ 2)) • arcVector D e + t ^ 2 • arcVector D (D.continuation e))

noncomputable def cornerTangent (D : PLLinkDiagram) (e : Fin D.nArc) (t : ℝ) : ℂ :=
  (1 - t) • arcVector D e + t • arcVector D (D.continuation e)

noncomputable def roundedCornerDerivative (D : PLLinkDiagram) (e : Fin D.nArc) (δ t : ℝ) : ℂ :=
  (2 * δ) • cornerTangent D e t

theorem cornerTangent_eq_relative (D : PLLinkDiagram) (e : Fin D.nArc) (t : ℝ) :
    cornerTangent D e t = arcVector D e * cornerRelativeTangent D e t := by
  unfold cornerTangent cornerRelativeTangent
  rw [Complex.real_smul, Complex.real_smul]
  symm
  calc
    arcVector D e * (((1 - t : ℝ) : ℂ) + (t : ℂ) *
      (arcVector D (D.continuation e) / arcVector D e)) =
        ((1 - t : ℝ) : ℂ) * arcVector D e + (t : ℂ) *
          (arcVector D (D.continuation e) / arcVector D e * arcVector D e) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ (arcVector_ne_zero D e)]

theorem roundedCorner_hasDerivAt (D : PLLinkDiagram) (e : Fin D.nArc) (δ t : ℝ) :
    HasDerivAt (roundedCorner D e δ) (roundedCornerDerivative D e δ t) t := by
  have h1 : HasDerivAt (fun x : ℝ => -((1 - x) ^ 2)) (2 * (1 - t)) t := by
    simpa using (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).pow 2).neg
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_id t).pow 2
  have h := (((h1.smul_const (arcVector D e)).add
    (h2.smul_const (arcVector D (D.continuation e)))).const_smul δ).const_add (cornerCenter D e)
  convert h using 1
  simp only [roundedCornerDerivative, cornerTangent, smul_add, smul_smul]
  congr 1 <;> congr 1 <;> ring

theorem roundedCorner_regular (D : PLLinkDiagram) (e : Fin D.nArc) (δ t : ℝ)
    (hδ : 0 < δ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    roundedCornerDerivative D e δ t ≠ 0 := by
  rw [roundedCornerDerivative, Complex.real_smul, cornerTangent_eq_relative]
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (mul_pos (by norm_num) hδ))
  · exact mul_ne_zero (arcVector_ne_zero D e)
      (Complex.slitPlane_ne_zero (cornerRelativeTangent_slitPlane D e t ht))

theorem roundedCorner_angleLift (D : PLLinkDiagram) (e : Fin D.nArc) (δ t : ℝ)
    (hδ : 0 < δ) :
    Complex.arg (roundedCornerDerivative D e δ t / arcVector D e) = cornerAngleLift D e t := by
  rw [roundedCornerDerivative, Complex.real_smul, cornerTangent_eq_relative]
  have heq : ((2 * δ : ℝ) : ℂ) * (arcVector D e * cornerRelativeTangent D e t) /
      arcVector D e = ((2 * δ : ℝ) : ℂ) * cornerRelativeTangent D e t := by
    field_simp [arcVector_ne_zero D e]; ring
  rw [heq]
  exact Complex.arg_real_mul _ (mul_pos (by norm_num) hδ)

theorem roundedCorner_endpoints (D : PLLinkDiagram) (e : Fin D.nArc) (δ : ℝ) :
    roundedCorner D e δ 0 = cornerCenter D e - δ • arcVector D e ∧
    roundedCorner D e δ 1 = cornerCenter D e + δ • arcVector D (D.continuation e) := by
  simp [roundedCorner, sub_eq_add_neg]

end DirectGLSSW.HOMFLY.PrincipalTurning




