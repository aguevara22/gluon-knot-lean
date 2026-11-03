import RoundingBasepointGerm
import RetainedRoundingIntersections

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Aggregate Gate2: the retained affine identity includes the actual join. -/
theorem normalizedRoundedCell_retained_arc_closed (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (s : ℝ) (hs : δ.val ≤ s) :
    Complex.equivRealProd
      (normalizedRoundedCell D (D.continuation.symm e) δ (s + δ.val)) =
      affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) s := by
  rcases lt_or_eq_of_le hs with h | h
  · exact normalizedRoundedCell_retained_arc D e δ s h
  · rw [← h]
    have hden : 2 * δ.val ≠ 0 := ne_of_gt (by linarith [δ.property.1])
    have hq : (δ.val + δ.val) / (2 * δ.val) = 1 := by field_simp; ring
    simp only [normalizedRoundedCell,roundedStep,hq,le_refl,if_true]
    rw [(roundedCorner_endpoints D (D.continuation.symm e) δ.val).2]
    have hi := congrArg D.vertexPoint (D.continuation_incidence (D.continuation.symm e))
    simp only [Equiv.apply_symm_apply] at hi
    apply Prod.ext <;> simp [Complex.equivRealProd_apply,Complex.real_smul,
      cornerCenter,arcVector,affinePoint,Equiv.apply_symm_apply,hi] <;> ring

/-- The actual closed normalized straight piece equals the literal retainedArcPoint. -/
theorem normalizedRoundedCell_retained_unit (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (s : ℝ) (hs : s ∈ Set.Icc 0 1) :
    Complex.equivRealProd (normalizedRoundedCell D e δ
      (2 * δ.val + (1 - 2 * δ.val) * s)) =
      retainedArcPoint D (D.continuation e) δ s := by
  have hparam : δ.val ≤ δ.val + (1 - 2 * δ.val) * s := by
    have hc : 0 ≤ 1 - 2 * δ.val := by linarith [δ.property.2]
    nlinarith [mul_nonneg hc hs.1]
  have h := normalizedRoundedCell_retained_arc_closed D (D.continuation e) δ
    (δ.val + (1 - 2 * δ.val) * s) hparam
  have htime : δ.val + (1 - 2 * δ.val) * s + δ.val =
      2 * δ.val + (1 - 2 * δ.val) * s := by ring
  simpa only [Equiv.symm_apply_apply,htime,retainedArcPoint] using h

end DirectGLSSW.HOMFLY.PrincipalTurning


