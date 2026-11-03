import RoundedStep

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- The literal retained straight subarc, in its own unit parameter. -/
noncomputable def retainedArcPoint (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (s : ℝ) : PlanarPoint ℝ :=
  affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e))
    (δ.val + (1 - 2 * δ.val) * s)

theorem retainedArc_parameter_interior (δ : RoundingFraction) (s : ℝ)
    (hs : s ∈ Set.Icc 0 1) : δ.val + (1 - 2 * δ.val) * s ∈ Set.Ioo 0 1 := by
  have hc : 0 < 1 - 2 * δ.val := by linarith [δ.property.2]
  have hl := mul_nonneg hc.le hs.1
  have hr := mul_le_mul_of_nonneg_left hs.2 hc.le
  constructor <;> nlinarith [δ.property.1]

/-- Retaining positive endpoint cutoffs cannot create any straight/straight
intersection: even endpoints are in the old open arc interiors. -/
theorem retainedArcPoint_intersection_iff (D : PLLinkDiagram) (e f : Fin D.nArc)
    (δ : RoundingFraction) (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    retainedArcPoint D e δ s = retainedArcPoint D f δ t ↔ e = f ∧ s = t := by
  constructor
  · intro heq
    have hiS := retainedArc_parameter_interior δ s hs
    have hiT := retainedArc_parameter_interior δ t ht
    have hef : e = f := by
      by_contra h
      exact D.arc_interiors_disjoint e f h _ _ hiS.1 hiS.2 hiT.1 hiT.2 heq
    subst f
    have hend : D.vertexPoint (D.arcSource e) ≠ D.vertexPoint (D.arcTarget e) :=
      fun h => D.arc_endpoints_distinct e (D.vertexPoint_injective h)
    have hparam := affinePoint_injective _ _ hend heq
    have hc : 0 < 1 - 2 * δ.val := by linarith [δ.property.2]
    exact ⟨rfl,by nlinarith⟩
  · rintro ⟨rfl,rfl⟩
    rfl

end DirectGLSSW.HOMFLY.PrincipalTurning


