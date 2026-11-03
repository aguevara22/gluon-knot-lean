import RoundedCorner

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- An actual positive common cutoff fraction with a nonempty retained straight piece. -/
abbrev RoundingFraction := {δ : ℝ // 0 < δ ∧ δ < 1 / 2}

noncomputable def roundingStepDuration (δ : RoundingFraction) : ℝ := 1 / (2 * δ.val)

/-- The retained part of the next actual straight arc, parametrized at the
same velocity as the corner's outgoing derivative. -/
noncomputable def roundingStraight (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) : ℂ :=
  cornerCenter D e + δ.val • arcVector D (D.continuation e) +
    (t - 1) • ((2 * δ.val) • arcVector D (D.continuation e))

/-- The literal corner followed by its retained actual straight arc. -/
noncomputable def roundedStep (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) : ℂ :=
  if t ≤ 1 then roundedCorner D e δ.val t else roundingStraight D e δ t

theorem roundingStepDuration_gt_one (δ : RoundingFraction) : 1 < roundingStepDuration δ := by
  rw [roundingStepDuration, one_lt_div (mul_pos (by norm_num) δ.property.1)]
  linarith [δ.property.2]

theorem cornerCenter_continuation (D : PLLinkDiagram) (e : Fin D.nArc) :
    cornerCenter D (D.continuation e) = cornerCenter D e + arcVector D (D.continuation e) := by
  have hi := congrArg D.vertexPoint (D.continuation_incidence e)
  apply Complex.ext <;> simp [cornerCenter, arcVector, ← hi]

theorem roundingStraight_hasDerivAt (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) :
    HasDerivAt (roundingStraight D e δ) ((2 * δ.val) • arcVector D (D.continuation e)) t := by
  unfold roundingStraight
  simpa only [one_smul] using
    (((hasDerivAt_id t).sub_const 1).smul_const
      ((2 * δ.val) • arcVector D (D.continuation e))).const_add
        (cornerCenter D e + δ.val • arcVector D (D.continuation e))

theorem roundedStep_join (D : PLLinkDiagram) (e : Fin D.nArc) (δ : RoundingFraction) :
    roundedCorner D e δ.val 1 = roundingStraight D e δ 1 := by
  rw [(roundedCorner_endpoints D e δ.val).2]
  simp [roundingStraight]

theorem roundedStep_join_derivative (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) :
    roundedCornerDerivative D e δ.val 1 = (2 * δ.val) • arcVector D (D.continuation e) := by
  simp [roundedCornerDerivative, cornerTangent]

theorem roundedStep_next_join (D : PLLinkDiagram) (e : Fin D.nArc) (δ : RoundingFraction) :
    roundingStraight D e δ (roundingStepDuration δ) =
      roundedCorner D (D.continuation e) δ.val 0 := by
  rw [(roundedCorner_endpoints D (D.continuation e) δ.val).1,
    cornerCenter_continuation]
  have hd : δ.val ≠ 0 := ne_of_gt δ.property.1
  apply Complex.ext <;>
    simp [roundingStraight, roundingStepDuration, Complex.real_smul] <;>
    field_simp [hd] <;> ring

/-- The actual piecewise corner/straight path is differentiable at its join;
both one-sided derivatives are the same actual outgoing velocity. -/
theorem roundedStep_hasDerivAt_join (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) :
    HasDerivAt (roundedStep D e δ) ((2 * δ.val) • arcVector D (D.continuation e)) 1 := by
  have hl : HasDerivWithinAt (roundedStep D e δ)
      ((2 * δ.val) • arcVector D (D.continuation e)) (Set.Iic 1) 1 := by
    have h : HasDerivWithinAt (roundedCorner D e δ.val)
        (roundedCornerDerivative D e δ.val 1) (Set.Iic 1) 1 :=
      (roundedCorner_hasDerivAt D e δ.val 1).hasDerivWithinAt
    rw [roundedStep_join_derivative D e δ] at h
    apply h.congr
    · intro t ht
      simp only [Set.mem_Iic] at ht
      simp [roundedStep, ht]
    · simp [roundedStep]
  have hr : HasDerivWithinAt (roundedStep D e δ)
      ((2 * δ.val) • arcVector D (D.continuation e)) (Set.Ici 1) 1 := by
    apply (roundingStraight_hasDerivAt D e δ 1).hasDerivWithinAt.congr
    · intro t ht
      simp only [Set.mem_Ici] at ht
      by_cases h : t ≤ 1
      · have heq : t = 1 := le_antisymm h ht
        subst t
        simp only [roundedStep, le_refl, if_true]
        exact roundedStep_join D e δ
      · simp [roundedStep, h]
    · simp only [roundedStep, le_refl, if_true]
      exact roundedStep_join D e δ
  simpa only [Set.Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr

end DirectGLSSW.HOMFLY.PrincipalTurning





