import RoundingCrossingOrientation

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Literal normalized corner position under its positive time change. -/
theorem normalizedRoundedCell_corner_time (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (s : ℝ) (hs : s ∈ Set.Icc 0 1) :
    normalizedRoundedCell D e δ (2 * δ.val * s) = roundedCorner D e δ.val s := by
  have hden : 2 * δ.val ≠ 0 := ne_of_gt (by linarith [δ.property.1])
  have hq : (2 * δ.val * s) / (2 * δ.val) = s := by field_simp
  simp only [normalizedRoundedCell,roundedStep,hq,hs.2,if_true]

/-- The normalized actual cell derivative is a positive scalar times the
literal quadratic derivative, including its join endpoint. -/
theorem normalizedRoundedVelocity_corner_time (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (s : ℝ) (hs : s ∈ Set.Icc 0 1) :
    normalizedRoundedVelocity D e δ (2 * δ.val * s) =
      (1 / (2 * δ.val)) • roundedCornerDerivative D e δ.val s := by
  have hden : 2 * δ.val ≠ 0 := ne_of_gt (by linarith [δ.property.1])
  have hq : (2 * δ.val * s) / (2 * δ.val) = s := by field_simp
  simp only [normalizedRoundedVelocity,roundedStepVelocity,hq,hs.2,if_true]

noncomputable def normalizedCrossingDet (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (δ : RoundingFraction) (s t : ℝ) : ℝ :=
  planarDet
    (Complex.equivRealProd (normalizedRoundedVelocity D (D.incoming c (D.overBranch c))
      δ (2 * δ.val * s)))
    (Complex.equivRealProd (normalizedRoundedVelocity D
      (D.incoming c (otherBranch (D.overBranch c))) δ (2 * δ.val * t)))

/-- Determinants acquire the square of the positive time-change factor. -/
theorem normalizedCrossingDet_eq_rescale (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (δ : RoundingFraction) (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    normalizedCrossingDet D c δ s t = (1 / (2 * δ.val)) ^ 2 *
      roundedCrossingDet D c δ.val s t := by
  simp only [normalizedCrossingDet,normalizedRoundedVelocity_corner_time D _ δ s hs,
    normalizedRoundedVelocity_corner_time D _ δ t ht]
  simp [roundedCrossingDet,Complex.equivRealProd_apply,Complex.real_smul,planarDet]
  ring

theorem normalizedCrossingDet_positive_multiple (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (δ : RoundingFraction) (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    ∃ k : ℝ, 0 < k ∧ normalizedCrossingDet D c δ s t = k * crossingDet D c := by
  obtain ⟨k,hk,heq⟩ := roundedCrossingDet_positive_multiple D c δ.val s t δ.property.1 hs ht
  have hp : 0 < 1 / (2 * δ.val) := one_div_pos.mpr (by linarith [δ.property.1])
  refine ⟨(1 / (2 * δ.val)) ^ 2 * k,mul_pos (pow_pos hp _) hk,?_⟩
  rw [normalizedCrossingDet_eq_rescale D c δ s t hs ht,heq,mul_assoc]

theorem normalizedCrossingDet_ne_zero (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (δ : RoundingFraction) (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    normalizedCrossingDet D c δ s t ≠ 0 := by
  obtain ⟨k,hk,heq⟩ := normalizedCrossingDet_positive_multiple D c δ s t hs ht
  rw [heq]
  exact mul_ne_zero (ne_of_gt hk) (selectedDet_ne_zero D c)

theorem normalizedCrossingDet_sign (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (δ : RoundingFraction) (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    nonzeroScalarSign (normalizedCrossingDet D c δ s t)
      (normalizedCrossingDet_ne_zero D c δ s t hs ht) = crossingSign D c := by
  obtain ⟨k,hk,heq⟩ := normalizedCrossingDet_positive_multiple D c δ s t hs ht
  have hneg : k * crossingDet D c < 0 ↔ crossingDet D c < 0 := by
    constructor
    · intro h
      by_contra hn
      have hd : 0 ≤ crossingDet D c := le_of_not_gt hn
      have hp := mul_nonneg hk.le hd
      linarith
    · exact fun h => mul_neg_of_pos_of_neg hk h
  simp only [crossingSign,nonzeroScalarSign,heq,hneg]

end DirectGLSSW.HOMFLY.PrincipalTurning






