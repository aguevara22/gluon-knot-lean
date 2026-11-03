import RoundingCrossingTrace

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Every actual rounded crossing velocity is a positive multiple of its
original incoming strand vector, including both cut endpoints. -/
theorem roundedCorner_crossing_velocity_positive (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (i : Fin 2) (δ t : ℝ) (hδ : 0 < δ)
    (ht : t ∈ Set.Icc 0 1) :
    ∃ k : ℝ, 0 < k ∧ roundedCornerDerivative D (D.incoming c i) δ t =
      k • arcVector D (D.incoming c i) := by
  obtain ⟨a,ha,hv⟩ := crossing_arcVector_collinear D c i
  have hq : 0 < (1 - t) * a + t := by
    by_cases ht1 : t = 1
    · simp [ht1]
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht.2 ht1)) ha) ht.1
  refine ⟨(2 * δ * ((1 - t) * a + t)) / a,
    div_pos (mul_pos (mul_pos (by norm_num) hδ) hq) ha,?_⟩
  rw [roundedCornerDerivative, cornerTangent, hv]
  simp only [smul_smul, ← add_smul]
  congr 1
  field_simp

/-- The coordinate derivative has the positive orientation of the actual
geometric strandTangent, not merely the same unoriented supporting line. -/
theorem roundedCorner_crossing_planar_velocity_positive (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (i : Fin 2) (δ t : ℝ) (hδ : 0 < δ)
    (ht : t ∈ Set.Icc 0 1) :
    ∃ k : ℝ, 0 < k ∧
      Complex.equivRealProd (roundedCornerDerivative D (D.incoming c i) δ t) =
        k • strandTangent D c i := by
  obtain ⟨k,hk,hv⟩ := roundedCorner_crossing_velocity_positive D c i δ t hδ ht
  refine ⟨k,hk,?_⟩
  rw [hv]
  apply Prod.ext <;> simp [Complex.equivRealProd_apply, Complex.real_smul,
    arcVector, strandTangent, D.incoming_target]

/-- Determinant of the literal rounded derivatives with the original actual
selected over/under strand ordering. -/
noncomputable def roundedCrossingDet (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (δ s t : ℝ) : ℝ :=
  planarDet
    (Complex.equivRealProd (roundedCornerDerivative D (D.incoming c (D.overBranch c)) δ s))
    (Complex.equivRealProd (roundedCornerDerivative D
      (D.incoming c (otherBranch (D.overBranch c))) δ t))

theorem roundedCrossingDet_positive_multiple (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (δ s t : ℝ) (hδ : 0 < δ)
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    ∃ k : ℝ, 0 < k ∧ roundedCrossingDet D c δ s t = k * crossingDet D c := by
  obtain ⟨a,ha,hva⟩ := roundedCorner_crossing_planar_velocity_positive
    D c (D.overBranch c) δ s hδ hs
  obtain ⟨b,hb,hvb⟩ := roundedCorner_crossing_planar_velocity_positive
    D c (otherBranch (D.overBranch c)) δ t hδ ht
  refine ⟨a * b,mul_pos ha hb,?_⟩
  simp only [roundedCrossingDet, hva, hvb, crossingDet, planarDet, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring

theorem roundedCrossingDet_ne_zero (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (δ s t : ℝ) (hδ : 0 < δ)
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    roundedCrossingDet D c δ s t ≠ 0 := by
  obtain ⟨k,hk,heq⟩ := roundedCrossingDet_positive_multiple D c δ s t hδ hs ht
  rw [heq]
  exact mul_ne_zero (ne_of_gt hk) (selectedDet_ne_zero D c)

theorem roundedCrossingDet_sign (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (δ s t : ℝ) (hδ : 0 < δ)
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    nonzeroScalarSign (roundedCrossingDet D c δ s t)
      (roundedCrossingDet_ne_zero D c δ s t hδ hs ht) = crossingSign D c := by
  obtain ⟨k,hk,heq⟩ := roundedCrossingDet_positive_multiple D c δ s t hδ hs ht
  have hneg : k * crossingDet D c < 0 ↔ crossingDet D c < 0 :=
    by
      constructor
      · intro h
        by_contra hn
        have hd : 0 ≤ crossingDet D c := le_of_not_gt hn
        have hp := mul_nonneg hk.le hd
        linarith
      · exact fun h => mul_neg_of_pos_of_neg hk h
  simp only [crossingSign, nonzeroScalarSign, heq, hneg]

end DirectGLSSW.HOMFLY.PrincipalTurning





