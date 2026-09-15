namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The empty selection is the unique unary outer composition. Its gap
sum is the whole zero-specialized top transform. -/
theorem topFar_single_summand (H U : TripleArray n R) (X : IntervalArray n R)
    (I : BoundaryInterval n) :
    (∏ x ∈ (IntervalComposition.single I).cutSet.interior.val, intervalFarCutWeight U I x) *
      (∏ k : Fin (IntervalComposition.single I).parts,
        ∑ σ : IntervalComposition ((IntervalComposition.single I).part k),
          IntervalComposition.positionCutSummand (intervalFarCutWeight H I) X σ) =
      farTransform H X I := by
  have hp : (∏ x ∈ (IntervalComposition.single I).cutSet.interior.val,
      intervalFarCutWeight U I x) = 1 := by
    rw [← (IntervalComposition.single I).prod_interior_positions]
    simp [IntervalComposition.single]
  rw [hp, one_mul]
  have hg := IntervalComposition.single_product
    (fun J : BoundaryInterval n => ∑ σ : IntervalComposition J,
      IntervalComposition.positionCutSummand (intervalFarCutWeight H I) X σ) I
  rw [hg]
  exact (farTransform_positionCutSum H X I).symm

/-- A purely algebraic cancellation principle for the exact top expansion.
The explicit hypothesis concerns every nonunary contribution; geometric
consumers must prove it, rather than assume formal constancy. -/
theorem farTransform_add_eq_of_nonunary_zero (H U : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n)
    (hzero : ∀ π : IntervalComposition I, 2 ≤ π.parts →
      (∏ x ∈ π.cutSet.interior.val, intervalFarCutWeight U I x) *
        (∏ k : Fin π.parts, ∑ σ : IntervalComposition (π.part k),
          IntervalComposition.positionCutSummand (intervalFarCutWeight H I) X σ) = 0) :
    farTransform (H + U) X I = farTransform H X I := by
  classical
  rw [farTransform_add_decomposition]
  rw [Finset.sum_eq_single (IntervalComposition.single I)]
  · exact topFar_single_summand H U X I
  · intro π _ hπ
    apply hzero π
    have hp := π.parts_pos
    have hne : π.parts ≠ 1 := fun he => hπ (π.eq_single_of_parts_eq_one he)
    omega
  · simp

end
end SM
