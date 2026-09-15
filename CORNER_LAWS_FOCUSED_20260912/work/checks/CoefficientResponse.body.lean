namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Change of all composition coefficients with the child coordinates held
fixed, summed over the complete raw domain, including the unary composition. -/
def coefficientDifferenceSum (H₁ H₂ : TripleArray n R) (X : IntervalArray n R)
    (I : BoundaryInterval n) : R :=
  ∑ π : IntervalComposition I,
    (π.nearFarWeight 0 H₂ - π.nearFarWeight 0 H₁) *
      ∏ k : Fin π.parts, X (π.part k)

/-- The unary coefficient difference is0, so removing just that composition
gives the exact nonunary coefficient sum in the triangular subtraction. -/
theorem coefficientDifferenceSum_eq_nonunary (H₁ H₂ : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    coefficientDifferenceSum H₁ H₂ X I =
      ∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        (π.val.nearFarWeight 0 H₂ - π.val.nearFarWeight 0 H₁) *
          ∏ k : Fin π.val.parts, X (π.val.part k) := by
  classical
  unfold coefficientDifferenceSum
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (IntervalComposition.single I)]
  rw [(IntervalComposition.single I).nearFarWeight_one 0 H₂ rfl,
    (IntervalComposition.single I).nearFarWeight_one 0 H₁ rfl,
    sub_self, zero_mul, zero_add]
  exact Fintype.sum_equiv (IntervalComposition.nonSingleEquiv I) _ _ (fun _ => rfl)

/-- Only actual middle-cut compositions contribute. Exact erasure and the
full raw splitting bijection factor their entire sum into the two gap sums. -/
theorem coefficientDifferenceSum_span (H₁ H₂ : TripleArray n R) (X : IntervalArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    coefficientDifferenceSum H₁ H₂ X t.spanInterval =
      (-(H₂ t - H₁ t) * ⅟ (2 : R)) *
        (cutWeightedSum (t.fixedFarGate H₁) X t.leftInterval *
         cutWeightedSum (t.fixedFarGate H₁) X t.rightInterval) := by
  classical
  let f : IntervalComposition t.spanInterval → R := fun π =>
    (π.nearFarWeight 0 H₂ - π.nearFarWeight 0 H₁) *
      ∏ k : Fin π.parts, X (π.part k)
  have ha := Fintype.sum_subtype_add_sum_subtype
    (fun π : IntervalComposition t.spanInterval => t.middle ∈ π.cutSet.cuts) f
  have hz : (∑ π : {π : IntervalComposition t.spanInterval // t.middle ∉ π.cutSet.cuts},
      f π.val) = 0 := by
    apply Finset.sum_eq_zero
    intro π _
    change (π.val.nearFarWeight 0 H₂ - π.val.nearFarWeight 0 H₁) *
      (∏ k : Fin π.val.parts, X (π.val.part k)) = 0
    rw [π.val.farWeight_unchanged_without_middle t H₁ H₂ h π.property,
      sub_self, zero_mul]
  rw [hz, add_zero] at ha
  change (∑ π : IntervalComposition t.spanInterval, f π) = _
  rw [← ha]
  change (∑ π : t.MiddleComposition,
    (π.val.nearFarWeight 0 H₂ - π.val.nearFarWeight 0 H₁) *
      ∏ k : Fin π.val.parts, X (π.val.part k)) = _
  simp_rw [t.farWeight_difference_physical H₁ H₂ h]
  calc
    _ = (-(H₂ t - H₁ t) * ⅟ (2 : R)) *
        ∑ π : t.MiddleComposition,
          (∏ x ∈ π.val.cutSet.interior.val.erase t.middle, t.fixedFarGate H₁ x) *
            ∏ k : Fin π.val.parts, X (π.val.part k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro π _
      ring
    _ = _ := by
      rw [t.middle_erased_weighted_composition_sum]
      rfl

/-- Reverse every far sign and compute the response again. The changing
factor has plus delta, and the gap sums use reversed remaining gates. -/
theorem coefficientDifferenceSum_span_reversed (H₁ H₂ : TripleArray n R)
    (X : IntervalArray n R) (t : IncreasingBoundaryTriple n)
    (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    coefficientDifferenceSum (-H₁) (-H₂) X t.spanInterval =
      ((H₂ t - H₁ t) * ⅟ (2 : R)) *
        (cutWeightedSum (t.fixedFarGate (-H₁)) X t.leftInterval *
         cutWeightedSum (t.fixedFarGate (-H₁)) X t.rightInterval) := by
  have he := coefficientDifferenceSum_span (-H₁) (-H₂) X t
    (fun u hu => congrArg Neg.neg (h u hu))
  simpa only [Pi.neg_apply, neg_sub_neg, neg_sub] using he

end
end SM
