import SM.CriticalCutSplit
import SM.FarOnlyLocality

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Separate the unary coordinate change from all coefficient changes when
every proper child coordinate agrees. This is an identity of the actual full
transforms, over all raw nonunary compositions. -/
theorem farTransform_difference_of_proper_children
    (H₁ H₂ : TripleArray n R) (X₁ X₂ : IntervalArray n R) (I : BoundaryInterval n)
    (hX : ∀ π : IntervalComposition I, 2 ≤ π.parts →
      ∀ k : Fin π.parts, X₁ (π.part k) = X₂ (π.part k)) :
    farTransform H₂ X₂ I - farTransform H₁ X₁ I =
      (X₂ I - X₁ I) +
      ∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        (π.val.nearFarWeight 0 H₂ - π.val.nearFarWeight 0 H₁) *
          ∏ k : Fin π.val.parts, X₁ (π.val.part k) := by
  classical
  change nearFarTransform 0 H₂ X₂ I - nearFarTransform 0 H₁ X₁ I = _
  rw [nearFarTransform_eq_triangular, nearFarTransform_eq_triangular]
  unfold triangularTransform
  have hs : (∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
      π.val.nearFarWeight 0 H₂ * ∏ k : Fin π.val.parts, X₂ (π.val.part k)) =
      ∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        π.val.nearFarWeight 0 H₂ * ∏ k : Fin π.val.parts, X₁ (π.val.part k) := by
    apply Finset.sum_congr rfl
    intro π _
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    exact (hX π.val π.property k).symm
  rw [hs]
  have hd : (∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
      (π.val.nearFarWeight 0 H₂ - π.val.nearFarWeight 0 H₁) *
        ∏ k : Fin π.val.parts, X₁ (π.val.part k)) =
      (∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        π.val.nearFarWeight 0 H₂ * ∏ k : Fin π.val.parts, X₁ (π.val.part k)) -
      (∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        π.val.nearFarWeight 0 H₁ * ∏ k : Fin π.val.parts, X₁ (π.val.part k)) := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  rw [hd]
  ring

/-- Every proper child of the critical span has unchanged inverse value.
Containing the span would contradict its strictly smaller leaf count. -/
theorem critical_proper_child_coordinates (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u)
    (π : IntervalComposition t.spanInterval) (hp : 2 ≤ π.parts) (k : Fin π.parts) :
    farOnlyCoordinates H₁ (π.part k) = farOnlyCoordinates H₂ (π.part k) := by
  apply farOnlyCoordinates_unchanged_off_critical H₁ H₂ t h
  rintro ⟨hl, hr⟩
  have hc := π.part_leaves_lt hp k
  change (π.part k).left.val ≤ t.lower.val at hl
  change t.upper.val ≤ (π.part k).right.val at hr
  change (π.part k).right.val - (π.part k).left.val < t.upper.val - t.lower.val at hc
  omega

/-- Subtract the two actual inverse equations. Their identical right-hand
side cancels, and the unary coefficient1 gives the negative coefficient sum.
This derives the source coordinate change without assuming a response formula. -/
theorem critical_inverse_difference (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval =
      -(∑ π : {π : IntervalComposition t.spanInterval // 2 ≤ π.parts},
        (π.val.nearFarWeight 0 H₂ - π.val.nearFarWeight 0 H₁) *
          ∏ k : Fin π.val.parts, farOnlyCoordinates H₁ (π.val.part k)) := by
  have he := farTransform_difference_of_proper_children H₁ H₂
    (farOnlyCoordinates H₁) (farOnlyCoordinates H₂) t.spanInterval
    (critical_proper_child_coordinates H₁ H₂ t h)
  rw [farOnlyCoordinates_equation, farOnlyCoordinates_equation, sub_self] at he
  exact eq_neg_of_add_eq_zero_left he.symm

/-- The complete reversed-far output has the same unary coordinate change
and its own separately computed coefficient response. -/
theorem critical_output_difference (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    farOnlyOutput H₂ t.spanInterval - farOnlyOutput H₁ t.spanInterval =
      (farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval) +
      ∑ π : {π : IntervalComposition t.spanInterval // 2 ≤ π.parts},
        (π.val.nearFarWeight 0 (-H₂) - π.val.nearFarWeight 0 (-H₁)) *
          ∏ k : Fin π.val.parts, farOnlyCoordinates H₁ (π.val.part k) :=
  farTransform_difference_of_proper_children (-H₁) (-H₂)
    (farOnlyCoordinates H₁) (farOnlyCoordinates H₂) t.spanInterval
    (critical_proper_child_coordinates H₁ H₂ t h)

end
end SM
