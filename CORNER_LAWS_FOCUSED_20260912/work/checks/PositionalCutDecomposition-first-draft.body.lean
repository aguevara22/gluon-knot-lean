namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The synthetic near and far factors add the two arbitrary positional
weights. Invertibility of two is the only division assumption. -/
theorem positional_cut_half_add (a b : R) :
    ((2 * b) - (-(2 * a))) * ⅟ (2 : R) = a + b := by
  calc
    _ = ((a + b) * 2) * ⅟ (2 : R) := by ring
    _ = a + b := by rw [mul_assoc, mul_invOf_self, mul_one]

namespace IntervalComposition
variable {I : BoundaryInterval n}

/-- Both the near and far triples have the same actual interior position.
The synthetic arrays therefore produce the sum of the positional weights. -/
theorem nearFarWeight_position_add (π : IntervalComposition I) (a b : Fin n → R) :
    π.nearFarWeight (fun t => 2 * b t.middle) (fun t => -(2 * a t.middle)) =
      ∏ j : Fin (π.parts - 1), (a (π.interiorPosition j) + b (π.interiorPosition j)) := by
  unfold nearFarWeight
  apply Finset.prod_congr rfl
  intro j _
  change ((2 * b (π.interiorPosition j)) - (-(2 * a (π.interiorPosition j)))) *
    ⅟ (2 : R) = a (π.interiorPosition j) + b (π.interiorPosition j)
  exact positional_cut_half_add _ _

/-- The near-only synthetic array gives exactly the b product, including
an empty product when the composition is unary. -/
theorem nearFarWeight_position_near (π : IntervalComposition I) (b : Fin n → R) :
    π.nearFarWeight (fun t => 2 * b t.middle) 0 =
      ∏ j : Fin (π.parts - 1), b (π.interiorPosition j) := by
  simpa only [mul_zero, neg_zero, zero_add] using
    π.nearFarWeight_position_add (fun _ => 0) b

/-- The far-only synthetic array gives exactly the a product; its negative
sign cancels the negative far factor in the actual transform definition. -/
theorem nearFarWeight_position_far (π : IntervalComposition I) (a : Fin n → R) :
    π.nearFarWeight 0 (fun t => -(2 * a t.middle)) =
      ∏ j : Fin (π.parts - 1), a (π.interiorPosition j) := by
  simpa only [mul_zero, add_zero] using
    π.nearFarWeight_position_add a (fun _ => 0)

end IntervalComposition
open IntervalComposition

/-- The mixed synthetic transform is exactly the positional sum with
weight a+b at each actual cut and the unchanged actual child coordinates. -/
theorem nearFarTransform_position_add (a b : Fin n → R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    nearFarTransform (fun t => 2 * b t.middle) (fun t => -(2 * a t.middle)) X I =
      ∑ π : IntervalComposition I, positionCutSummand (a + b) X π := by
  unfold nearFarTransform
  apply Finset.sum_congr rfl
  intro π _
  rw [π.nearFarWeight_position_add a b]
  rfl

/-- Exact near-transform identification at every actual interval. -/
theorem nearTransform_position (b : Fin n → R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    nearTransform (fun t => 2 * b t.middle) X I =
      ∑ π : IntervalComposition I, positionCutSummand b X π := by
  unfold nearTransform nearFarTransform
  apply Finset.sum_congr rfl
  intro π _
  rw [π.nearFarWeight_position_near b]
  rfl

/-- Exact far-transform identification at every actual interval. -/
theorem farTransform_position (a : Fin n → R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    farTransform (fun t => -(2 * a t.middle)) X I =
      ∑ π : IntervalComposition I, positionCutSummand a X π := by
  unfold farTransform nearFarTransform
  apply Finset.sum_congr rfl
  intro π _
  rw [π.nearFarWeight_position_far a]
  rfl

/-- The full polynomial decomposition for arbitrary positional weights:
select the a-cuts as the actual outer composition and independently sum
all b-compositions of every actual gap. This is a specialization of the
proved source near/far factorization, with no coefficient identity assumed. -/
theorem positionCutSum_add_decomposition (a b : Fin n → R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    (∑ ρ : IntervalComposition I, positionCutSummand (a + b) X ρ) =
      ∑ π : IntervalComposition I,
        (∏ x ∈ π.cutSet.interior.val, a x) *
          ∏ k : Fin π.parts, ∑ σ : IntervalComposition (π.part k), positionCutSummand b X σ := by
  calc
    _ = nearFarTransform (fun t => 2 * b t.middle) (fun t => -(2 * a t.middle)) X I :=
      (nearFarTransform_position_add a b X I).symm
    _ = farTransform (fun t => -(2 * a t.middle))
        (nearTransform (fun t => 2 * b t.middle) X) I :=
      (nearFar_factorization_coordinate (fun t => 2 * b t.middle)
        (fun t => -(2 * a t.middle)) X I).symm
    _ = ∑ π : IntervalComposition I,
        positionCutSummand a (nearTransform (fun t => 2 * b t.middle) X) π :=
      farTransform_position a _ I
    _ = _ := by
      apply Finset.sum_congr rfl
      intro π _
      unfold positionCutSummand
      rw [π.prod_interior_positions a]
      apply congrArg (fun y : R => (∏ x ∈ π.cutSet.interior.val, a x) * y)
      apply Finset.prod_congr rfl
      intro k _
      exact nearTransform_position b X (π.part k)

end
end SM
