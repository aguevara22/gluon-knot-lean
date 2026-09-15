namespace SM

noncomputable section

universe u
variable {n : ℕ} [NeZero n] {R : Type u} [CommRing R]

/-- A triangular composition transform: the unary coordinate has coefficient
one; every nonunary term reads only strictly shorter child intervals. -/
def triangularTransform
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (X : BoundaryInterval n → R) : BoundaryInterval n → R :=
  fun I => X I + ∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
    weight I π.val * ∏ k : Fin π.val.parts, X (π.val.part k)

/-- Construct the inverse in increasing interval length using only subtraction,
finite sums and finite products. No coefficient is divided by. -/
def triangularInverse
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (Y : BoundaryInterval n → R) (I : BoundaryInterval n) : R :=
  Y I - ∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
    weight I π.val * ∏ k : Fin π.val.parts, triangularInverse weight Y (π.val.part k)
termination_by I.leaves
decreasing_by exact π.val.part_leaves_lt π.property k

theorem triangularTransform_inverse
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (Y : BoundaryInterval n → R) :
    triangularTransform weight (triangularInverse weight Y) = Y := by
  funext I
  unfold triangularTransform
  rw [triangularInverse]
  ring

theorem triangularInverse_transform_apply
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (X : BoundaryInterval n → R) (I : BoundaryInterval n) :
    triangularInverse weight (triangularTransform weight X) I = X I := by
  rw [triangularInverse]
  change (X I + ∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
      weight I π.val * ∏ k : Fin π.val.parts, X (π.val.part k)) -
    (∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
      weight I π.val * ∏ k : Fin π.val.parts,
        triangularInverse weight (triangularTransform weight X) (π.val.part k)) = X I
  have hs : (∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
      weight I π.val * ∏ k : Fin π.val.parts,
        triangularInverse weight (triangularTransform weight X) (π.val.part k)) =
      ∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        weight I π.val * ∏ k : Fin π.val.parts, X (π.val.part k) := by
    apply Finset.sum_congr rfl
    intro π _
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    exact triangularInverse_transform_apply weight X (π.val.part k)
  rw [hs]
  ring
termination_by I.leaves
decreasing_by exact π.val.part_leaves_lt π.property k

theorem triangularInverse_transform
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (X : BoundaryInterval n → R) :
    triangularInverse weight (triangularTransform weight X) = X :=
  funext (triangularInverse_transform_apply weight X)

theorem triangular_solution_unique
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (X Y : BoundaryInterval n → R) (hX : triangularTransform weight X = Y) :
    X = triangularInverse weight Y := by
  rw [← hX]
  exact (triangularInverse_transform weight X).symm

def triangularEquiv
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R) :
    (BoundaryInterval n → R) ≃ (BoundaryInterval n → R) where
  toFun := triangularTransform weight
  invFun := triangularInverse weight
  left_inv := triangularInverse_transform weight
  right_inv := triangularTransform_inverse weight

end

end SM
