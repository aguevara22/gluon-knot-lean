namespace NearFarFactorizationIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

-- The inverse order is near-inverse after far-inverse, matching F after G.
theorem inverse_factorization_order (D H : TripleArray n R) (Y : IntervalArray n R) :
    nearFarInverse D H Y = nearFarInverse D 0 (nearFarInverse 0 H Y) := by
  symm
  apply nearFar_solution_unique D H
  rw [nearFar_factorization D H]
  change farTransform H (nearTransform D (nearFarInverse D 0 (nearFarInverse 0 H Y))) = Y
  simp only [nearTransform, farTransform, nearFarTransform_inverse]

-- No assumed solutions are needed: the canonical inverse supplies every target.
theorem output_independent_with_actual_inverse (D₁ D₂ H : TripleArray n R)
    (Y : IntervalArray n R) :
    nearFarTransform D₁ (-H) (nearFarInverse D₁ H Y) =
      nearFarTransform D₂ (-H) (nearFarInverse D₂ H Y) :=
  complete_output_near_independent D₁ D₂ H _ _ Y
    (nearFarTransform_inverse D₁ H Y) (nearFarTransform_inverse D₂ H Y)

theorem inverse_target_E_has_far_only_output (D H : TripleArray n R) :
    nearFarTransform D (-H) (nearFarInverse D H boundaryUnitArray) = farOnlyOutput H :=
  reversedFar_output_of_solution D H _ _ (nearFarTransform_inverse D H boundaryUnitArray)

-- The actual geometric root coefficient remains the same with arbitrary near-array D.
theorem actual_root_all_near_arrays (P : LabelledTuple n) (hP : G1 P)
    (g : ZMod n) (hn : 3 ≤ n) (D : TripleArray n R) :
    (treeCoefficient P hP g hn : R) =
      nearFarTransform D (-geometricBoundaryArray P g)
        (nearFarInverse D (geometricBoundaryArray P g) boundaryUnitArray)
        (fullBoundaryInterval hn) := by
  rw [inverse_target_E_has_far_only_output]
  exact treeCoefficient_farOnly P hP g hn

-- The output is tied to the same physical root when the representative is shifted.
theorem far_only_output_physical_root_shift (P : LabelledTuple n) (g a : ZMod n) :
    farOnlyOutput (geometricBoundaryArray (R := R) (shift a P) (g-a)) =
      farOnlyOutput (geometricBoundaryArray P g) := by
  rw [geometricBoundaryArray_shift]

-- Open-word leaf and nonleaf conventions use every original interval coordinate.
theorem all_interval_E_and_leaf_B_values (H : TripleArray n R) (I : BoundaryInterval n) :
    (I.leaves = 1 → farTransform H (farOnlyCoordinates H) I = 1 ∧ farOnlyOutput H I = 1) ∧
    (2 ≤ I.leaves → farTransform H (farOnlyCoordinates H) I = 0) :=
  ⟨farOnly_leaf_values H I, farOnly_nonleaf_E H I⟩

-- The whole marked sum keeps the source unary composition's exact X_I term.
theorem unary_marked_sum_retains_coordinate (D H : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    (∑ m : MarkedCuts (IntervalComposition.single I).cutSet,
      IntervalComposition.markedSummand D H X (IntervalComposition.single I) m) = X I := by
  rw [IntervalComposition.sum_markedSummand]
  rw [(IntervalComposition.single I).nearFarWeight_one D H rfl,
    one_mul, IntervalComposition.single_product]

end
end NearFarFactorizationIndependentReview
