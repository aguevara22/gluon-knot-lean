namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The actual complete near/far transform reindexed by the proved physical
composition fibers. All gates and child products remain in each summand. -/
theorem nearFarTransform_eq_cutFiber_sum {R : Type*} [CommRing R] [Invertible (2 : R)]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (D H : TripleArray (n + 1) R) (X : IntervalArray (n + 1) R) :
    nearFarTransform D H X I =
      ∑ C : BoundaryCutSet (collapseInterval s I hI),
        ∑ Q : CutFiber s I hI C, (expandCuts s I hI C Q).nearFarSummand D H X := by
  rw [nearFarTransform_eq_cutSet_sum]
  exact sum_cutFiber s I hI (fun T => T.nearFarSummand D H X)

/-- The proposed source ordinary array satisfies the singleton coordinate
for arbitrary top arrays, including both ordinary and reversed-far tops.
This is an interval identity, not a two-gon polygon amplitude. -/
theorem ordinaryLift_transform_duplicate (s : Fin n) (etaMinus etaPlus : ℚ)
    (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) (D H : TripleArray (n + 1) ℚ) :
    nearFarTransform D H (ordinaryLift s etaMinus etaPlus t b0) (duplicateInterval s) = 1 := by
  rw [nearFarTransform_leaf D H _ _ (duplicateInterval_leaves s), ordinaryLift_duplicate]

/-- At the exceptional singleton interval the full ordinary equation is
already checked, before any use of inverse uniqueness for other coordinates. -/
theorem ordinaryLift_equation_duplicate (s : Fin n) (etaMinus etaPlus : ℚ)
    (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) (D H : TripleArray (n + 1) ℚ) :
    nearFarTransform D H (ordinaryLift s etaMinus etaPlus t b0) (duplicateInterval s) =
      boundaryUnitArray (R := ℚ) (duplicateInterval s) := by
  rw [ordinaryLift_transform_duplicate, boundaryUnitArray_leaf _ (duplicateInterval_leaves s)]

end
end SM.SoftDuplication
