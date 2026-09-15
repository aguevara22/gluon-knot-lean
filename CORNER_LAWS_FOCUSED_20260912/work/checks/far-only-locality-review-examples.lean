namespace FarOnlyLocalityIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]
local instance : DecidableEq (IncreasingBoundaryTriple n) := Classical.decEq _

theorem entire_restricted_c_equal (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ t : IncreasingBoundaryTriple n, J.left ≤ t.lower → t.upper ≤ J.right → H₁ t = H₂ t) :
    restrictIntervalArray J (farOnlyCoordinates H₁) = restrictIntervalArray J (farOnlyCoordinates H₂) := by
  rw [farOnlyCoordinates_restrict, farOnlyCoordinates_restrict, restrictTripleArray_eq_of_local J H₁ H₂ h]

theorem every_actual_local_subinterval (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ t : IncreasingBoundaryTriple n, J.left ≤ t.lower → t.upper ≤ J.right → H₁ t = H₂ t)
    (K : BoundaryInterval (J.leaves + 1)) :
    farOnlyCoordinates H₁ (J.liftInterval K) = farOnlyCoordinates H₂ (J.liftInterval K) :=
  congrFun (entire_restricted_c_equal J H₁ H₂ h) K

theorem left_gap_unchanged (H₁ H₂ : TripleArray n R) (critical : IncreasingBoundaryTriple n)
    (h : ∀ t : IncreasingBoundaryTriple n, t ≠ critical → H₁ t = H₂ t) :
    farOnlyCoordinates H₁ critical.leftInterval = farOnlyCoordinates H₂ critical.leftInterval := by
  apply farOnlyCoordinates_unchanged_off_critical H₁ H₂ critical h
  intro hc
  have hb := hc.2
  change critical.upper ≤ critical.middle at hb
  exact (not_le_of_gt critical.middle_upper) hb

theorem right_gap_unchanged (H₁ H₂ : TripleArray n R) (critical : IncreasingBoundaryTriple n)
    (h : ∀ t : IncreasingBoundaryTriple n, t ≠ critical → H₁ t = H₂ t) :
    farOnlyCoordinates H₁ critical.rightInterval = farOnlyCoordinates H₂ critical.rightInterval := by
  apply farOnlyCoordinates_unchanged_off_critical H₁ H₂ critical h
  intro hc
  have hb := hc.1
  change critical.middle ≤ critical.lower at hb
  exact (not_le_of_gt critical.lower_middle) hb

theorem every_proper_critical_child (H₁ H₂ : TripleArray n R) (critical : IncreasingBoundaryTriple n)
    (h : ∀ t : IncreasingBoundaryTriple n, t ≠ critical → H₁ t = H₂ t)
    (π : IntervalComposition (⟨critical.lower, critical.upper,
      lt_trans critical.lower_middle critical.middle_upper⟩ : BoundaryInterval n))
    (hp : 2 ≤ π.parts) (k : Fin π.parts) :
    farOnlyCoordinates H₁ (π.part k) = farOnlyCoordinates H₂ (π.part k) := by
  apply farOnlyCoordinates_unchanged_off_critical H₁ H₂ critical h
  intro hc
  have hs := π.part_leaves_lt hp k
  have hl := hc.1
  have hr := hc.2
  change (π.part k).left.val ≤ critical.lower.val at hl
  change critical.upper.val ≤ (π.part k).right.val at hr
  change (π.part k).right.val - (π.part k).left.val < critical.upper.val - critical.lower.val at hs
  omega

theorem leaf_needs_no_array_agreement (J : BoundaryInterval n) (hj : J.leaves = 1)
    (H₁ H₂ : TripleArray n R) : farOnlyCoordinates H₁ J = farOnlyCoordinates H₂ J := by
  rw [farOnlyCoordinates_leaf H₁ J hj, farOnlyCoordinates_leaf H₂ J hj]

theorem arbitrary_critical_update_off_span (H : TripleArray n R) (critical : IncreasingBoundaryTriple n)
    (value : R) (J : BoundaryInterval n)
    (hj : ¬ (J.left ≤ critical.lower ∧ critical.upper ≤ J.right)) :
    farOnlyCoordinates H J = farOnlyCoordinates (Function.update H critical value) J := by
  classical
  apply farOnlyCoordinates_unchanged_off_critical H (Function.update H critical value) critical _ J hj
  intro t ht
  simp [Function.update_of_ne ht]

theorem entire_restricted_output_equal (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ t : IncreasingBoundaryTriple n, J.left ≤ t.lower → t.upper ≤ J.right → H₁ t = H₂ t) :
    restrictIntervalArray J (farOnlyOutput H₁) = restrictIntervalArray J (farOnlyOutput H₂) := by
  rw [farOnlyOutput_restrict, farOnlyOutput_restrict, restrictTripleArray_eq_of_local J H₁ H₂ h]

end
end FarOnlyLocalityIndependentReview
