namespace CriticalSourceIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]
local instance : DecidableEq (IncreasingBoundaryTriple n) := Classical.decEq _

theorem fixed_coefficients_retain_unary_change (H : TripleArray n R) (X₁ X₂ : IntervalArray n R)
    (I : BoundaryInterval n)
    (hX : ∀ π : IntervalComposition I, 2 ≤ π.parts → ∀ k : Fin π.parts, X₁ (π.part k) = X₂ (π.part k)) :
    farTransform H X₂ I - farTransform H X₁ I = X₂ I - X₁ I := by
  rw [farTransform_difference_of_proper_children H H X₁ X₂ I hX]
  simp

theorem coefficient_sum_is_actual_fixed_input_difference (H₁ H₂ : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    coefficientDifferenceSum H₁ H₂ X I = farTransform H₂ X I - farTransform H₁ X I := by
  simp only [coefficientDifferenceSum, farTransform, nearFarTransform, sub_mul, Finset.sum_sub_distrib]

theorem actual_critical_middle_gate (t : IncreasingBoundaryTriple n) (H : TripleArray n R) :
    t.fixedFarGate H t.middle = -H t * ⅟ (2 : R) := by
  rw [IncreasingBoundaryTriple.fixedFarGate, dif_pos ⟨t.lower_middle,t.middle_upper⟩]

theorem unused_fixed_gate_positions_are_zero (t : IncreasingBoundaryTriple n) (H : TripleArray n R)
    (x : Fin n) (h : ¬ (t.lower < x ∧ x < t.upper)) : t.fixedFarGate H x = 0 := by
  rw [IncreasingBoundaryTriple.fixedFarGate, dif_neg h]

theorem actual_full_span_gate_sum (t : IncreasingBoundaryTriple n) (H : TripleArray n R)
    (X : IntervalArray n R) : cutWeightedSum (t.fixedFarGate H) X t.spanInterval = farTransform H X t.spanInterval :=
  cutWeightedSum_eq_farTransform _ _ _ _ (t.fixedFarGate_at_interior H)

theorem both_responses_vanish_when_critical_value_unchanged (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u) (ht : H₂ t = H₁ t) :
    farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval = 0 ∧
    farOnlyOutput H₂ t.spanInterval - farOnlyOutput H₁ t.spanInterval = 0 := by
  constructor
  · rw [critical_inverse_source_jump H₁ H₂ t h, ht]
    simp
  · rw [critical_output_source_jump H₁ H₂ t h, ht]
    simp

theorem reversed_orientation_uses_new_baseline (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    farOnlyCoordinates H₁ t.spanInterval - farOnlyCoordinates H₂ t.spanInterval =
      -((H₂ t - H₁ t) * ⅟ (2 : R)) *
        (cutWeightedSum (t.fixedFarGate H₂) (farOnlyCoordinates H₂) t.leftInterval *
         cutWeightedSum (t.fixedFarGate H₂) (farOnlyCoordinates H₂) t.rightInterval) := by
  rw [critical_inverse_source_jump H₂ H₁ t (fun u hu => (h u hu).symm)]
  ring

theorem arbitrary_single_entry_update_has_actual_inverse_response (H : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (v : R) :
    farOnlyCoordinates (Function.update H t v) t.spanInterval - farOnlyCoordinates H t.spanInterval =
      ((v - H t) * ⅟ (2 : R)) *
        (cutWeightedSum (t.fixedFarGate H) (farOnlyCoordinates H) t.leftInterval *
         cutWeightedSum (t.fixedFarGate H) (farOnlyCoordinates H) t.rightInterval) := by
  have h : ∀ u, u ≠ t → H u = Function.update H t v u := by
    intro u hu
    simp [Function.update_of_ne hu]
  simpa only [Function.update_self] using critical_inverse_source_jump H (Function.update H t v) t h

theorem output_is_reversed_minus_ordinary_coefficient_response (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    farOnlyOutput H₂ t.spanInterval - farOnlyOutput H₁ t.spanInterval =
      coefficientDifferenceSum (-H₁) (-H₂) (farOnlyCoordinates H₁) t.spanInterval -
        coefficientDifferenceSum H₁ H₂ (farOnlyCoordinates H₁) t.spanInterval := by
  rw [critical_output_difference H₁ H₂ t h, critical_inverse_difference H₁ H₂ t h,
    ← coefficientDifferenceSum_eq_nonunary H₁ H₂ (farOnlyCoordinates H₁) t.spanInterval,
    ← coefficientDifferenceSum_eq_nonunary (-H₁) (-H₂) (farOnlyCoordinates H₁) t.spanInterval]
  ring

theorem arbitrary_delta_has_positive_inverse_and_both_output_terms (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u)
    (δ : R) (hd : δ = (H₂ t - H₁ t) * ⅟ (2 : R)) :
    farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval =
      δ * (cutWeightedSum (t.fixedFarGate H₁) (farOnlyCoordinates H₁) t.leftInterval *
        cutWeightedSum (t.fixedFarGate H₁) (farOnlyCoordinates H₁) t.rightInterval) ∧
    farOnlyOutput H₂ t.spanInterval - farOnlyOutput H₁ t.spanInterval =
      δ * ((cutWeightedSum (t.fixedFarGate H₁) (farOnlyCoordinates H₁) t.leftInterval *
          cutWeightedSum (t.fixedFarGate H₁) (farOnlyCoordinates H₁) t.rightInterval) +
        (cutWeightedSum (t.fixedFarGate (-H₁)) (farOnlyCoordinates H₁) t.leftInterval *
          cutWeightedSum (t.fixedFarGate (-H₁)) (farOnlyCoordinates H₁) t.rightInterval)) := by
  subst δ
  exact ⟨critical_inverse_source_jump H₁ H₂ t h, critical_output_source_jump H₁ H₂ t h⟩

end
end CriticalSourceIndependentReview
