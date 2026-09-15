namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The actual critical inverse-coordinate jump, expressed as the product
of the two complete fixed-endpoint gap sums. Delta is the actual scalar array
difference divided by2; no sign-valued or geometric assumption is imposed. -/
theorem critical_inverse_source_jump (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval =
      ((H₂ t - H₁ t) * ⅟ (2 : R)) *
        (cutWeightedSum (t.fixedFarGate H₁) (farOnlyCoordinates H₁) t.leftInterval *
         cutWeightedSum (t.fixedFarGate H₁) (farOnlyCoordinates H₁) t.rightInterval) := by
  have he := critical_inverse_difference H₁ H₂ t h
  rw [← coefficientDifferenceSum_eq_nonunary H₁ H₂ (farOnlyCoordinates H₁) t.spanInterval,
    coefficientDifferenceSum_span H₁ H₂ (farOnlyCoordinates H₁) t h] at he
  rw [he]
  ring

/-- The full critical-span output response includes both the derived unary
jump and the independently computed reversed-far coefficient change. These
are algebraic gap sums; their geometric E/B identification is a later step. -/
theorem critical_output_source_jump (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    farOnlyOutput H₂ t.spanInterval - farOnlyOutput H₁ t.spanInterval =
      ((H₂ t - H₁ t) * ⅟ (2 : R)) *
        ((cutWeightedSum (t.fixedFarGate H₁) (farOnlyCoordinates H₁) t.leftInterval *
          cutWeightedSum (t.fixedFarGate H₁) (farOnlyCoordinates H₁) t.rightInterval) +
         (cutWeightedSum (t.fixedFarGate (-H₁)) (farOnlyCoordinates H₁) t.leftInterval *
          cutWeightedSum (t.fixedFarGate (-H₁)) (farOnlyCoordinates H₁) t.rightInterval)) := by
  have he := critical_output_difference H₁ H₂ t h
  rw [← coefficientDifferenceSum_eq_nonunary (-H₁) (-H₂)
      (farOnlyCoordinates H₁) t.spanInterval,
    coefficientDifferenceSum_span_reversed H₁ H₂ (farOnlyCoordinates H₁) t h,
    critical_inverse_source_jump H₁ H₂ t h] at he
  rw [he]
  ring

end
end SM
