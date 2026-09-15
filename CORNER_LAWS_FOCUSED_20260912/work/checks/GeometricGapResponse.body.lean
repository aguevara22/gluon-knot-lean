namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Geometric wall signs identify both complete gap sums and their reversed
counterparts with the source U/V values. Agreement is required only away from
the critical triple; the nearby array need not have a zero critical gate. -/
theorem geometric_gap_sums (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (H : TripleArray n R)
    (hH : ∀ u, u ≠ t → H u = geometricBoundaryArray P g u)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    (cutWeightedSum (t.fixedFarGate H) (farOnlyCoordinates H) t.leftInterval =
      wallGapU H t.leftInterval (wallLeftEpsilon x y z)) ∧
    (cutWeightedSum (t.fixedFarGate H) (farOnlyCoordinates H) t.rightInterval =
      wallGapU H t.rightInterval (wallRightEpsilon x y z)) ∧
    (cutWeightedSum (t.fixedFarGate (-H)) (farOnlyCoordinates H) t.leftInterval =
      wallGapV H t.leftInterval (wallLeftEpsilon x y z)) ∧
    (cutWeightedSum (t.fixedFarGate (-H)) (farOnlyCoordinates H) t.rightInterval =
      wallGapV H t.rightInterval (wallRightEpsilon x y z)) := by
  have hε := wall_epsilons_one_or_neg_one x y z hyx hzy hzx
  have hL := boundary_left_gap_gate P g t H hH p ω x y z hx hy hz hyx hzx
  have hR := boundary_right_gap_gate P g t H hH p ω x y z hx hy hz hzy hzx
  have hn : t.fixedFarGate (-H) = -t.fixedFarGate H :=
    funext (t.fixedFarGate_neg H)
  refine ⟨cutWeightedSum_signed_inverse _ H _ _ hε.1 hL,
    cutWeightedSum_signed_inverse _ H _ _ hε.2 hR, ?_, ?_⟩
  · rw [hn]
    exact cutWeightedSum_neg_signed_inverse _ H _ _ hε.1 hL
  · rw [hn]
    exact cutWeightedSum_neg_signed_inverse _ H _ _ hε.2 hR

/-- The derived critical inverse jump now uses the actual geometric U gap
values. This is a critical-span formula, not a propagation assumption. -/
theorem geometric_critical_inverse_response (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (H₁ H₂ : TripleArray n R)
    (h₁ : ∀ u, u ≠ t → H₁ u = geometricBoundaryArray P g u)
    (h₂ : ∀ u, u ≠ t → H₂ u = geometricBoundaryArray P g u)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval =
      ((H₂ t - H₁ t) * ⅟ (2 : R)) *
        (wallGapU H₁ t.leftInterval (wallLeftEpsilon x y z) *
          wallGapU H₁ t.rightInterval (wallRightEpsilon x y z)) := by
  have hs := geometric_gap_sums P g t H₁ h₁ p ω x y z hx hy hz hyx hzy hzx
  rw [critical_inverse_source_jump H₁ H₂ t (fun u hu => (h₁ u hu).trans (h₂ u hu).symm),
    hs.1, hs.2.1]

/-- Both ordinary and reversed geometric gap contributions occur in the
complete critical output response. No contracted output is used or presumed. -/
theorem geometric_critical_output_response (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (H₁ H₂ : TripleArray n R)
    (h₁ : ∀ u, u ≠ t → H₁ u = geometricBoundaryArray P g u)
    (h₂ : ∀ u, u ≠ t → H₂ u = geometricBoundaryArray P g u)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    farOnlyOutput H₂ t.spanInterval - farOnlyOutput H₁ t.spanInterval =
      ((H₂ t - H₁ t) * ⅟ (2 : R)) *
        ((wallGapU H₁ t.leftInterval (wallLeftEpsilon x y z) *
          wallGapU H₁ t.rightInterval (wallRightEpsilon x y z)) +
         (wallGapV H₁ t.leftInterval (wallLeftEpsilon x y z) *
          wallGapV H₁ t.rightInterval (wallRightEpsilon x y z))) := by
  have hs := geometric_gap_sums P g t H₁ h₁ p ω x y z hx hy hz hyx hzy hzx
  rw [critical_output_source_jump H₁ H₂ t (fun u hu => (h₁ u hu).trans (h₂ u hu).symm),
    hs.1, hs.2.1, hs.2.2.1, hs.2.2.2]

end
end SM
