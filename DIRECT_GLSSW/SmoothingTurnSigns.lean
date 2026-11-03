import SmoothingTurnCount

set_option autoImplicit false
namespace DirectGLSSW.SmoothingTurnCount
open DaughterFirstReturn GeometricSmoothingWeights PermutationOrbits
open scoped BigOperators
noncomputable section

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
variable (S : Finset (PolygonCrossing q))

/-- The actual daughter signs give precisely the parent sign and one minus sign per smoothing. -/
theorem product_daughter_leftTurnSigns :
    (∏ c : Component (smoothingDartPermutation q hq.g2 S),
      (-1 : ℚ) ^ leftTurnCount (componentPolygon q hq S c)) =
      (-1 : ℚ) ^ leftTurnCount q * (-1 : ℚ) ^ S.card := by
  classical
  rw [Finset.prod_pow_eq_pow_sum, sum_daughter_leftTurnCount, pow_add]

/-- The sign extraction used in the final reconstruction, for arbitrary actual component weights. -/
theorem product_daughter_signed_weights
    (w : Component (smoothingDartPermutation q hq.g2 S) → ℚ) :
    (∏ c : Component (smoothingDartPermutation q hq.g2 S),
      ((-1 : ℚ) ^ leftTurnCount (componentPolygon q hq S c) * w c)) =
      (-1 : ℚ) ^ leftTurnCount q * (-1 : ℚ) ^ S.card * ∏ c, w c := by
  classical
  rw [Finset.prod_mul_distrib, product_daughter_leftTurnSigns]

/-- Total daughter vertex parity is the parent's vertex parity. -/
theorem product_daughter_vertexSigns :
    (∏ c : Component (smoothingDartPermutation q hq.g2 S),
      (-1 : ℚ) ^ Fintype.card (CornerCoord q hq.g2 S (componentRoot q hq S c))) =
      (-1 : ℚ) ^ n := by
  classical
  rw [Finset.prod_pow_eq_pow_sum, sum_daughter_vertexCount, pow_add, pow_mul]
  norm_num




end
end DirectGLSSW.SmoothingTurnCount
