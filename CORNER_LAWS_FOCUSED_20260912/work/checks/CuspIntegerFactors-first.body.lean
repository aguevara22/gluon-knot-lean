namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The exact integer gap factors for the source cusp table, with the
left gap singleton and the right gap nonleaf. -/
theorem integer_wall_factor_left_leaf_pos_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : t.leftInterval.leaves = 1) (hR : 2 ≤ t.rightInterval.leaves) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = criticalIntervalIntegerOutput P g t hZ t.rightInterval t.rightInterval_excludes_span) := by
  have hl := critical_integer_leaf_values P g t hZ t.leftInterval t.leftInterval_excludes_span hL 1
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  constructor
  · rw [hl.2.1]
    norm_num only [criticalGapUInteger, he, one_mul, mul_one]
  · rw [hl.2.2]
    norm_num only [criticalGapVInteger, he, one_mul, mul_one]

/-- The exact integer gap factors for the source cusp table, with the
left gap singleton and the right gap nonleaf. -/
theorem integer_wall_factor_left_leaf_pos_neg (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : t.leftInterval.leaves = 1) (hR : 2 ≤ t.rightInterval.leaves) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span (-1) = criticalIntervalIntegerOutput P g t hZ t.rightInterval t.rightInterval_excludes_span) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span (-1) = 0) := by
  have hl := critical_integer_leaf_values P g t hZ t.leftInterval t.leftInterval_excludes_span hL 1
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  constructor
  · rw [hl.2.1]
    norm_num only [criticalGapUInteger, he, one_mul, mul_one]
  · rw [hl.2.2]
    norm_num only [criticalGapVInteger, he, one_mul, mul_one]

/-- The exact integer gap factors for the source cusp table, with the
right gap singleton and the left gap nonleaf. -/
theorem integer_wall_factor_right_leaf_neg_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : t.rightInterval.leaves = 1) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span (-1) *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = criticalIntervalIntegerOutput P g t hZ t.leftInterval t.leftInterval_excludes_span) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span (-1) *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0) := by
  have hl := critical_integer_leaf_values P g t hZ t.rightInterval t.rightInterval_excludes_span hR 1
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  constructor
  · rw [hl.2.1]
    norm_num only [criticalGapUInteger, he, one_mul, mul_one]
  · rw [hl.2.2]
    norm_num only [criticalGapVInteger, he, one_mul, mul_one]

/-- The exact integer gap factors for the source cusp table, with the
right gap singleton and the left gap nonleaf. -/
theorem integer_wall_factor_right_leaf_pos_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : t.rightInterval.leaves = 1) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = criticalIntervalIntegerOutput P g t hZ t.leftInterval t.leftInterval_excludes_span) := by
  have hl := critical_integer_leaf_values P g t hZ t.rightInterval t.rightInterval_excludes_span hR 1
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  constructor
  · rw [hl.2.1]
    norm_num only [criticalGapUInteger, he, one_mul, mul_one]
  · rw [hl.2.2]
    norm_num only [criticalGapVInteger, he, one_mul, mul_one]

end
end SM
