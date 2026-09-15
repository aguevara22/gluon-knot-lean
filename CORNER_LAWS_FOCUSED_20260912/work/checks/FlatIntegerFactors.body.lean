namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem boundaryUnitArray_nonleaf_zero {R : Type*} [CommRing R]
    (J : BoundaryInterval n) (hJ : 2 ≤ J.leaves) : boundaryUnitArray (R := R) J = 0 := by
  have he : J.right.val ≠ J.left.val + 1 := by
    change 2 ≤ J.right.val - J.left.val at hJ
    omega
  simp only [boundaryUnitArray, if_neg he]

/-- Two singleton gaps give the proper-span unit multiplier for all signs. -/
theorem integer_wall_factor_two_leaves (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : t.leftInterval.leaves = 1) (hR : t.rightInterval.leaves = 1) (εL εR : SignType) :
    criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span εL *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span εR = 1 := by
  have hl := critical_integer_leaf_values P g t hZ t.leftInterval t.leftInterval_excludes_span hL εL
  have hr := critical_integer_leaf_values P g t hZ t.rightInterval t.rightInterval_excludes_span hR εR
  rw [hl.2.1, hr.2.1, one_mul]

/-- At the incoming root, epsilon (-,+) annihilates the unbarred product;
the barred product is precisely the nonleaf right-gap B output. -/
theorem integer_wall_factor_left_leaf (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : t.leftInterval.leaves = 1) (hR : 2 ≤ t.rightInterval.leaves) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span (-1) *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span (-1) *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 =
      criticalIntervalIntegerOutput P g t hZ t.rightInterval t.rightInterval_excludes_span) := by
  have hl := critical_integer_leaf_values P g t hZ t.leftInterval t.leftInterval_excludes_span hL (-1)
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  constructor
  · rw [hl.2.1]
    simp only [criticalGapUInteger, ite_true, he, mul_zero]
  · rw [hl.2.2]
    simp only [criticalGapVInteger, ite_true, one_mul]

/-- At the outgoing root epsilon (+,-) reverses the roles of the two gaps. -/
theorem integer_wall_factor_right_leaf (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : t.rightInterval.leaves = 1) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span (-1) = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span (-1) =
      criticalIntervalIntegerOutput P g t hZ t.leftInterval t.leftInterval_excludes_span) := by
  have hr := critical_integer_leaf_values P g t hZ t.rightInterval t.rightInterval_excludes_span hR (-1)
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  constructor
  · rw [hr.2.1]
    simp only [criticalGapUInteger, ite_true, he, zero_mul]
  · rw [hr.2.2]
    simp only [criticalGapVInteger, ite_true, mul_one]

end
end SM
