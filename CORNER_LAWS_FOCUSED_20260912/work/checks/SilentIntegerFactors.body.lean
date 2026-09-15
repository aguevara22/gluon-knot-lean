namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem integer_U_product_zero_of_left_nonleaf_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (εR : SignType) :
    criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span εR = 0 := by
  have hE := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  simp only [criticalGapUInteger, ite_true, hE, zero_mul]

theorem integer_U_product_zero_of_right_nonleaf_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hR : 2 ≤ t.rightInterval.leaves) (εL : SignType) :
    criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span εL *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0 := by
  have hE := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  simp only [criticalGapUInteger, ite_true, hE, mul_zero]

/-- With two nonleaf gaps, one positive epsilon suffices to annihilate the
proper-span source product, whatever the other allowed sign is. -/
theorem integer_U_product_zero_of_nonleaves_one_positive (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : 2 ≤ t.rightInterval.leaves)
    (εL εR : SignType) (hε : εL = 1 ∨ εR = 1) :
    criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span εL *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span εR = 0 := by
  rcases hε with rfl | rfl
  · exact integer_U_product_zero_of_left_nonleaf_pos P g t hZ hL εR
  · exact integer_U_product_zero_of_right_nonleaf_pos P g t hZ hR εL

/-- Opposite epsilons on two nonleaf gaps annihilate both products required
by the FULL-span response. No amplitude is canceled or assumed nonzero. -/
theorem integer_UV_products_zero_of_nonleaves_opposite (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : 2 ≤ t.rightInterval.leaves)
    (εL εR : SignType) (hε : (εL = 1 ∧ εR = -1) ∨ (εL = -1 ∧ εR = 1)) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span εL *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span εR = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span εL *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span εR = 0) := by
  have hEL := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  have hER := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  rcases hε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp [criticalGapUInteger, criticalGapVInteger, hEL, hER,
    show (-1 : SignType) ≠ 1 by decide]

end
end SM
