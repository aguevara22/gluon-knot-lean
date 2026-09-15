namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem contactBaseTriple_support (M a : ZMod n) (hn : 3 ≤ n) (hc : ContactSeparated M a) :
    (contactBaseTriple M a hn hc).vertexSet a = contactSupport M a := by
  have hl := contactBaseTriple_labels M a hn hc
  simp only [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet,
    Finset.image_insert, Finset.image_singleton, hl.1, hl.2.1, hl.2.2, contactSupport]
  ext k
  simp [or_comm, or_left_comm, or_assoc]

theorem contactFirstArcTriple_support (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a) :
    (contactFirstArcTriple g M a hn hc hu).vertexSet g = contactSupport M a := by
  have hl := contactFirstArcTriple_labels g M a hn hc hu
  simp only [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet,
    Finset.image_insert, Finset.image_singleton, hl.1, hl.2.1, hl.2.2, contactSupport]

theorem contactSecondArcTriple_support (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val) :
    (contactSecondArcTriple g M a hn hc hu).vertexSet g = contactSupport M a := by
  have hl := contactSecondArcTriple_labels g M a hn hc hu
  simp only [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet,
    Finset.image_insert, Finset.image_singleton, hl.1, hl.2.1, hl.2.2, contactSupport]
  ext k
  simp [or_comm, or_left_comm, or_assoc]

/-- At epsilon (+,+), both nonleaf E factors vanish and the V product is
the ordered product of the two actual integer B outputs. -/
theorem integer_wall_factor_two_nonleaves_pos_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : 2 ≤ t.rightInterval.leaves) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 =
      criticalIntervalIntegerOutput P g t hZ t.leftInterval t.leftInterval_excludes_span *
        criticalIntervalIntegerOutput P g t hZ t.rightInterval t.rightInterval_excludes_span) := by
  have hEL := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  have hER := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  constructor
  · simp only [criticalGapUInteger, ite_true, hEL, hER, zero_mul]
  · simp only [criticalGapVInteger, ite_true]

/-- The base cut's B-to-X gap is the second half at its opening root zero.
All G1 and arity premises are proved from the stated contact data. -/
theorem contactBaseTriple_left_integer_gap (P : LabelledTuple n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) :
    criticalIntervalIntegerOutput P a (contactBaseTriple M a hn hc)
      (by simpa only [contactBaseTriple_support] using hz)
      (contactBaseTriple M a hn hc).leftInterval
      (contactBaseTriple M a hn hc).leftInterval_excludes_span =
      treeCoefficient (secondHalf P M a) (g1_secondHalf hn hc hz) 0
        (contactHalfSizes_bounds hn hc).2.1 := by
  let t := contactBaseTriple M a hn hc
  have hZt : pointZeroTriples P = {t.vertexSet a} := by
    simpa only [t, contactBaseTriple_support] using hz
  obtain ⟨hsize, hword⟩ := contactBaseTriple_left_word P M a hn hc
  have hhalf := (contactHalfSizes_bounds hn hc).2.1
  have hJ : 2 ≤ t.leftInterval.leaves := by
    dsimp only [t]
    omega
  have hleaf : t.leftInterval.leaves ≠ 1 := by omega
  have hP := restrictedWord_G1_off_critical P a t hZt t.leftInterval t.leftInterval_excludes_span
  change criticalIntervalIntegerOutput P a t hZt t.leftInterval t.leftInterval_excludes_span = _
  rw [criticalIntervalIntegerOutput, dif_neg hleaf]
  exact treeCoefficient_of_reindexed_tuple_eq hsize _ _ hP
    (g1_secondHalf hn hc hz) hword (by omega)

/-- The base cut's X-to-A gap closes along A-to-X. Whole tuple transport
and cyclic covariance identify its root with first-half label -1. -/
theorem contactBaseTriple_right_integer_gap (P : LabelledTuple n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) :
    criticalIntervalIntegerOutput P a (contactBaseTriple M a hn hc)
      (by simpa only [contactBaseTriple_support] using hz)
      (contactBaseTriple M a hn hc).rightInterval
      (contactBaseTriple M a hn hc).rightInterval_excludes_span =
      treeCoefficient (firstHalf P M a) (g1_firstHalf hn hc hz) (-1)
        (contactHalfSizes_bounds hn hc).1.1 := by
  let t := contactBaseTriple M a hn hc
  have hZt : pointZeroTriples P = {t.vertexSet a} := by
    simpa only [t, contactBaseTriple_support] using hz
  obtain ⟨hsize, hword⟩ := contactBaseTriple_right_word P M a hn hc
  have hhalf := (contactHalfSizes_bounds hn hc).1.1
  have hJ : 2 ≤ t.rightInterval.leaves := by
    dsimp only [t]
    omega
  have hleaf : t.rightInterval.leaves ≠ 1 := by omega
  have hP := restrictedWord_G1_off_critical P a t hZt t.rightInterval t.rightInterval_excludes_span
  change criticalIntervalIntegerOutput P a t hZt t.rightInterval t.rightInterval_excludes_span = _
  rw [criticalIntervalIntegerOutput, dif_neg hleaf]
  have he := treeCoefficient_of_reindexed_tuple_eq hsize _ _ hP
    (g1_shift_forward (-1) (g1_firstHalf hn hc hz)) hword (by omega)
  have hs := treeCoefficient_shift (firstHalf P M a) (g1_firstHalf hn hc hz) (-1) (-1) hhalf
  simp only [sub_self] at hs
  exact he.trans hs

/-- Every first-arc root has the same complete B-to-X integer gap output,
at second-half root zero, including the endpoint-adjacent roots. -/
theorem contactFirstArcTriple_right_integer_gap (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a)
    (hu : (g - M).val < contactDistance M a)
    (hz : pointZeroTriples P = {contactSupport M a}) :
    criticalIntervalIntegerOutput P g (contactFirstArcTriple g M a hn hc hu)
      (by simpa only [contactFirstArcTriple_support] using hz)
      (contactFirstArcTriple g M a hn hc hu).rightInterval
      (contactFirstArcTriple g M a hn hc hu).rightInterval_excludes_span =
      treeCoefficient (secondHalf P M a) (g1_secondHalf hn hc hz) 0
        (contactHalfSizes_bounds hn hc).2.1 := by
  let t := contactFirstArcTriple g M a hn hc hu
  have hZt : pointZeroTriples P = {t.vertexSet g} := by
    simpa only [t, contactFirstArcTriple_support] using hz
  obtain ⟨hsize, hword⟩ := contactFirstArcTriple_right_word P g M a hn hc hu
  have hhalf := (contactHalfSizes_bounds hn hc).2.1
  have hJ : 2 ≤ t.rightInterval.leaves := by
    dsimp only [t]
    omega
  have hleaf : t.rightInterval.leaves ≠ 1 := by omega
  have hP := restrictedWord_G1_off_critical P g t hZt t.rightInterval t.rightInterval_excludes_span
  change criticalIntervalIntegerOutput P g t hZt t.rightInterval t.rightInterval_excludes_span = _
  rw [criticalIntervalIntegerOutput, dif_neg hleaf]
  exact treeCoefficient_of_reindexed_tuple_eq hsize _ _ hP
    (g1_secondHalf hn hc hz) hword (by omega)

/-- Every second-arc root has the same X-to-A integer gap output at
first-half closing root -1; no caller G1 or tuple identity is needed. -/
theorem contactSecondArcTriple_left_integer_gap (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a)
    (hu : contactDistance M a < (g - M).val)
    (hz : pointZeroTriples P = {contactSupport M a}) :
    criticalIntervalIntegerOutput P g (contactSecondArcTriple g M a hn hc hu)
      (by simpa only [contactSecondArcTriple_support] using hz)
      (contactSecondArcTriple g M a hn hc hu).leftInterval
      (contactSecondArcTriple g M a hn hc hu).leftInterval_excludes_span =
      treeCoefficient (firstHalf P M a) (g1_firstHalf hn hc hz) (-1)
        (contactHalfSizes_bounds hn hc).1.1 := by
  let t := contactSecondArcTriple g M a hn hc hu
  have hZt : pointZeroTriples P = {t.vertexSet g} := by
    simpa only [t, contactSecondArcTriple_support] using hz
  obtain ⟨hsize, hword⟩ := contactSecondArcTriple_left_word P g M a hn hc hu
  have hhalf := (contactHalfSizes_bounds hn hc).1.1
  have hJ : 2 ≤ t.leftInterval.leaves := by
    dsimp only [t]
    omega
  have hleaf : t.leftInterval.leaves ≠ 1 := by omega
  have hP := restrictedWord_G1_off_critical P g t hZt t.leftInterval t.leftInterval_excludes_span
  change criticalIntervalIntegerOutput P g t hZt t.leftInterval t.leftInterval_excludes_span = _
  rw [criticalIntervalIntegerOutput, dif_neg hleaf]
  have he := treeCoefficient_of_reindexed_tuple_eq hsize _ _ hP
    (g1_shift_forward (-1) (g1_firstHalf hn hc hz)) hword (by omega)
  have hs := treeCoefficient_shift (firstHalf P M a) (g1_firstHalf hn hc hz) (-1) (-1) hhalf
  simp only [sub_self] at hs
  exact he.trans hs

end
end SM
