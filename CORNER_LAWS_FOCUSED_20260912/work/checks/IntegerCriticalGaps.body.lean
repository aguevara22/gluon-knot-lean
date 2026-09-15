namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem IncreasingBoundaryTriple.leftInterval_excludes_span (t : IncreasingBoundaryTriple n) :
    ¬ (t.leftInterval.left ≤ t.lower ∧ t.upper ≤ t.leftInterval.right) := by
  rintro ⟨_, hr⟩
  exact (not_le_of_gt t.middle_upper) hr

theorem IncreasingBoundaryTriple.rightInterval_excludes_span (t : IncreasingBoundaryTriple n) :
    ¬ (t.rightInterval.left ≤ t.lower ∧ t.upper ≤ t.rightInterval.right) := by
  rintro ⟨hl, _⟩
  exact (not_le_of_gt t.lower_middle) hl

/-- The integer B value on a noncritical interval is one on a formal leaf and
otherwise the actual closed endpoint polygon's tree coefficient. The latter
has proved G1 and at least three vertices. No inverse over the integers is used. -/
def criticalIntervalIntegerOutput (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) : ℤ :=
  if hl : J.leaves = 1 then 1 else
    treeCoefficient (restrictedWordTuple P g J) (restrictedWord_G1_off_critical P g t hZ J hJ) 0
      (by have := J.leaves_pos; omega)

/-- Source U as an integer: the exact unit array or the proved integral B value. -/
def criticalGapUInteger (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) (ε : SignType) : ℤ :=
  if ε = 1 then boundaryUnitArray (R := ℤ) J else criticalIntervalIntegerOutput P g t hZ J hJ

/-- Source V interchanges the same two integer values. -/
def criticalGapVInteger (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) (ε : SignType) : ℤ :=
  if ε = 1 then criticalIntervalIntegerOutput P g t hZ J hJ else boundaryUnitArray (R := ℤ) J

theorem critical_integer_leaf_values (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right))
    (hl : J.leaves = 1) (ε : SignType) :
    criticalIntervalIntegerOutput P g t hZ J hJ = 1 ∧
      criticalGapUInteger P g t hZ J hJ ε = 1 ∧ criticalGapVInteger P g t hZ J hJ ε = 1 := by
  have hb : criticalIntervalIntegerOutput P g t hZ J hJ = 1 := by
    simp only [criticalIntervalIntegerOutput, dif_pos hl]
  have hr : J.right.val = J.left.val + 1 := by
    have hpos := J.increasing
    change J.left.val < J.right.val at hpos
    change J.right.val - J.left.val = 1 at hl
    omega
  have he : boundaryUnitArray (R := ℤ) J = 1 := by simp [boundaryUnitArray, hr]
  simp only [criticalGapUInteger, criticalGapVInteger, hb, he, ite_self, and_self]

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

theorem boundaryUnitArray_intCast (J : BoundaryInterval n) :
    ((boundaryUnitArray (R := ℤ) J : ℤ) : R) = boundaryUnitArray (R := R) J := by
  by_cases h : J.right.val = J.left.val + 1 <;> simp [boundaryUnitArray, h]

/-- Only the complete B output is identified with an integer cast. The
constructed inverse coordinates themselves may have denominators. -/
theorem criticalIntervalIntegerOutput_cast (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) :
    (criticalIntervalIntegerOutput P g t hZ J hJ : R) =
      farOnlyOutput (geometricBoundaryArray P g) J := by
  by_cases hl : J.leaves = 1
  · rw [criticalIntervalIntegerOutput, dif_pos hl, Int.cast_one]
    exact (farOnly_leaf_values (geometricBoundaryArray P g) J hl).2.symm
  · rw [criticalIntervalIntegerOutput, dif_neg hl]
    have htwo : 2 ≤ J.leaves := by have := J.leaves_pos; omega
    exact (farOnlyOutput_restricted_tree P g J htwo
      (restrictedWord_G1_off_critical P g t hZ J hJ)).symm

theorem criticalGapUInteger_cast (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) (ε : SignType) :
    (criticalGapUInteger P g t hZ J hJ ε : R) = wallGapU (geometricBoundaryArray P g) J ε := by
  by_cases hε : ε = 1
  · simp only [criticalGapUInteger, wallGapU, if_pos hε]
    exact boundaryUnitArray_intCast J
  · simp only [criticalGapUInteger, wallGapU, if_neg hε]
    exact criticalIntervalIntegerOutput_cast P g t hZ J hJ

theorem criticalGapVInteger_cast (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) (ε : SignType) :
    (criticalGapVInteger P g t hZ J hJ ε : R) = wallGapV (geometricBoundaryArray P g) J ε := by
  by_cases hε : ε = 1
  · simp only [criticalGapVInteger, wallGapV, if_pos hε]
    exact criticalIntervalIntegerOutput_cast P g t hZ J hJ
  · simp only [criticalGapVInteger, wallGapV, if_neg hε]
    exact boundaryUnitArray_intCast J

end
end SM
