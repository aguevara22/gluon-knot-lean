namespace ContractedGeometricWordIndependentReview
open SM

noncomputable section
variable {n : ℕ} [NeZero n]

-- Exact cyclic labels correspond to every surviving linear position.
theorem cyclic_label_on_boundary_position (g : ZMod n) (t : IncreasingBoundaryTriple n)
    (k : Fin t.contractedSize) :
    contractedVertexIndex g t ((k.val : ZMod t.contractedSize) + 1) =
      boundaryIndex g (t.expandPosition k) := by
  letI := t.contractedSize_neZero
  unfold contractedVertexIndex
  have hz : ((k.val : ZMod t.contractedSize) + 1) - 1 = (k.val : ZMod t.contractedSize) := by ring
  simp only [hz, ZMod.val_natCast_of_lt k.isLt]

-- All old survivors, and only those survivors, occur among actual cyclic labels.
theorem cyclic_label_range_iff (g : ZMod n) (t : IncreasingBoundaryTriple n) (x : Fin n) :
    (∃ j : ZMod t.contractedSize, contractedVertexIndex g t j = boundaryIndex g x) ↔
      x ≤ t.lower ∨ t.upper ≤ x := by
  letI := t.contractedSize_neZero
  constructor
  · rintro ⟨j, hj⟩
    have hp : t.expandPosition ⟨(j - 1).val, ZMod.val_lt _⟩ = x := boundaryIndex_injective g hj
    simpa only [hp] using t.expandPosition_survives ⟨(j - 1).val, ZMod.val_lt _⟩
  · intro hx
    let k := t.contractPosition x hx
    refine ⟨(k.val : ZMod t.contractedSize) + 1, ?_⟩
    rw [cyclic_label_on_boundary_position]
    exact congrArg (boundaryIndex g) (t.expand_contractPosition x hx)

-- Uniqueness is label uniqueness; no injectivity assumption is made about geometric P.
theorem survivor_has_unique_cyclic_label (g : ZMod n) (t : IncreasingBoundaryTriple n)
    (x : Fin n) (hx : x ≤ t.lower ∨ t.upper ≤ x) :
    ∃! j : ZMod t.contractedSize, contractedVertexIndex g t j = boundaryIndex g x := by
  obtain ⟨j, hj⟩ := (cyclic_label_range_iff g t x).mpr hx
  refine ⟨j, hj, ?_⟩
  intro k hk
  exact contractedVertexIndex_injective g t (hk.trans hj.symm)

-- The forbidden support loses its critical middle label even for arbitrary nongeneric tuples.
theorem critical_middle_cyclic_label_deleted (g : ZMod n) (t : IncreasingBoundaryTriple n)
    (j : ZMod t.contractedSize) : contractedVertexIndex g t j ≠ boundaryIndex g t.middle := by
  intro hj
  rcases (cyclic_label_range_iff g t t.middle).mp ⟨j, hj⟩ with hl | hr
  · exact (not_le_of_gt t.lower_middle) hl
  · exact (not_le_of_gt t.middle_upper) hr

-- The distinguished one-leaf replacement has the actual old x-to-z directed displacement.
theorem replacement_leaf_edge_vector (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) :
    boundaryWord (contractedWordTuple P g t) 0
        ⟨t.lower.val + 1, by have := t.contractedSize_bounds; omega⟩ -
      boundaryWord (contractedWordTuple P g t) 0
        ⟨t.lower.val, by have := t.contractedSize_bounds; omega⟩ =
      boundaryWord P g t.upper - boundaryWord P g t.lower := by
  rw [contractedWord_boundary, contractedWord_boundary,
    IncreasingBoundaryTriple.expandPosition_upper, IncreasingBoundaryTriple.expandPosition_lower]

-- Verify both endpoint values in addition to the directed root displacement.
theorem exact_root_vertices_and_edge (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) :
    contractedWordTuple P g t 0 = P g ∧ contractedWordTuple P g t 1 = P (g + 1) ∧
      edge (contractedWordTuple P g t) 0 = P (g + 1) - P g := by
  exact ⟨contractedWord_last_vertex P g t, contractedWord_first_vertex P g t,
    contractedWord_physical_root P g t⟩

-- Singleton original zero support leaves no zero triple in the entire contracted tuple.
theorem contracted_zero_support_empty (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g}) :
    letI := t.contractedSize_neZero
    pointZeroTriples (contractedWordTuple P g t) = ∅ := by
  letI := t.contractedSize_neZero
  exact (pointZeroTriples_empty_iff _).mpr (contractedWord_G1 P g t hZ)

-- Only the proper case constructs an admissible original tree coefficient for Q at root zero.
theorem proper_contracted_faronly_interpretation {R : Type*} [CommRing R] [Invertible (2 : R)]
    (P : LabelledTuple n) (g : ZMod n) (t : IncreasingBoundaryTriple n) (hn : 3 ≤ n)
    (hZ : pointZeroTriples P = {t.vertexSet g})
    (hp : t.spanInterval ≠ fullBoundaryInterval hn) :
    letI := t.contractedSize_neZero
    ∃ (hm : 3 ≤ t.contractedSize) (hQ : G1 (contractedWordTuple P g t)),
      (treeCoefficient (contractedWordTuple P g t) hQ 0 hm : R) =
        farOnlyOutput (geometricBoundaryArray (contractedWordTuple P g t) 0)
          (fullBoundaryInterval hm) := by
  letI := t.contractedSize_neZero
  have hdata := proper_contracted_polygon_data P g t hn hZ hp
  exact ⟨hdata.1, hdata.2.1, treeCoefficient_farOnly (R := R) _ hdata.2.1 0 hdata.1⟩

-- In the full-span case the tuple still exists and preserves the root, but has only two positions.
theorem full_span_keeps_two_position_word (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hn : 3 ≤ n) (he : t.spanInterval = fullBoundaryInterval hn) :
    t.contractedSize = 2 ∧ ¬ 3 ≤ t.contractedSize ∧
      edge (contractedWordTuple P g t) 0 = edge P g := by
  have hm := (t.contractedSize_eq_two_iff hn).mpr he
  exact ⟨hm, by omega, contractedWord_physical_root P g t⟩

end
end ContractedGeometricWordIndependentReview
