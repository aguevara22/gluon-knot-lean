namespace GeometricGapResponseIndependentReview
open SM Filter Topology
noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]
local instance : DecidableEq (IncreasingBoundaryTriple n) := Classical.decEq _

theorem gap_values_have_exact_four_cases (H : TripleArray n R) (I : BoundaryInterval n) :
    wallGapU H I 1 = boundaryUnitArray I ∧ wallGapV H I 1 = farOnlyOutput H I ∧
    wallGapU H I (-1) = farOnlyOutput H I ∧ wallGapV H I (-1) = boundaryUnitArray I := by
  simp [wallGapU, wallGapV]

theorem leaf_gap_values_are_both_one (H : TripleArray n R) (I : BoundaryInterval n)
    (hI : I.leaves = 1) (ε : SignType) : wallGapU H I ε = 1 ∧ wallGapV H I ε = 1 := by
  simp [wallGapU, wallGapV, boundaryUnitArray_leaf I hI, (farOnly_leaf_values H I hI).2]

theorem reversing_nonzero_epsilon_exchanges_gap_values (H : TripleArray n R)
    (I : BoundaryInterval n) (ε : SignType) (hε : ε = 1 ∨ ε = -1) :
    wallGapU H I (-ε) = wallGapV H I ε ∧ wallGapV H I (-ε) = wallGapU H I ε := by
  rcases hε with rfl | rfl <;> simp [wallGapU, wallGapV]

theorem nonleaf_positive_U_and_negative_V_vanish (H : TripleArray n R)
    (I : BoundaryInterval n) (hI : 2 ≤ I.leaves) :
    wallGapU H I 1 = 0 ∧ wallGapV H I (-1) = 0 := by
  have he : boundaryUnitArray (R := R) I = 0 := by
    rw [← farOnlyCoordinates_equation H]
    exact farOnly_nonleaf_E H I hI
  simp [wallGapU, wallGapV, he]

theorem critical_entry_changes_no_excluded_gap_value (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u)
    (J : BoundaryInterval n) (hj : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) (ε : SignType) :
    wallGapU H₁ J ε = wallGapU H₂ J ε ∧ wallGapV H₁ J ε = wallGapV H₂ J ε := by
  have hb := farOnlyOutput_unchanged_off_critical H₁ H₂ t h J hj
  simp only [wallGapU, wallGapV, hb, and_self]

theorem restricted_labels_read_the_actual_original_tuple (P : LabelledTuple n) (g : ZMod n)
    (J : BoundaryInterval n) (j : ZMod (J.leaves + 1)) :
    restrictedWordTuple P g J j = P (restrictedVertexIndex g J j) := rfl

theorem restricted_label_equality_is_exact (g : ZMod n) (J : BoundaryInterval n)
    (i j : ZMod (J.leaves + 1)) :
    restrictedVertexIndex g J i = restrictedVertexIndex g J j ↔ i = j :=
  ⟨fun h => restrictedVertexIndex_injective g J h, fun h => h ▸ rfl⟩

theorem off_span_word_has_G1_and_physical_closing_edge (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hz : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hj : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) :
    G1 (restrictedWordTuple P g J) ∧
      edge (restrictedWordTuple P g J) 0 = boundaryWord P g J.left - boundaryWord P g J.right :=
  ⟨restrictedWord_G1_off_critical P g t hz J hj, restrictedWord_closing_edge P g J⟩

theorem off_span_nonleaf_output_is_actual_closed_tree (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hz : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hj : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) (hleaf : 2 ≤ J.leaves) :
    farOnlyOutput (geometricBoundaryArray (R := R) P g) J =
      (treeCoefficient (restrictedWordTuple P g J)
        (restrictedWord_G1_off_critical P g t hz J hj) 0 (by omega : 3 ≤ J.leaves + 1) : R) :=
  farOnlyOutput_restricted_tree P g J hleaf (restrictedWord_G1_off_critical P g t hz J hj)

theorem common_radius_covers_both_actual_side_maps (w : WallGerm n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hz : pointZeroTriples w.center = {t.vertexSet g}) :
    ∃ d : ℝ, 0 < d ∧ d ≤ w.radius ∧ ∀ s : w.SideParameter, s.val < d → ∀ positive : Bool,
      (∀ u : IncreasingBoundaryTriple n, u ≠ t →
        geometricBoundaryArray (R := R) (w.sideTuple positive s).val g u =
          geometricBoundaryArray w.center g u) ∧
      (∀ J : BoundaryInterval n, ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right) →
        farOnlyCoordinates (geometricBoundaryArray (R := R) (w.sideTuple positive s).val g) J =
          farOnlyCoordinates (geometricBoundaryArray w.center g) J ∧
        farOnlyOutput (geometricBoundaryArray (R := R) (w.sideTuple positive s).val g) J =
          farOnlyOutput (geometricBoundaryArray w.center g) J) := by
  obtain ⟨d, hd, hr, hs⟩ := w.boundary_values_stable_near_center (R := R) g t hz
  refine ⟨d, hd, hr, ?_⟩
  intro s hsd positive
  have ha : |(w.sideTime positive s).val| < d := by
    cases positive <;> simpa [WallGerm.sideTime, abs_of_pos s.property.1] using hsd
  have h := hs (w.sideTime positive s) ha
  exact ⟨h.1, fun J hj => ⟨h.2.1 J hj, h.2.2 J hj⟩⟩

theorem arbitrary_critical_value_retains_geometric_gap_sum (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (v : R) (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    cutWeightedSum (t.fixedFarGate (Function.update (geometricBoundaryArray P g) t v))
      (farOnlyCoordinates (Function.update (geometricBoundaryArray P g) t v)) t.leftInterval =
      wallGapU (geometricBoundaryArray P g) t.leftInterval (wallLeftEpsilon x y z) := by
  let H : TripleArray n R := Function.update (geometricBoundaryArray P g) t v
  have hh : ∀ u, u ≠ t → H u = geometricBoundaryArray P g u := by
    intro u hu
    exact Function.update_of_ne hu v (geometricBoundaryArray P g)
  have hs := (geometric_gap_sums P g t H hh p ω x y z hx hy hz hyx hzy hzx).1
  have hj : ¬ (t.leftInterval.left ≤ t.lower ∧ t.upper ≤ t.leftInterval.right) := by
    intro h; exact (not_le_of_gt t.middle_upper) h.2
  exact hs.trans (critical_entry_changes_no_excluded_gap_value H _ t hh _ hj _).1

theorem full_tree_response_at_equal_positive_side_distances (w : WallGerm n) (g : ZMod n)
    (hn : 3 ≤ n) (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples w.center = {t.vertexSet g})
    (hspan : t.spanInterval = fullBoundaryInterval hn) (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord w.center g t.lower = p + x • ω)
    (hy : boundaryWord w.center g t.middle = p + y • ω)
    (hz : boundaryWord w.center g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    ∃ d : ℝ, 0 < d ∧ d ≤ w.radius ∧ ∀ s : w.SideParameter, s.val < d →
      (treeCoefficient (w.sideTuple true s).val (w.sideTuple true s).property.1 g hn : R) -
        (treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn : R) =
        ((geometricBoundaryArray (R := R) (w.sideTuple true s).val g t -
          geometricBoundaryArray (w.sideTuple false s).val g t) * ⅟ (2 : R)) *
          ((wallGapU (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
            wallGapU (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)) +
           (wallGapV (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
            wallGapV (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z))) := by
  obtain ⟨d, hd, hr, h⟩ := w.full_span_tree_response (R := R) g hn t hZ hspan p ω x y z hx hy hz hyx hzy hzx
  refine ⟨d, hd, hr, ?_⟩
  intro s hs
  have hm : (w.sideTime false s).val < 0 := by
    change -s.val < 0
    linarith [s.property.1]
  have hp : 0 < (w.sideTime true s).val := by simpa [WallGerm.sideTime] using s.property.1
  have ham : |(w.sideTime false s).val| < d := by
    simpa [WallGerm.sideTime, abs_of_pos s.property.1] using hs
  have hap : |(w.sideTime true s).val| < d := by
    simpa [WallGerm.sideTime, abs_of_pos s.property.1] using hs
  exact h (w.sideTime false s) (w.sideTime true s) hm hp ham hap

end
end GeometricGapResponseIndependentReview
