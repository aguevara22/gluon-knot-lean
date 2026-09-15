namespace OffLeafContractionIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

theorem excluded_leaf_iff_wholly_on_one_side (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) :
    (¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) ↔
      J.right ≤ t.contractedLeaf.left ∨ t.contractedLeaf.right ≤ J.left := by
  constructor
  · exact t.contractedInterval_side J
  · rintro (h | h) hc
    · exact (not_le_of_gt t.contractedLeaf.increasing) (hc.2.trans h)
    · exact (not_le_of_gt t.contractedLeaf.increasing) (h.trans hc.1)

theorem every_original_raw_composition_roundtrips (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hj : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right))
    (π : IntervalComposition (t.expandInterval J)) :
    IntervalComposition.expandComposition t
      ((IntervalComposition.offLeafCompositionEquiv t J hj).symm π) = π :=
  (IntervalComposition.offLeafCompositionEquiv t J hj).apply_symm_apply π

theorem every_raw_part_and_child_preserved (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) (π : IntervalComposition J) :
    (IntervalComposition.expandComposition t π).parts = π.parts ∧
      ∀ k : Fin π.parts, (IntervalComposition.expandComposition t π).part k = t.expandInterval (π.part k) :=
  ⟨rfl, fun _ => rfl⟩

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
local instance : DecidableEq (IncreasingBoundaryTriple n) := Classical.decEq _

theorem complete_raw_sum_with_arbitrary_zero_or_nonzero_weights (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hj : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right))
    (W : IntervalComposition (t.expandInterval J) → R) :
    (∑ π : IntervalComposition J, W (IntervalComposition.expandComposition t π)) =
      ∑ π : IntervalComposition (t.expandInterval J), W π :=
  Fintype.sum_equiv (IntervalComposition.offLeafCompositionEquiv t J hj) _ _ (fun _ => rfl)

theorem inverse_transport_allows_touching_left_endpoint (t : IncreasingBoundaryTriple n)
    (H : TripleArray n R) (J : BoundaryInterval t.contractedSize)
    (hj : J.right ≤ t.contractedLeaf.left) :
    farOnlyCoordinates H (t.expandInterval J) = farOnlyCoordinates (contractedTripleArray t H) J := by
  apply farOnlyCoordinates_expanded_off_leaf t H J
  intro h
  exact (not_le_of_gt t.contractedLeaf.increasing) (h.2.trans hj)

theorem inverse_transport_allows_touching_right_endpoint (t : IncreasingBoundaryTriple n)
    (H : TripleArray n R) (J : BoundaryInterval t.contractedSize)
    (hj : t.contractedLeaf.right ≤ J.left) :
    farOnlyCoordinates H (t.expandInterval J) = farOnlyCoordinates (contractedTripleArray t H) J := by
  apply farOnlyCoordinates_expanded_off_leaf t H J
  intro h
  exact (not_le_of_gt t.contractedLeaf.increasing) (hj.trans h.1)

theorem all_actual_child_inverse_values_transport (t : IncreasingBoundaryTriple n)
    (H : TripleArray n R) (J : BoundaryInterval t.contractedSize)
    (hj : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right))
    (π : IntervalComposition J) (k : Fin π.parts) :
    farOnlyCoordinates H ((IntervalComposition.expandComposition t π).part k) =
      farOnlyCoordinates (contractedTripleArray t H) (π.part k) :=
  farOnlyCoordinates_expanded_off_leaf t H (π.part k)
    (t.subinterval_off_leaf J (π.part k) hj (π.part_bounds k))

theorem off_leaf_one_leaf_values_stay_one (t : IncreasingBoundaryTriple n)
    (H : TripleArray n R) (J : BoundaryInterval t.contractedSize)
    (hj : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right))
    (hleaf : J.leaves = 1) :
    farOnlyCoordinates H (t.expandInterval J) = 1 ∧
      farOnlyCoordinates (contractedTripleArray t H) J = 1 :=
  ⟨farOnlyCoordinates_leaf H _ ((t.expandInterval_leaves_off_leaf J hj).trans hleaf),
    farOnlyCoordinates_leaf _ J hleaf⟩

theorem full_reversed_transform_transports (t : IncreasingBoundaryTriple n)
    (H : TripleArray n R) (X : IntervalArray n R) (J : BoundaryInterval t.contractedSize)
    (hj : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) :
    farTransform (-(contractedTripleArray t H)) (fun I => X (t.expandInterval I)) J =
      farTransform (-H) X (t.expandInterval J) := by
  have h := nearFarTransform_expanded_off_leaf t 0 (-H) X J hj
  exact h

theorem two_side_arrays_have_identical_entire_contracted_inverse (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    farOnlyCoordinates (contractedTripleArray t H₁) = farOnlyCoordinates (contractedTripleArray t H₂) := by
  rw [contractedTripleArray_eq_off_critical t H₁ H₂ h]

theorem arbitrary_critical_entry_is_deleted_from_contracted_array (t : IncreasingBoundaryTriple n)
    (H : TripleArray n R) (v : R) :
    contractedTripleArray t (Function.update H t v) = contractedTripleArray t H := by
  apply contractedTripleArray_eq_off_critical t
  intro u hu
  exact Function.update_of_ne hu v H

theorem actual_geometric_inverse_transport_off_leaf (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (J : BoundaryInterval t.contractedSize)
    (hj : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) :
    farOnlyCoordinates (geometricBoundaryArray (R := R) P g) (t.expandInterval J) =
      farOnlyCoordinates (geometricBoundaryArray (contractedWordTuple P g t) 0) J := by
  rw [geometricBoundaryArray_contractedWord]
  exact farOnlyCoordinates_expanded_off_leaf t _ J hj

theorem full_contraction_uses_formal_leaf_inverse (t : IncreasingBoundaryTriple n)
    (H : TripleArray n R) (hn : 3 ≤ n) (hfull : t.spanInterval = fullBoundaryInterval hn) :
    t.contractedSize = 2 ∧ farOnlyCoordinates (contractedTripleArray t H) t.contractedLeaf = 1 :=
  ⟨(t.contractedSize_eq_two_iff hn).mpr hfull, contracted_leaf_inverse_value t H⟩

theorem actual_proper_output_retains_the_physical_root (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {t.vertexSet g}) (hproper : t.spanInterval ≠ fullBoundaryInterval hn) :
    farOnlyOutput (contractedTripleArray t (geometricBoundaryArray (R := R) P g))
      (fullBoundaryInterval (t.contractedSize_of_proper hn hproper)) =
      (treeCoefficient (contractedWordTuple P g t) (contractedWord_G1 P g t hz) 0
        (t.contractedSize_of_proper hn hproper) : R) ∧
    edge (contractedWordTuple P g t) 0 = edge P g :=
  ⟨contracted_output_tree P g t hn hz hproper, contractedWord_physical_root P g t⟩

theorem actual_contracted_geometry_commutes_with_reversal (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) :
    -(geometricBoundaryArray (R := R) (contractedWordTuple P g t) 0) =
      contractedTripleArray t (-geometricBoundaryArray P g) := by
  rw [geometricBoundaryArray_contractedWord, contractedTripleArray_neg]

theorem every_nonunary_expanded_child_is_strictly_shorter (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) (π : IntervalComposition J)
    (hπ : 2 ≤ π.parts) (k : Fin π.parts) :
    (t.expandInterval (π.part k)).leaves < (t.expandInterval J).leaves :=
  (IntervalComposition.expandComposition t π).part_leaves_lt hπ k

theorem unary_composition_still_has_one_distinguished_child (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hj : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right) :
    ∃! k : Fin (IntervalComposition.single J).parts,
      ((IntervalComposition.single J).part k).left ≤ t.contractedLeaf.left ∧
        t.contractedLeaf.right ≤ ((IntervalComposition.single J).part k).right :=
  (IntervalComposition.single J).unique_contracted_leaf_child t hj

theorem zero_contracted_factor_annuls_conditional_response (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    (J : BoundaryInterval t.contractedSize) (π : IntervalComposition J)
    (hj : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right) (s : R)
    (hchild : ∀ k : Fin π.parts,
      (π.part k).left ≤ t.contractedLeaf.left → t.contractedLeaf.right ≤ (π.part k).right →
      farOnlyCoordinates H₂ (t.expandInterval (π.part k)) - farOnlyCoordinates H₁ (t.expandInterval (π.part k)) =
        s * farOnlyCoordinates (contractedTripleArray t H₁) (π.part k))
    (l : Fin π.parts) (hz : farOnlyCoordinates (contractedTripleArray t H₁) (π.part l) = 0) :
    (∏ k : Fin π.parts, farOnlyCoordinates H₂ (t.expandInterval (π.part k))) -
      (∏ k : Fin π.parts, farOnlyCoordinates H₁ (t.expandInterval (π.part k))) = 0 := by
  rw [expanded_child_product_response t H₁ H₂ hH π hj s hchild]
  have hp : (∏ k : Fin π.parts, farOnlyCoordinates (contractedTripleArray t H₁) (π.part k)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ l) hz
  rw [hp, mul_zero]

theorem nonsurviving_lists_have_zero_difference_not_zero_value (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    (I : BoundaryInterval n) (π : IntervalComposition I) (hπ : ¬ IntervalComposition.SurvivingCuts t π) :
    (∏ k : Fin π.parts, farOnlyCoordinates H₂ (π.part k)) -
      (∏ k : Fin π.parts, farOnlyCoordinates H₁ (π.part k)) = 0 :=
  sub_eq_zero.mpr (nonsurviving_child_product_unchanged t H₁ H₂ hH π hπ).symm

end
end OffLeafContractionIndependentReview
