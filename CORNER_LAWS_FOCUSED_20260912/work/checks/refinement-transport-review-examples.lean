namespace RefinementTransportIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

-- Characterize the actual raw child intervals, including unique indexing.
theorem actual_parts_are_exact_consecutive_pairs (π : IntervalComposition I)
    (J : BoundaryInterval n) :
    π.cutSet.Consecutive J ↔ ∃! k : Fin π.parts, π.part k = J := by
  constructor
  · intro hJ
    obtain ⟨k, hk⟩ := π.exists_part_of_consecutive J hJ
    exact ⟨k, hk, fun l hl => π.part_injective (hl.trans hk.symm)⟩
  · rintro ⟨k, rfl, _⟩
    exact π.part_consecutive k

-- Every globally fine child has exactly one containing outer part.
theorem actual_fine_child_has_unique_outer (π : IntervalComposition I)
    (T : RefiningCutSet π) (J : BoundaryInterval n) (hJ : T.val.Consecutive J) :
    ∃! k : Fin π.parts, (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right := by
  obtain ⟨k, hk⟩ := π.consecutive_contained_in_part T.val T.property J hJ
  exact ⟨k, hk, fun l hl => π.containing_part_unique J hl hk⟩

-- A physical interior position determines one actual neighboring triple.
theorem actual_near_sample_unique (π : IntervalComposition I) (k : Fin (π.parts - 1)) :
    ∃! t : IncreasingBoundaryTriple n,
      π.cutSet.Consecutive t.leftInterval ∧ π.cutSet.Consecutive t.rightInterval ∧
        t.middle = π.interiorPosition k := by
  refine ⟨π.nearTriple k, ⟨(π.nearTriple_consecutive k).1,
    (π.nearTriple_consecutive k).2, π.nearTriple_middle_position k⟩, ?_⟩
  intro t ht
  exact (π.nearTriple_eq_of_consecutive k t ht.1 ht.2.1 ht.2.2.symm).symm

-- Any coefficient array therefore samples the exact same three physical positions.
theorem arbitrary_array_samples_actual_neighbors {R : Type*}
    (π : IntervalComposition I) (k : Fin (π.parts - 1)) (D : TripleArray n R)
    (t : IncreasingBoundaryTriple n)
    (hl : π.cutSet.Consecutive t.leftInterval) (hr : π.cutSet.Consecutive t.rightInterval)
    (hm : π.interiorPosition k = t.middle) : D (π.nearTriple k) = D t := by
  rw [π.nearTriple_eq_of_consecutive k t hl hr hm]

-- The chosen index equivalence preserves the full child interval.
theorem refined_index_keeps_interval (π : IntervalComposition I) (T : RefiningCutSet π)
    (a : Σ k : Fin π.parts, Fin (π.refinementInner T k).parts) :
    T.val.toComposition.part (π.refinedChildrenEquiv T a) =
      (π.refinementInner T a.1).part a.2 :=
  π.refinedChildIndex_part T a

-- The bijection also fixes the total number of children, so none is lost or repeated.
theorem child_count_is_sum_of_inner_counts (π : IntervalComposition I) (T : RefiningCutSet π) :
    (∑ k : Fin π.parts, (π.refinementInner T k).parts) = T.val.toComposition.parts := by
  have h := Fintype.card_congr (π.refinedChildrenEquiv T)
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h

-- Recover the original raw part count and cut map, not just an equal set of endpoints.
theorem recovered_inner_has_raw_data (π : IntervalComposition I)
    (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k)) (k : Fin π.parts) :
    (π.refinementInner (π.flattenRefinement (fun k => (σ k).cutSet)) k).parts = (σ k).parts ∧
      HEq (π.refinementInner (π.flattenRefinement (fun k => (σ k).cutSet)) k).cut (σ k).cut := by
  rw [π.refinementInner_flatten σ k]
  exact ⟨rfl, HEq.rfl⟩

-- The actual source marked-refinement map, not an unrelated enumeration, has the same product.
theorem actual_marked_refinement_child_product {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k))
    (X : BoundaryInterval n → R) :
    (∏ k : Fin π.parts, ∏ j : Fin (σ k).parts, X ((σ k).part j)) =
      ∏ r : Fin (IntervalComposition.nestedMarkedCutEquiv I ⟨π, σ⟩).1.parts,
        X ((IntervalComposition.nestedMarkedCutEquiv I ⟨π, σ⟩).1.part r) :=
  π.prod_nested_children σ X

-- Unary inner compositions keep exactly their outer child coordinate.
theorem all_inner_unary_product {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (X : BoundaryInterval n → R) :
    (∏ k : Fin π.parts, X (π.part k)) =
      ∏ r : Fin (π.flattenCutSets
        (fun k => (IntervalComposition.single (π.part k)).cutSet)).toComposition.parts,
        X ((π.flattenCutSets
          (fun k => (IntervalComposition.single (π.part k)).cutSet)).toComposition.part r) := by
  simpa only [IntervalComposition.single_product] using
    π.prod_nested_children (fun k => IntervalComposition.single (π.part k)) X

-- Full/empty markings are the exact interior universe and empty set.
theorem empty_and_full_index_marks (π : IntervalComposition I) :
    (π.indexMarks ∅).val = ∅ ∧
      (π.indexMarks Finset.univ).val = π.cutSet.interior.val := by
  constructor
  · simp [IntervalComposition.indexMarks]
  · simpa [IntervalComposition.indexMarks] using π.indexMarks_compl ∅

-- Complementary marks never include either endpoint or an unrelated boundary position.
theorem unmarked_positions_are_exactly_relative (π : IntervalComposition I)
    (s : Finset (Fin (π.parts - 1))) (x : Fin n) (hx : x ∈ (π.indexMarks sᶜ).val) :
    I.left < x ∧ x < I.right ∧ x ∉ (π.indexMarks s).val := by
  rw [π.indexMarks_compl] at hx
  have h := Finset.mem_sdiff.mp hx
  exact ⟨(π.cutSet.interior.property x h.1).1,
    (π.cutSet.interior.property x h.1).2, h.2⟩

-- Both chosen and complementary products transport their actual physical arguments.
theorem marked_and_unmarked_product_transport {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (m : MarkedCuts π.cutSet) (f g : Fin n → R) :
    (∏ k ∈ π.markIndices m, f (π.interiorPosition k)) *
      (∏ k ∈ (π.markIndices m)ᶜ, g (π.interiorPosition k)) =
    (∏ x ∈ m.val, f x) * (∏ x ∈ π.cutSet.interior.val \ m.val, g x) := by
  rw [π.prod_markIndices, π.prod_indexMarks, π.indexMarks_compl, π.indexMarks_markIndices]

-- Every one of the 2^(parts-1) possible source markings occurs exactly once.
theorem all_markings_have_full_cardinality (π : IntervalComposition I) :
    Fintype.card (MarkedCuts π.cutSet) = 2 ^ (π.parts - 1) := by
  have h := Fintype.card_congr π.marksIndexEquiv
  simpa only [Fintype.card_finset, Fintype.card_fin] using h.symm

-- In the unary case the complete sum contains precisely the empty marking.
theorem unary_marking_sum {R : Type*} [AddCommMonoid R]
    (I : BoundaryInterval n) (f : MarkedCuts (IntervalComposition.single I).cutSet → R) :
    (∑ m : MarkedCuts (IntervalComposition.single I).cutSet, f m) =
      f ((IntervalComposition.single I).indexMarks ∅) := by
  rw [← (IntervalComposition.single I).sum_all_indexMarks f]
  change (∑ s : Finset (Fin 0), f ((IntervalComposition.single I).indexMarks s)) = _
  simp only [Fintype.sum_unique]
  exact congrArg (fun s : Finset (Fin 0) => f ((IntervalComposition.single I).indexMarks s))
    (Subsingleton.elim _ _)

end
end RefinementTransportIndependentReview
