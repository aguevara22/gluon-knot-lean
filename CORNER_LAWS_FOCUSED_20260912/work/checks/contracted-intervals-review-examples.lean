namespace ContractedIntervalsIndependentReview
open SM

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

-- The expansion range is exactly all intervals with two surviving endpoints.
theorem interval_range_iff_surviving_endpoints (t : IncreasingBoundaryTriple n) (I : BoundaryInterval n) :
    (∃ J : BoundaryInterval t.contractedSize, t.expandInterval J = I) ↔
      (I.left ≤ t.lower ∨ t.upper ≤ I.left) ∧ (I.right ≤ t.lower ∨ t.upper ≤ I.right) := by
  constructor
  · rintro ⟨J, rfl⟩
    exact ⟨t.expandPosition_survives J.left, t.expandPosition_survives J.right⟩
  · rintro ⟨hl, hr⟩
    exact ⟨t.contractInterval I hl hr, t.expand_contractInterval I hl hr⟩

-- Every containing old interval occurs exactly once and its contraction contains the formal leaf.
theorem containing_interval_unique_preimage (t : IncreasingBoundaryTriple n) (I : BoundaryInterval n)
    (hI : I.left ≤ t.lower ∧ t.upper ≤ I.right) :
    ∃! J : BoundaryInterval t.contractedSize,
      t.expandInterval J = I ∧ J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right := by
  obtain ⟨J, hJ⟩ := t.containing_interval_is_expanded I hI
  refine ⟨J, hJ, ?_⟩
  intro K hK
  exact t.expandInterval_injective (hK.1.trans hJ.1.symm)

-- Precisely the distinguished formal leaf expands to the original critical span.
theorem critical_interval_iff_formal_leaf (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) :
    t.expandInterval J = t.spanInterval ↔ J = t.contractedLeaf := by
  constructor
  · intro h
    exact t.expandInterval_injective (h.trans t.expandInterval_contractedLeaf.symm)
  · rintro rfl
    exact t.expandInterval_contractedLeaf

-- Every strictly larger containing source interval has an actual nonleaf contraction.
theorem all_strictly_larger_intervals_contract_to_nonleaf (t : IncreasingBoundaryTriple n)
    (I : BoundaryInterval n) (hI : I.left ≤ t.lower ∧ t.upper ≤ I.right) (hne : I ≠ t.spanInterval) :
    ∃ J : BoundaryInterval t.contractedSize, t.expandInterval J = I ∧ 2 ≤ J.leaves := by
  obtain ⟨J, he, hc⟩ := t.containing_interval_is_expanded I hI
  refine ⟨J, he, t.containing_contracted_nonleaf J hc ?_⟩
  intro hj
  apply hne
  rw [← he, hj]
  exact t.expandInterval_contractedLeaf

-- The actual inverse has value one on the formal leaf, including a complete size-two word.
theorem actual_inverse_formal_leaf_value {R : Type*} [CommRing R] [Invertible (2 : R)]
    (t : IncreasingBoundaryTriple n) (H : TripleArray t.contractedSize R) :
    farOnlyCoordinates H t.contractedLeaf = 1 :=
  farOnlyCoordinates_leaf H t.contractedLeaf t.contractedLeaf_leaves

-- The proper containing-interval hypothesis is sufficient for the zero equation used in propagation.
theorem actual_inverse_strict_containing_equation {R : Type*} [CommRing R] [Invertible (2 : R)]
    (t : IncreasingBoundaryTriple n) (H : TripleArray t.contractedSize R)
    (J : BoundaryInterval t.contractedSize)
    (hc : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)
    (hne : J ≠ t.contractedLeaf) :
    farTransform H (farOnlyCoordinates H) J = 0 :=
  farOnly_nonleaf_E H J (t.containing_contracted_nonleaf J hc hne)

-- Contraction of the critical span returns its exact formal leaf, not merely an interval of the same length.
theorem critical_span_contracts_exactly_to_leaf (t : IncreasingBoundaryTriple n) :
    t.contractInterval t.spanInterval (Or.inl le_rfl) (Or.inr le_rfl) = t.contractedLeaf := by
  apply t.expandInterval_injective
  rw [t.expand_contractInterval]
  exact t.expandInterval_contractedLeaf.symm

-- The entire increasing triple is retained injectively by the actual position expansion.
theorem triple_expansion_injective (t : IncreasingBoundaryTriple n) :
    Function.Injective t.expandTriple := by
  intro u v he
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact t.expandPosition_strict.injective (congrArg IncreasingBoundaryTriple.lower he)
  · exact t.expandPosition_strict.injective (congrArg IncreasingBoundaryTriple.middle he)
  · exact t.expandPosition_strict.injective (congrArg IncreasingBoundaryTriple.upper he)

-- No expanded triple can reintroduce the deleted critical middle and equal the critical triple.
theorem expanded_triple_is_not_critical (t : IncreasingBoundaryTriple n)
    (u : IncreasingBoundaryTriple t.contractedSize) : t.expandTriple u ≠ t := by
  intro he
  have hm := congrArg IncreasingBoundaryTriple.middle he
  have hs := t.expandPosition_survives u.middle
  change t.expandPosition u.middle = t.middle at hm
  rw [hm] at hs
  rcases hs with hl | hr
  · exact (not_le_of_gt t.lower_middle) hl
  · exact (not_le_of_gt t.middle_upper) hr

end
end ContractedIntervalsIndependentReview
