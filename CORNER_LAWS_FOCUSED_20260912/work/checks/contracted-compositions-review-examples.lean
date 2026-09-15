namespace ContractedCompositionsIndependentReview
open SM
open SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

-- Every raw cut survives with its exact old position; there is no hidden relabelled enumeration.
theorem expanded_complete_cut_set (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J) :
    (expandComposition t π).cutSet.cuts = π.cutSet.cuts.image t.expandPosition := by
  simp only [IntervalComposition.cutSet, expandComposition, Finset.image_image]

-- The actual unique unary raw composition belongs to the expansion domain and stays unary.
theorem unary_composition_retained (t : IncreasingBoundaryTriple n) (J : BoundaryInterval t.contractedSize) :
    expandComposition t (IntervalComposition.single J) = IntervalComposition.single (t.expandInterval J) := by
  apply IntervalComposition.eq_single_of_parts_eq_one
  rfl

-- Every surviving raw composition of a containing interval has exactly one containing child.
theorem surviving_composition_has_unique_containing_child (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)
    (π : IntervalComposition (t.expandInterval J)) (hπ : SurvivingCuts t π) :
    ∃! k : Fin π.parts, (π.part k).left ≤ t.lower ∧ t.upper ≤ (π.part k).right := by
  obtain ⟨k, hk⟩ := containing_child_of_survivingCuts t π ((t.expandInterval_contains J).mpr hJ) hπ
  refine ⟨k, hk, ?_⟩
  intro l hl
  exact π.halfOpen_part_unique t.lower
    ⟨hl.1, lt_of_lt_of_le (lt_trans t.lower_middle t.middle_upper) hl.2⟩
    ⟨hk.1, lt_of_lt_of_le (lt_trans t.lower_middle t.middle_upper) hk.2⟩

-- The actual source equivalence reconstructs each entire raw original cut sequence.
theorem containing_equivalence_recovers_raw_composition (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)
    (π : IntervalComposition (t.expandInterval J))
    (hπ : ∃ k : Fin π.parts, (π.part k).left ≤ t.lower ∧ t.upper ≤ (π.part k).right) :
    (containingCompositionEquiv t J hJ ((containingCompositionEquiv t J hJ).symm ⟨π, hπ⟩)).val = π :=
  congrArg Subtype.val ((containingCompositionEquiv t J hJ).apply_symm_apply ⟨π, hπ⟩)

-- Reindex arbitrary summands on the complete domains, with no nonunary restriction.
theorem full_containing_sum_reindexed {R : Type*} [AddCommMonoid R]
    (t : IncreasingBoundaryTriple n) (J : BoundaryInterval t.contractedSize)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)
    (f : IntervalComposition (t.expandInterval J) → R) :
    (∑ π : IntervalComposition J, f (expandComposition t π)) =
      ∑ ρ : {π : IntervalComposition (t.expandInterval J) //
        ∃ k : Fin π.parts, (π.part k).left ≤ t.lower ∧ t.upper ≤ (π.part k).right}, f ρ.val := by
  classical
  exact Fintype.sum_equiv (containingCompositionEquiv t J hJ) _ _ (fun _ => rfl)

-- Every actual child factor is evaluated on the expansion of that same child interval.
theorem full_child_product_transported {R : Type*} [CommMonoid R]
    (t : IncreasingBoundaryTriple n) {J : BoundaryInterval t.contractedSize}
    (π : IntervalComposition J) (X : IntervalArray n R) :
    (∏ k : Fin (expandComposition t π).parts, X ((expandComposition t π).part k)) =
      ∏ k : Fin π.parts, X (t.expandInterval (π.part k)) := rfl

-- Every near and far gate uses the expanded actual triple for arbitrary coefficient arrays.
theorem full_nearfar_weight_transported {R : Type*} [CommRing R] [Invertible (2 : R)]
    (t : IncreasingBoundaryTriple n) {J : BoundaryInterval t.contractedSize}
    (π : IntervalComposition J) (D H : TripleArray n R) :
    (expandComposition t π).nearFarWeight D H =
      π.nearFarWeight (fun u => D (t.expandTriple u)) (fun u => H (t.expandTriple u)) := rfl

end
end ContractedCompositionsIndependentReview
