namespace NonunaryContractionIndependentReview
open SM
open SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

-- Exact raw arity and cut positions are preserved by the nonunary subtype map.
theorem nonunary_map_exact_parts_and_cuts (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : {π : IntervalComposition J // 2 ≤ π.parts}) :
    (expandNonunaryComposition t π).val.parts = π.val.parts ∧
      ∀ k : Fin (π.val.parts + 1),
        (expandNonunaryComposition t π).val.cut k = t.expandPosition (π.val.cut k) := by
  exact ⟨rfl, fun _ => rfl⟩

-- The complete surviving nonunary range is covered exactly once.
theorem unique_nonunary_preimage_iff_survives (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (π : {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts}) :
    (∃! ρ : {ρ : IntervalComposition J // 2 ≤ ρ.parts}, expandNonunaryComposition t ρ = π) ↔
      SurvivingCuts t π.val := by
  constructor
  · rintro ⟨ρ, he, _⟩
    exact (mem_range_expandNonunary t J π).mp ⟨ρ, he⟩
  · intro hs
    obtain ⟨ρ, he⟩ := (mem_range_expandNonunary t J π).mpr hs
    refine ⟨ρ, he, ?_⟩
    intro σ hσ
    exact expandNonunaryComposition_injective t J (hσ.trans he.symm)

-- On a containing parent, the exact range consists of all raw nonunary compositions with a containing child.
theorem nonunary_range_iff_containing_child (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)
    (π : {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts}) :
    π ∈ Set.range (expandNonunaryComposition t (J := J)) ↔
      ∃ k : Fin π.val.parts, (π.val.part k).left ≤ t.lower ∧ t.upper ≤ (π.val.part k).right :=
  (mem_range_expandNonunary t J π).trans
    (survivingCuts_iff_containing_child t π.val ((t.expandInterval_contains J).mpr hJ))

-- Reindex the difference when omitted original side terms agree, without requiring either value to vanish.
theorem unchanged_original_sides_suffice {R : Type*} [AddCommGroup R]
    (t : IncreasingBoundaryTriple n) (J : BoundaryInterval t.contractedSize)
    (A B : IntervalComposition (t.expandInterval J) → R)
    (hAB : ∀ π : IntervalComposition (t.expandInterval J),
      2 ≤ π.parts → ¬ SurvivingCuts t π → A π = B π) :
    (∑ π : {π : IntervalComposition J // 2 ≤ π.parts},
      B (expandComposition t π.val) - A (expandComposition t π.val)) =
      ∑ π : {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts}, B π.val - A π.val := by
  apply sum_nonunary_expansion t J (fun π => B π - A π)
  intro π hp hs
  exact sub_eq_zero.mpr (hAB π hp hs).symm

-- An arbitrary common baseline cancels: no zero premise is imposed on that original value.
theorem arbitrary_baseline_response {R : Type*} [AddCommGroup R]
    (t : IncreasingBoundaryTriple n) (J : BoundaryInterval t.contractedSize)
    (c : R) (d : IntervalComposition (t.expandInterval J) → R)
    (hd : ∀ π : IntervalComposition (t.expandInterval J),
      2 ≤ π.parts → ¬ SurvivingCuts t π → d π = 0) :
    (∑ π : {π : IntervalComposition J // 2 ≤ π.parts},
      (c + d (expandComposition t π.val)) - c) =
      ∑ π : {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts}, d π.val := by
  simpa only [add_sub_cancel_left] using sum_nonunary_expansion t J d hd

-- At the formal leaf the contracted nonunary domain is empty; the conditional response sum is therefore zero.
theorem formal_leaf_conditional_response_zero {R : Type*} [AddCommMonoid R]
    (t : IncreasingBoundaryTriple n)
    (f : IntervalComposition (t.expandInterval t.contractedLeaf) → R)
    (hz : ∀ π : IntervalComposition (t.expandInterval t.contractedLeaf),
      2 ≤ π.parts → ¬ SurvivingCuts t π → f π = 0) :
    (∑ π : {π : IntervalComposition (t.expandInterval t.contractedLeaf) // 2 ≤ π.parts}, f π.val) = 0 := by
  letI : IsEmpty {π : IntervalComposition t.contractedLeaf // 2 ≤ π.parts} :=
    ⟨fun π => by
      have hparts := π.val.parts_eq_one_of_leaves_eq_one t.contractedLeaf_leaves
      have hp := π.property
      omega⟩
  simpa using (sum_nonunary_expansion t t.contractedLeaf f hz).symm

end
end NonunaryContractionIndependentReview
