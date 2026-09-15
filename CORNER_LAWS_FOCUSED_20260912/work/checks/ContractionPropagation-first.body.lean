namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Propagate the actual critical inverse-coordinate difference through
every containing interval. The source difference is defined by the actual
inverse arrays; neither its geometric value nor a propagation law is assumed. -/
theorem farOnlyCoordinates_contraction_propagation (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    (J : BoundaryInterval t.contractedSize)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right) :
    farOnlyCoordinates H₂ (t.expandInterval J) - farOnlyCoordinates H₁ (t.expandInterval J) =
      (farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval) *
        farOnlyCoordinates (contractedTripleArray t H₁) J := by
  classical
  by_cases hleaf : J = t.contractedLeaf
  · subst J
    rw [t.expandInterval_contractedLeaf, farOnlyCoordinates_leaf _ _ t.contractedLeaf_leaves, mul_one]
  · let s := farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval
    let Hq := contractedTripleArray t H₁
    have hI : t.expandInterval J ≠ t.spanInterval := by
      intro he
      exact hleaf (t.expandInterval_injective (he.trans t.expandInterval_contractedLeaf.symm))
    have hJ2 : 2 ≤ J.leaves := t.containing_contracted_nonleaf J hJ hleaf
    have hI2 : 2 ≤ (t.expandInterval J).leaves := by
      have hc := (t.expandInterval_contains J).mpr hJ
      have hl : (t.expandInterval J).left.val ≤ t.lower.val := hc.1
      have hr : t.upper.val ≤ (t.expandInterval J).right.val := hc.2
      have hxy : t.lower.val < t.middle.val := t.lower_middle
      have hyz : t.middle.val < t.upper.val := t.middle_upper
      change 2 ≤ (t.expandInterval J).right.val - (t.expandInterval J).left.val
      omega
    let f (π : IntervalComposition (t.expandInterval J)) :=
      π.nearFarWeight 0 H₁ *
        ((∏ k : Fin π.parts, farOnlyCoordinates H₂ (π.part k)) -
          ∏ k : Fin π.parts, farOnlyCoordinates H₁ (π.part k))
    have hfzero (π : IntervalComposition (t.expandInterval J)) (_hp : 2 ≤ π.parts)
        (hπ : ¬ IntervalComposition.SurvivingCuts t π) : f π = 0 := by
      have hp := nonsurviving_child_product_unchanged t H₁ H₂ hH π hπ
      simp only [f, hp, sub_self, mul_zero]
    have hreindex := IntervalComposition.sum_nonunary_expansion t J f hfzero
    have hsum :
        (∑ π : {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts},
          π.val.nearFarWeight 0 H₂ * ∏ k : Fin π.val.parts, farOnlyCoordinates H₂ (π.val.part k)) -
        (∑ π : {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts},
          π.val.nearFarWeight 0 H₁ * ∏ k : Fin π.val.parts, farOnlyCoordinates H₁ (π.val.part k)) =
        s * ∑ π : {π : IntervalComposition J // 2 ≤ π.parts},
          π.val.nearFarWeight 0 Hq * ∏ k : Fin π.val.parts, farOnlyCoordinates Hq (π.val.part k) := by
      rw [← Finset.sum_sub_distrib]
      have hd :
          (∑ π : {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts},
            (π.val.nearFarWeight 0 H₂ * ∏ k : Fin π.val.parts, farOnlyCoordinates H₂ (π.val.part k)) -
            (π.val.nearFarWeight 0 H₁ * ∏ k : Fin π.val.parts, farOnlyCoordinates H₁ (π.val.part k))) =
          ∑ π : {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts}, f π.val := by
        apply Finset.sum_congr rfl
        intro π _
        rw [← π.val.farWeight_unchanged_off_span t H₁ H₂ hH hI]
        dsimp only [f]
        ring
      rw [hd, ← hreindex, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro π _
      have hp := expanded_child_product_response t H₁ H₂ hH π.val hJ s
        (fun k hkl hkr => farOnlyCoordinates_contraction_propagation t H₁ H₂ hH
          (π.val.part k) ⟨hkl, hkr⟩)
      change (IntervalComposition.expandComposition t π.val).nearFarWeight 0 H₁ *
        ((∏ k : Fin π.val.parts, farOnlyCoordinates H₂ (t.expandInterval (π.val.part k))) -
          ∏ k : Fin π.val.parts, farOnlyCoordinates H₁ (t.expandInterval (π.val.part k))) = _
      rw [hp]
      change π.val.nearFarWeight 0 Hq *
        (s * ∏ k : Fin π.val.parts, farOnlyCoordinates Hq (π.val.part k)) = _
      ring
    have he₁ := farOnly_nonleaf_E H₁ (t.expandInterval J) hI2
    have he₂ := farOnly_nonleaf_E H₂ (t.expandInterval J) hI2
    have heq := farOnly_nonleaf_E Hq J hJ2
    unfold farTransform at he₁ he₂ heq
    rw [nearFarTransform_eq_triangular] at he₁ he₂ heq
    unfold triangularTransform at he₁ he₂ heq
    change farOnlyCoordinates H₂ (t.expandInterval J) - farOnlyCoordinates H₁ (t.expandInterval J) =
      s * farOnlyCoordinates Hq J
    linear_combination he₂ - he₁ - hsum - s * heq
termination_by (t.expandInterval J).leaves
decreasing_by
  exact (IntervalComposition.expandComposition t π.val).part_leaves_lt π.property k

end
end SM
