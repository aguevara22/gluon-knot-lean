namespace CriticalContractionChildIndependentReview
open SM

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

-- At most one index is in the entire set of children containing a positive interval.
theorem containing_child_card_le_one (π : IntervalComposition I) (J : BoundaryInterval n) :
    (Finset.univ.filter (fun k : Fin π.parts =>
      (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro k hk l hl
  exact π.part_contains_unique J (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hl).2

-- Every formal leaf in I belongs to one complete child, including at a shared cut.
theorem formal_leaf_has_unique_child (π : IntervalComposition I) (J : BoundaryInterval n)
    (hj : J.leaves = 1) (hl : I.left ≤ J.left) (hr : J.right ≤ I.right) :
    ∃! k : Fin π.parts, (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right := by
  obtain ⟨k, hk⟩ := π.exists_halfOpen_part J.left hl (lt_of_lt_of_le J.increasing hr)
  have hkright : J.right ≤ (π.part k).right := by
    have hi := J.increasing
    change J.left.val < J.right.val at hi
    change J.right.val - J.left.val = 1 at hj
    have hp := hk.2
    change J.left.val < (π.part k).right.val at hp
    change J.right.val ≤ (π.part k).right.val
    omega
  refine ⟨k, ⟨hk.1, hkright⟩, ?_⟩
  intro l hl
  exact π.part_contains_unique J hl ⟨hk.1, hkright⟩

variable {R : Type*} [CommRing R]

-- The unaffected factor product is identical on both sides: the response has no side ambiguity.
theorem difference_uses_either_side_for_other_children (π : IntervalComposition I)
    (J : BoundaryInterval n) (X₁ X₂ : IntervalArray n R)
    (h : ∀ K, ¬ (K.left ≤ J.left ∧ J.right ≤ K.right) → X₁ K = X₂ K)
    (k : Fin π.parts) (hk : (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right) :
    (∏ l : Fin π.parts, X₂ (π.part l)) - (∏ l : Fin π.parts, X₁ (π.part l)) =
      (X₂ (π.part k) - X₁ (π.part k)) * ∏ l ∈ Finset.univ.erase k, X₂ (π.part l) := by
  classical
  rw [π.child_product_difference J X₁ X₂ h k hk]
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  exact h _ (π.other_part_excludes J k hk l (Finset.mem_erase.mp hl).1)

-- Zero unaffected factors force a zero response, with no division or nonzero premise.
theorem zero_unchanged_child_annihilates_difference (π : IntervalComposition I)
    (J : BoundaryInterval n) (X₁ X₂ : IntervalArray n R)
    (h : ∀ K, ¬ (K.left ≤ J.left ∧ J.right ≤ K.right) → X₁ K = X₂ K)
    (k : Fin π.parts) (hk : (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right)
    (l : Fin π.parts) (hl : l ≠ k) (hz : X₁ (π.part l) = 0) :
    (∏ j : Fin π.parts, X₂ (π.part j)) - (∏ j : Fin π.parts, X₁ (π.part j)) = 0 := by
  classical
  rw [π.child_product_difference J X₁ X₂ h k hk]
  have hp : (∏ j ∈ Finset.univ.erase k, X₁ (π.part j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩) hz
  rw [hp, mul_zero]

-- The product response applies to actual canonical inverse coordinates on any containing parent.
theorem actual_inverse_child_response [Invertible (2 : R)]
    (H₁ H₂ : TripleArray n R) (t : IncreasingBoundaryTriple n)
    (h : ∀ u, u ≠ t → H₁ u = H₂ u) (π : IntervalComposition I)
    (k : Fin π.parts) (hk : (π.part k).left ≤ t.lower ∧ t.upper ≤ (π.part k).right) :
    (∏ l : Fin π.parts, farOnlyCoordinates H₂ (π.part l)) -
      (∏ l : Fin π.parts, farOnlyCoordinates H₁ (π.part l)) =
        (farOnlyCoordinates H₂ (π.part k) - farOnlyCoordinates H₁ (π.part k)) *
          ∏ l ∈ Finset.univ.erase k, farOnlyCoordinates H₁ (π.part l) := by
  apply π.child_product_difference t.spanInterval (farOnlyCoordinates H₁) (farOnlyCoordinates H₂)
    (fun K hK => farOnlyCoordinates_unchanged_off_critical H₁ H₂ t h K hK) k hk

end
end CriticalContractionChildIndependentReview
