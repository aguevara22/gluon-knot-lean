import SM.CriticalSourceResponse

namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- A positive-length interval belongs to at most one full child. This
also covers a contracted formal leaf without an interior vertex label. -/
theorem part_contains_unique (π : IntervalComposition I) (J : BoundaryInterval n)
    {k l : Fin π.parts}
    (hk : (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right)
    (hl : (π.part l).left ≤ J.left ∧ J.right ≤ (π.part l).right) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · exact ((not_le_of_gt J.increasing) (hk.2.trans ((π.part_order h).trans hl.1))).elim
  · exact h
  · exact ((not_le_of_gt J.increasing) (hl.2.trans ((π.part_order h).trans hk.1))).elim

theorem other_part_excludes (π : IntervalComposition I) (J : BoundaryInterval n)
    (k : Fin π.parts) (hk : (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right)
    (l : Fin π.parts) (hl : l ≠ k) :
    ¬ ((π.part l).left ≤ J.left ∧ J.right ≤ (π.part l).right) := by
  intro hc
  exact hl (π.part_contains_unique J hc hk)

variable {R : Type*} [CommRing R]

/-- If no child contains the critical span, every child inverse coordinate
is unchanged, hence so is the complete child product. -/
theorem child_product_unchanged (π : IntervalComposition I) (J : BoundaryInterval n)
    (X₁ X₂ : IntervalArray n R)
    (h : ∀ K, ¬ (K.left ≤ J.left ∧ J.right ≤ K.right) → X₁ K = X₂ K)
    (hπ : ∀ k : Fin π.parts, ¬ ((π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right)) :
    (∏ k : Fin π.parts, X₁ (π.part k)) = ∏ k : Fin π.parts, X₂ (π.part k) := by
  apply Finset.prod_congr rfl
  intro k _
  exact h _ (hπ k)

/-- Remove the unique potentially changing child from each full product.
Every remaining factor agrees; subtraction gives exactly one changed factor,
with no division and no product of two changes, including zero coordinates. -/
theorem child_product_difference (π : IntervalComposition I) (J : BoundaryInterval n)
    (X₁ X₂ : IntervalArray n R)
    (h : ∀ K, ¬ (K.left ≤ J.left ∧ J.right ≤ K.right) → X₁ K = X₂ K)
    (k : Fin π.parts) (hk : (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right) :
    (∏ l : Fin π.parts, X₂ (π.part l)) - (∏ l : Fin π.parts, X₁ (π.part l)) =
      (X₂ (π.part k) - X₁ (π.part k)) *
        ∏ l ∈ Finset.univ.erase k, X₁ (π.part l) := by
  classical
  have hp : (∏ l ∈ Finset.univ.erase k, X₂ (π.part l)) =
      ∏ l ∈ Finset.univ.erase k, X₁ (π.part l) := by
    apply Finset.prod_congr rfl
    intro l hl
    exact (h _ (π.other_part_excludes J k hk l (Finset.mem_erase.mp hl).1)).symm
  rw [← Finset.mul_prod_erase Finset.univ (fun l => X₂ (π.part l)) (Finset.mem_univ k)]
  rw [← Finset.mul_prod_erase Finset.univ (fun l => X₁ (π.part l)) (Finset.mem_univ k)]
  rw [hp]
  ring

end
end SM.IntervalComposition

#print axioms SM.IntervalComposition.part_contains_unique
#print axioms SM.IntervalComposition.other_part_excludes
#print axioms SM.IntervalComposition.child_product_unchanged
#print axioms SM.IntervalComposition.child_product_difference
