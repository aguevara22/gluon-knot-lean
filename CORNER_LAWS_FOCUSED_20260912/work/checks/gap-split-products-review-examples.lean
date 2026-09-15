namespace GapSplitProductsIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n]

theorem every_raw_left_child_preserved (t : IncreasingBoundaryTriple n) (π : t.MiddleComposition)
    (j : Fin (t.gapCompositionEquiv π).1.parts) :
    ∃ r : Fin π.val.parts, π.val.part r = (t.gapCompositionEquiv π).1.part j := by
  have h := t.gapBaseComposition.exists_refined_child (t.gapRefinement π) (0 : Fin 2) j
  change ∃ r : Fin π.val.cutSet.toComposition.parts,
    π.val.cutSet.toComposition.part r = (t.gapCompositionEquiv π).1.part j at h
  rw [π.val.cutSet_toComposition] at h
  exact h

theorem every_raw_right_child_preserved (t : IncreasingBoundaryTriple n) (π : t.MiddleComposition)
    (j : Fin (t.gapCompositionEquiv π).2.parts) :
    ∃ r : Fin π.val.parts, π.val.part r = (t.gapCompositionEquiv π).2.part j := by
  have h := t.gapBaseComposition.exists_refined_child (t.gapRefinement π) (1 : Fin 2) j
  change ∃ r : Fin π.val.cutSet.toComposition.parts,
    π.val.cutSet.toComposition.part r = (t.gapCompositionEquiv π).2.part j at h
  rw [π.val.cutSet_toComposition] at h
  exact h

variable {R : Type*} [CommMonoid R]

theorem arbitrary_raw_pair_child_product (t : IncreasingBoundaryTriple n)
    (L : IntervalComposition t.leftInterval) (Q : IntervalComposition t.rightInterval)
    (X : BoundaryInterval n → R) :
    (∏ k : Fin (t.gapCompositionEquiv.symm (L,Q)).val.parts,
      X ((t.gapCompositionEquiv.symm (L,Q)).val.part k)) =
      (∏ k : Fin L.parts, X (L.part k)) * ∏ k : Fin Q.parts, X (Q.part k) := by
  have h := t.gapComposition_child_product (t.gapCompositionEquiv.symm (L,Q)) X
  rw [t.gapCompositionEquiv.apply_symm_apply] at h
  exact h

theorem unary_left_keeps_actual_gap_coordinate (t : IncreasingBoundaryTriple n)
    (Q : IntervalComposition t.rightInterval) (X : BoundaryInterval n → R) :
    (∏ k : Fin (t.gapCompositionEquiv.symm (IntervalComposition.single t.leftInterval,Q)).val.parts,
      X ((t.gapCompositionEquiv.symm (IntervalComposition.single t.leftInterval,Q)).val.part k)) =
      X t.leftInterval * ∏ k : Fin Q.parts, X (Q.part k) := by
  rw [arbitrary_raw_pair_child_product, IntervalComposition.single_product]

theorem unary_right_keeps_actual_gap_coordinate (t : IncreasingBoundaryTriple n)
    (L : IntervalComposition t.leftInterval) (X : BoundaryInterval n → R) :
    (∏ k : Fin (t.gapCompositionEquiv.symm (L,IntervalComposition.single t.rightInterval)).val.parts,
      X ((t.gapCompositionEquiv.symm (L,IntervalComposition.single t.rightInterval)).val.part k)) =
      (∏ k : Fin L.parts, X (L.part k)) * X t.rightInterval := by
  rw [arbitrary_raw_pair_child_product, IntervalComposition.single_product]

theorem erased_product_ignores_omitted_value (t : IncreasingBoundaryTriple n) (π : t.MiddleComposition)
    (f g : Fin n → R) (h : ∀ x, x ≠ t.middle → f x = g x) :
    (∏ x ∈ π.val.cutSet.interior.val.erase t.middle, f x) =
      ∏ x ∈ π.val.cutSet.interior.val.erase t.middle, g x := by
  classical
  apply Finset.prod_congr rfl
  intro x hx
  exact h x (Finset.mem_erase.mp hx).1

theorem two_unary_gaps_leave_empty_gate_product (t : IncreasingBoundaryTriple n)
    (π : t.MiddleComposition) (hL : (t.gapCompositionEquiv π).1.parts = 1)
    (hR : (t.gapCompositionEquiv π).2.parts = 1)
    (k : Fin (π.val.parts - 1)) (hk : π.val.interiorPosition k = t.middle) (f : Fin n → R) :
    (∏ j ∈ Finset.univ.erase k, f (π.val.interiorPosition j)) = 1 := by
  letI : IsEmpty (Fin ((t.gapCompositionEquiv π).1.parts - 1)) :=
    ⟨fun j => by have := j.isLt; omega⟩
  letI : IsEmpty (Fin ((t.gapCompositionEquiv π).2.parts - 1)) :=
    ⟨fun j => by have := j.isLt; omega⟩
  rw [t.gapComposition_cut_product_without_middle π k hk]
  simp

end
end GapSplitProductsIndependentReview

namespace GapSplitProductsIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommSemiring R]

theorem zero_middle_annuls_full_sum (t : IncreasingBoundaryTriple n) (f : Fin n → R)
    (X : BoundaryInterval n → R) (hzero : f t.middle = 0) :
    (∑ π : t.MiddleComposition,
      (∏ k : Fin (π.val.parts - 1), f (π.val.interiorPosition k)) *
        ∏ k : Fin π.val.parts, X (π.val.part k)) = 0 := by
  rw [t.middle_weighted_composition_sum, hzero, zero_mul]

theorem erased_sum_keeps_gap_products_when_middle_zero (t : IncreasingBoundaryTriple n)
    (f : Fin n → R) (X : BoundaryInterval n → R) (_hzero : f t.middle = 0) :
    (∑ π : t.MiddleComposition,
      (∏ x ∈ π.val.cutSet.interior.val.erase t.middle, f x) *
        ∏ k : Fin π.val.parts, X (π.val.part k)) =
      (∑ L : IntervalComposition t.leftInterval,
        (∏ k : Fin (L.parts - 1), f (L.interiorPosition k)) * ∏ k : Fin L.parts, X (L.part k)) *
      (∑ Q : IntervalComposition t.rightInterval,
        (∏ k : Fin (Q.parts - 1), f (Q.interiorPosition k)) * ∏ k : Fin Q.parts, X (Q.part k)) :=
  t.middle_erased_weighted_composition_sum f X

theorem erased_sum_ignores_any_middle_change (t : IncreasingBoundaryTriple n)
    (f g : Fin n → R) (h : ∀ x, x ≠ t.middle → f x = g x) (X : BoundaryInterval n → R) :
    (∑ π : t.MiddleComposition,
      (∏ x ∈ π.val.cutSet.interior.val.erase t.middle, f x) * ∏ k : Fin π.val.parts, X (π.val.part k)) =
    (∑ π : t.MiddleComposition,
      (∏ x ∈ π.val.cutSet.interior.val.erase t.middle, g x) * ∏ k : Fin π.val.parts, X (π.val.part k)) := by
  classical
  apply Finset.sum_congr rfl
  intro π _
  rw [erased_product_ignores_omitted_value t π f g h]

end
end GapSplitProductsIndependentReview
