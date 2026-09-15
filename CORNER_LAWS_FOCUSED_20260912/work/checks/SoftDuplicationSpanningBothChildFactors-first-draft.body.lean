namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Every actual inherited child in the both-cut row is plain and collapses to its core child. -/
theorem spanning_two_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∈ C.cuts) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (K : BoundaryInterval n) (hK : C.Consecutive K) :
    ordinaryLift s etaMinus etaPlus t b0 (spanningBothChild s K) = b0 K := by
  rw [ordinaryLift_plain s etaMinus etaPlus t b0 _ (spanningBothChild_plain s I hI C hs K hK),
    spanningBothChild_collapse]

/-- The complete both-cut child product is the core product; its additional singleton has value1. -/
theorem spanning_two_child_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∏ J : {J : BoundaryInterval (n + 1) //
        (spanningCutSet s I hI C hL hR hs 2).Consecutive J},
      ordinaryLift s etaMinus etaPlus t b0 J.val) =
      ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := by
  calc
    _ = ∏ x : Unit ⊕ {K : BoundaryInterval n // C.Consecutive K},
        ordinaryLift s etaMinus etaPlus t b0
          ((spanningChildrenBothEquiv s I hI C hL hR hs) x).val :=
      (Fintype.prod_equiv (spanningChildrenBothEquiv s I hI C hL hR hs) _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      simp only [spanningChildrenBothEquiv_inl_val, spanningChildrenBothEquiv_inr_val,
        ordinaryLift_duplicate, Finset.prod_const_one, one_mul]
      apply Finset.prod_congr rfl
      intro K hK
      exact spanning_two_child_factor s I hI C hs etaMinus etaPlus t b0 K.val K.property

end
end SM.SoftDuplication
