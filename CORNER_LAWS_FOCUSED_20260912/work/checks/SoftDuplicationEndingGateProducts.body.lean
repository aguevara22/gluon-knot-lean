namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Row zero's actual near and far gates evaluate to their core entries. -/
theorem ending_zero_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) (x : {x : Fin n // x ∈ C.interior.val}) :
    tripleLift s D0 tD ((endingCutSet s I hI C hL hR 0).nearAtCut
      (endingInteriorZeroEquiv s I hI C hL hR x)) = D0 (C.nearAtCut x) ∧
    tripleLift s H0 tH ((endingCutSet s I hI C hL hR 0).farAtCut
      (endingInteriorZeroEquiv s I hI C hL hR x)) = H0 (C.farAtCut x) := by
  constructor
  · rw [ending_zero_nearTriple, tripleLift_startingTail]
  · rw [ending_zero_farTriple, tripleLift_startingTail]

/-- Row one's inherited near triple is an old image, while its far triple is
a tail image. Both are evaluated at their actual core triples. -/
theorem ending_one_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) (x : {x : Fin n // x ∈ C.interior.val}) :
    tripleLift s D0 tD ((endingCutSet s I hI C hL hR 1).nearAtCut
      (endingInteriorOneEquiv s I hI C hL hR (Sum.inr x))) = D0 (C.nearAtCut x) ∧
    tripleLift s H0 tH ((endingCutSet s I hI C hL hR 1).farAtCut
      (endingInteriorOneEquiv s I hI C hL hR (Sum.inr x))) = H0 (C.farAtCut x) := by
  constructor
  · rw [ending_one_nearTriple, tripleLift_startingOld]
  · rw [ending_one_farTriple, tripleLift_startingTail]

/-- The additional A gate has exactly the last-child near argument and full
interval far argument, including a unary core composition. -/
theorem ending_new_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) :
    tripleLift s D0 tD ((endingCutSet s I hI C hL hR 1).nearAtCut
      (endingInteriorOneEquiv s I hI C hL hR (Sum.inl ()))) =
        tD (endingLastChild s I hI C).left ∧
    tripleLift s H0 tH ((endingCutSet s I hI C hL hR 1).farAtCut
      (endingInteriorOneEquiv s I hI C hL hR (Sum.inl ()))) =
        tH (collapseInterval s I hI).left := by
  have hn := ending_new_near_positions s I hI C hL hR
  have hf := ending_new_far_positions s I hI C hL hR
  constructor
  · rw [tripleLift_upper s D0 tD _ ⟨hn.2.1, hn.2.2⟩, hn.1, collapse_old]
  · rw [tripleLift_upper s H0 tH _ ⟨hf.2.1, hf.2.2⟩, hf.1]
    rfl

/-- The complete row-zero gate product is the actual core gate product. -/
theorem ending_zero_gate_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) :
    cutGateProduct (endingCutSet s I hI C hL hR 0)
      (tripleLift s D0 tD) (tripleLift s H0 tH) = cutGateProduct C D0 H0 := by
  unfold cutGateProduct
  symm
  apply Fintype.prod_equiv (endingInteriorZeroEquiv s I hI C hL hR)
  intro x
  have h := ending_zero_gate_values s I hI C hL hR D0 H0 tD tH x
  rw [h.1, h.2]

/-- The complete row-one gate product includes exactly its additional A gate.
The core interior product may be empty and any gate may be zero. -/
theorem ending_one_gate_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) :
    cutGateProduct (endingCutSet s I hI C hL hR 1)
      (tripleLift s D0 tD) (tripleLift s H0 tH) =
      ((tD (endingLastChild s I hI C).left - tH (collapseInterval s I hI).left) / 2) *
        cutGateProduct C D0 H0 := by
  calc
    _ = ∏ x : Unit ⊕ {x : Fin n // x ∈ C.interior.val},
        (tripleLift s D0 tD ((endingCutSet s I hI C hL hR 1).nearAtCut
            (endingInteriorOneEquiv s I hI C hL hR x)) -
          tripleLift s H0 tH ((endingCutSet s I hI C hL hR 1).farAtCut
            (endingInteriorOneEquiv s I hI C hL hR x))) / 2 :=
      (Fintype.prod_equiv (endingInteriorOneEquiv s I hI C hL hR) _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      simp only [Fintype.prod_unique]
      have h := ending_new_gate_values s I hI C hL hR D0 H0 tD tH
      rw [h.1, h.2]
      congr 1
      apply Finset.prod_congr rfl
      intro x hx
      have h := ending_one_gate_values s I hI C hL hR D0 H0 tD tH x
      rw [h.1, h.2]

end
end SM.SoftDuplication
