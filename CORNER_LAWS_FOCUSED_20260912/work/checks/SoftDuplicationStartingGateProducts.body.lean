namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The complete product over actual interior cuts, with rational gate entries. -/
def cutGateProduct {m : ℕ} [NeZero m] {I : BoundaryInterval m}
    (C : BoundaryCutSet I) (D H : TripleArray m ℚ) : ℚ :=
  ∏ x : {x : Fin m // x ∈ C.interior.val},
    (D (C.nearAtCut x) - H (C.farAtCut x)) / 2

/-- Separate the complete actual gate and child products without cancelling either. -/
theorem nearFarSummand_eq_cutGateProduct {m : ℕ} [NeZero m] {I : BoundaryInterval m}
    (C : BoundaryCutSet I) (D H : TripleArray m ℚ) (b : IntervalArray m ℚ) :
    C.nearFarSummand D H b = cutGateProduct C D H *
      ∏ K : {K : BoundaryInterval m // C.Consecutive K}, b K.val := by
  simp only [BoundaryCutSet.nearFarSummand, cutGateProduct, div_eq_mul_inv, invOf_eq_inv]

variable {n : ℕ} [NeZero n]

/-- Row zero's actual near and far gates evaluate to their core entries. -/
theorem starting_zero_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) (x : {x : Fin n // x ∈ C.interior.val}) :
    tripleLift s D0 tD ((startingCutSet s I hI C hL hR 0).nearAtCut
      (startingInteriorZeroEquiv s I hI C hL hR x)) = D0 (C.nearAtCut x) ∧
    tripleLift s H0 tH ((startingCutSet s I hI C hL hR 0).farAtCut
      (startingInteriorZeroEquiv s I hI C hL hR x)) = H0 (C.farAtCut x) := by
  constructor
  · rw [starting_zero_nearTriple, tripleLift_startingOld]
  · rw [starting_zero_farTriple, tripleLift_startingOld]

/-- Row one's inherited near triple is a tail image, while its far triple is
an old image. Both are evaluated at their actual core triples. -/
theorem starting_one_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) (x : {x : Fin n // x ∈ C.interior.val}) :
    tripleLift s D0 tD ((startingCutSet s I hI C hL hR 1).nearAtCut
      (startingInteriorOneEquiv s I hI C hL hR (Sum.inr x))) = D0 (C.nearAtCut x) ∧
    tripleLift s H0 tH ((startingCutSet s I hI C hL hR 1).farAtCut
      (startingInteriorOneEquiv s I hI C hL hR (Sum.inr x))) = H0 (C.farAtCut x) := by
  constructor
  · rw [starting_one_nearTriple, tripleLift_startingTail]
  · rw [starting_one_farTriple, tripleLift_startingOld]

/-- The additional B gate has exactly the first-child near argument and full
interval far argument, including a unary core composition. -/
theorem starting_new_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) :
    tripleLift s D0 tD ((startingCutSet s I hI C hL hR 1).nearAtCut
      (startingInteriorOneEquiv s I hI C hL hR (Sum.inl ()))) =
        tD (startingFirstChild s I hI C).right ∧
    tripleLift s H0 tH ((startingCutSet s I hI C hL hR 1).farAtCut
      (startingInteriorOneEquiv s I hI C hL hR (Sum.inl ()))) =
        tH (collapseInterval s I hI).right := by
  have hn := starting_new_near_positions s I hI C hL hR
  have hf := starting_new_far_positions s I hI C hL hR
  constructor
  · rw [tripleLift_lower s D0 tD _ ⟨hn.1, hn.2.1⟩, hn.2.2, collapse_old]
  · rw [tripleLift_lower s H0 tH _ ⟨hf.1, hf.2.1⟩, hf.2.2]
    rfl

/-- The complete row-zero gate product is the actual core gate product. -/
theorem starting_zero_gate_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) :
    cutGateProduct (startingCutSet s I hI C hL hR 0)
      (tripleLift s D0 tD) (tripleLift s H0 tH) = cutGateProduct C D0 H0 := by
  unfold cutGateProduct
  symm
  apply Fintype.prod_equiv (startingInteriorZeroEquiv s I hI C hL hR)
  intro x
  have h := starting_zero_gate_values s I hI C hL hR D0 H0 tD tH x
  rw [h.1, h.2]

/-- The complete row-one gate product includes exactly its additional B gate.
The core interior product may be empty and any gate may be zero. -/
theorem starting_one_gate_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) :
    cutGateProduct (startingCutSet s I hI C hL hR 1)
      (tripleLift s D0 tD) (tripleLift s H0 tH) =
      ((tD (startingFirstChild s I hI C).right - tH (collapseInterval s I hI).right) / 2) *
        cutGateProduct C D0 H0 := by
  calc
    _ = ∏ x : Unit ⊕ {x : Fin n // x ∈ C.interior.val},
        (tripleLift s D0 tD ((startingCutSet s I hI C hL hR 1).nearAtCut
            (startingInteriorOneEquiv s I hI C hL hR x)) -
          tripleLift s H0 tH ((startingCutSet s I hI C hL hR 1).farAtCut
            (startingInteriorOneEquiv s I hI C hL hR x))) / 2 :=
      (Fintype.prod_equiv (startingInteriorOneEquiv s I hI C hL hR) _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      simp only [Fintype.prod_unique]
      have h := starting_new_gate_values s I hI C hL hR D0 H0 tD tH
      rw [h.1, h.2]
      congr 1
      apply Finset.prod_congr rfl
      intro x hx
      have h := starting_one_gate_values s I hI C hL hR D0 H0 tD tH x
      rw [h.1, h.2]

end
end SM.SoftDuplication
