namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The tail-mapped last core child receives the printed ending factor. -/
theorem ending_zero_last_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hR : I.right = B s) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) (endingLastChild s I hI C)) =
      ((etaMinus - t (endingLastChild s I hI C).left) / 2) *
        b0 (endingLastChild s I hI C) := by
  have h := ending_last_zero_endpoints s I hI C hR
  have hl := lt_of_eq_of_lt h.1 h.2.2
  rw [ordinaryLift_end s etaMinus etaPlus t b0 _ hl h.2.1]
  have hc : collapse s
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) (endingLastChild s I hI C)).left =
      (endingLastChild s I hI C).left := collapse_startingTail s _
  rw [hc, collapse_sectionInterval s (startingTailEmbedding s) (collapse_startingTail s)]

/-- Every other tail-mapped child ends strictly before B and is plain. -/
theorem ending_zero_other_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hR : I.right = B s) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ endingLastChild s I hI C) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) K) = b0 K := by
  have hs := ending_otherChild_right_lt s I hI C hR K hK hne
  have hb : startingTailEmbedding s K.right < B s := by
    rw [← startingTail_self s]
    exact (startingTailEmbedding s).strictMono hs
  have hplain : ¬ intervalContainsBoth s
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) K) :=
    fun h => (not_le_of_gt hb) h.2
  rw [ordinaryLift_plain s etaMinus etaPlus t b0 _ hplain,
    collapse_sectionInterval s (startingTailEmbedding s) (collapse_startingTail s)]

/-- Every old-mapped core child ends at or before A and is plain. -/
theorem ending_one_core_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hR : I.right = B s) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (K : BoundaryInterval n) (hK : C.Consecutive K) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) = b0 K := by
  have hs : K.right ≤ s := by
    simpa only [ending_core_right s I hI hR] using (C.bounds K.right hK.2.1).2
  have ha : old s K.right ≤ A s := by
    rw [← old_self s]
    exact (old_strictMono s).monotone hs
  have hb : old s K.right < B s := lt_of_le_of_lt ha (A_lt_B s)
  have hplain : ¬ intervalContainsBoth s
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) :=
    fun h => (not_le_of_gt hb) h.2
  rw [ordinaryLift_plain s etaMinus etaPlus t b0 _ hplain,
    collapse_sectionInterval s (startingOldEmbedding s) (collapse_old s)]

/-- The complete row-zero child product has exactly the actual last-child factor.
No core child value is divided out, so all zero and unary cases remain. -/
theorem ending_zero_child_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) (etaMinus etaPlus : ℚ)
    (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∏ J : {J : BoundaryInterval (n + 1) //
        (endingCutSet s I hI C hL hR 0).Consecutive J},
      ordinaryLift s etaMinus etaPlus t b0 J.val) =
      ((etaMinus - t (endingLastChild s I hI C).left) / 2) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := by
  let K0 : {K : BoundaryInterval n // C.Consecutive K} :=
    ⟨endingLastChild s I hI C, endingLastChild_consecutive s I hI C⟩
  let m : ℚ := (etaMinus - t (endingLastChild s I hI C).left) / 2
  calc
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        ordinaryLift s etaMinus etaPlus t b0
          (OrderedBoundaryTransport.interval (startingTailEmbedding s) K.val) :=
      (Fintype.prod_equiv (endingChildrenZeroEquiv s I hI C hL hR) _ _ (fun _ => rfl)).symm
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        (if K = K0 then m else 1) * b0 K.val := by
      apply Finset.prod_congr rfl
      intro K hK
      by_cases he : K = K0
      · subst K
        rw [if_pos rfl]
        exact ending_zero_last_child_factor s I hI C hR etaMinus etaPlus t b0
      · rw [if_neg he, one_mul]
        exact ending_zero_other_child_factor s I hI C hR etaMinus etaPlus t b0 K.val K.property
          (fun h => he (Subtype.ext h))
    _ = (∏ K : {K : BoundaryInterval n // C.Consecutive K}, if K = K0 then m else 1) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := Finset.prod_mul_distrib
    _ = _ := by simp [m]

/-- The complete row-one child product is the actual core product: the new
singleton contributes one and each old-mapped child contributes its core value. -/
theorem ending_one_child_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) (etaMinus etaPlus : ℚ)
    (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∏ J : {J : BoundaryInterval (n + 1) //
        (endingCutSet s I hI C hL hR 1).Consecutive J},
      ordinaryLift s etaMinus etaPlus t b0 J.val) =
      ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := by
  calc
    _ = ∏ x : Unit ⊕ {K : BoundaryInterval n // C.Consecutive K},
        ordinaryLift s etaMinus etaPlus t b0
          ((endingChildrenOneEquiv s I hI C hL hR) x).val :=
      (Fintype.prod_equiv (endingChildrenOneEquiv s I hI C hL hR) _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      change (∏ _u : Unit, ordinaryLift s etaMinus etaPlus t b0 (duplicateInterval s)) *
        (∏ K : {K : BoundaryInterval n // C.Consecutive K},
          ordinaryLift s etaMinus etaPlus t b0
            (OrderedBoundaryTransport.interval (startingOldEmbedding s) K.val)) = _
      simp only [ordinaryLift_duplicate, Finset.prod_const_one, one_mul]
      apply Finset.prod_congr rfl
      intro K hK
      exact ending_one_core_child_factor s I hI C hR etaMinus etaPlus t b0 K.val K.property

end
end SM.SoftDuplication
