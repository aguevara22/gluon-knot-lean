namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The unique actual core child containing s receives the spanning multiplier. -/
theorem emptySpanning_distinguished_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) (spanningChild s I hI C hL hR hs)) =
      ((etaMinus + etaPlus) / 2) * b0 (spanningChild s I hI C hL hR hs) := by
  let K := spanningChild s I hI C hL hR hs
  have hb := spanningChild_bounds s I hI C hL hR hs
  have hl : old s K.left < A s := by
    rw [← old_self s]
    exact old_strictMono s hb.1
  have hr : B s < old s K.right := by
    have hk : s.val < K.right.val := hb.2
    change s.val + 1 < (old s K.right).val
    rw [old_val, if_neg (by omega)]
    omega
  rw [ordinaryLift_span s etaMinus etaPlus t b0 _ hl hr,
    collapse_sectionInterval s (startingOldEmbedding s) (collapse_old s)]

/-- Every other actual child lies strictly to one side and contributes its core value. -/
theorem emptySpanning_other_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ)
    (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ spanningChild s I hI C hL hR hs) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) = b0 K := by
  have hplain : ¬ intervalContainsBoth s
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) := by
    rcases spanningChild_other s I hI C hL hR hs K hK hne with hr | hl
    · have ha : old s K.right < A s := by
        rw [← old_self s]
        exact old_strictMono s hr
      exact fun h => (not_le_of_gt (lt_trans ha (A_lt_B s))) h.2
    · have ha : A s < old s K.left := by
        rw [← old_self s]
        exact old_strictMono s hl
      exact fun h => (not_le_of_gt ha) h.1
  rw [ordinaryLift_plain s etaMinus etaPlus t b0 _ hplain,
    collapse_sectionInterval s (startingOldEmbedding s) (collapse_old s)]

/-- Reindex the actual full child product and isolate one multiplier without division. -/
theorem emptySpanning_child_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∏ J : {J : BoundaryInterval (n + 1) //
        (emptySpanningCutSet s I hI C hs).Consecutive J},
      ordinaryLift s etaMinus etaPlus t b0 J.val) =
      ((etaMinus + etaPlus) / 2) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := by
  let K0 : {K : BoundaryInterval n // C.Consecutive K} :=
    ⟨spanningChild s I hI C hL hR hs, spanningChild_consecutive s I hI C hL hR hs⟩
  let m : ℚ := (etaMinus + etaPlus) / 2
  calc
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        ordinaryLift s etaMinus etaPlus t b0
          (OrderedBoundaryTransport.interval (startingOldEmbedding s) K.val) :=
      (Fintype.prod_equiv (emptySpanningChildrenEquiv s I hI C hs) _ _ (fun _ => rfl)).symm
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        (if K = K0 then m else 1) * b0 K.val := by
      apply Finset.prod_congr rfl
      intro K hK
      by_cases he : K = K0
      · subst K
        rw [if_pos rfl]
        exact emptySpanning_distinguished_child_factor s I hI C hL hR hs etaMinus etaPlus t b0
      · rw [if_neg he, one_mul]
        exact emptySpanning_other_child_factor s I hI C hL hR hs etaMinus etaPlus t b0 K.val K.property
          (fun h => he (Subtype.ext h))
    _ = (∏ K : {K : BoundaryInterval n // C.Consecutive K}, if K = K0 then m else 1) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := Finset.prod_mul_distrib
    _ = _ := by simp [m]

/-- The unique no-cut presentation has its complete core summand multiplied by k. -/
theorem emptySpanning_summand (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (D0 H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (emptySpanningCutSet s I hI C hs).nearFarSummand
      (tripleLift s D0 t) (tripleLift s H0 u) (ordinaryLift s etaMinus etaPlus t b0) =
      ((etaMinus + etaPlus) / 2) * C.nearFarSummand D0 H0 b0 := by
  rw [nearFarSummand_eq_cutGateProduct,
    emptySpanning_gate_product s I hI C hs hL hR,
    emptySpanning_child_product s I hI C hL hR hs, nearFarSummand_eq_cutGateProduct]
  ring

/-- Sum over the actual singleton fiber, including a unary core composition. -/
theorem emptySpanning_weighted_fiber_sum (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (D0 H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∑ Q : CutFiber s I hI C, (expandCuts s I hI C Q).nearFarSummand
      (tripleLift s D0 t) (tripleLift s H0 u) (ordinaryLift s etaMinus etaPlus t b0)) =
      ((etaMinus + etaPlus) / 2) * C.nearFarSummand D0 H0 b0 := by
  rw [sum_emptyCutFiber s I hI C hs]
  exact emptySpanning_summand s I hI C hL hR hs D0 H0 etaMinus etaPlus t u b0

/-- Reversing the complete far array preserves the no-cut multiplier and ordinary children. -/
theorem emptySpanning_root_fiber_sum (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (D0 H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∑ Q : CutFiber s I hI C, (expandCuts s I hI C Q).nearFarSummand
      (tripleLift s D0 t) (-tripleLift s H0 u) (ordinaryLift s etaMinus etaPlus t b0)) =
      ((etaMinus + etaPlus) / 2) * C.nearFarSummand D0 (-H0) b0 := by
  rw [← tripleLift_neg]
  exact emptySpanning_weighted_fiber_sum s I hI C hL hR hs D0 (-H0) etaMinus etaPlus t (-u) b0

end
end SM.SoftDuplication
