namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The complete row-zero summand has the actual first-child multiplier.
All inherited gate and child factors are retained, even if they vanish. -/
theorem starting_zero_summand (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (D0 H0 : TripleArray n ℚ)
    (etaMinus etaPlus : ℚ) (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (startingCutSet s I hI C hL hR 0).nearFarSummand
      (tripleLift s D0 t) (tripleLift s H0 u) (ordinaryLift s etaMinus etaPlus t b0) =
      ((etaPlus - t (startingFirstChild s I hI C).right) / 2) *
        C.nearFarSummand D0 H0 b0 := by
  rw [nearFarSummand_eq_cutGateProduct, starting_zero_gate_product,
    starting_zero_child_product, nearFarSummand_eq_cutGateProduct]
  ring

/-- The complete row-one summand has the additional B gate multiplier.
The new singleton child has already been proved to have value one. -/
theorem starting_one_summand (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (D0 H0 : TripleArray n ℚ)
    (etaMinus etaPlus : ℚ) (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (startingCutSet s I hI C hL hR 1).nearFarSummand
      (tripleLift s D0 t) (tripleLift s H0 u) (ordinaryLift s etaMinus etaPlus t b0) =
      ((t (startingFirstChild s I hI C).right - u (collapseInterval s I hI).right) / 2) *
        C.nearFarSummand D0 H0 b0 := by
  rw [nearFarSummand_eq_cutGateProduct, starting_one_gate_product,
    starting_one_child_product, nearFarSummand_eq_cutGateProduct]
  ring

/-- Sum both actual presentations. The first-boundary dependence cancels
using the same t in the near lift and child table; far data u remains arbitrary. -/
theorem starting_weighted_fiber_sum (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (D0 H0 : TripleArray n ℚ)
    (etaMinus etaPlus : ℚ) (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∑ Q : CutFiber s I hI C, (expandCuts s I hI C Q).nearFarSummand
      (tripleLift s D0 t) (tripleLift s H0 u) (ordinaryLift s etaMinus etaPlus t b0)) =
      ((etaPlus - u (collapseInterval s I hI).right) / 2) *
        C.nearFarSummand D0 H0 b0 := by
  rw [sum_startingRows s I hI C hL hR]
  change (startingCutSet s I hI C hL hR 0).nearFarSummand _ _ _ +
    (startingCutSet s I hI C hL hR 1).nearFarSummand _ _ _ = _
  rw [starting_zero_summand, starting_one_summand]
  ring

/-- The complete starting-interval transform, including every composition.
There is no supplied solution, weight transport, or nonvanishing hypothesis. -/
theorem nearFarTransform_starting (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left = A s) (hR : B s < I.right)
    (D0 H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    nearFarTransform (tripleLift s D0 t) (tripleLift s H0 u)
      (ordinaryLift s etaMinus etaPlus t b0) I =
      ((etaPlus - u (collapseInterval s I hI).right) / 2) *
        nearFarTransform D0 H0 b0 (collapseInterval s I hI) := by
  rw [nearFarTransform_eq_cutFiber_sum s I hI, nearFarTransform_eq_cutSet_sum]
  calc
    _ = ∑ C : BoundaryCutSet (collapseInterval s I hI),
        ((etaPlus - u (collapseInterval s I hI).right) / 2) *
          C.nearFarSummand D0 H0 b0 := by
      apply Finset.sum_congr rfl
      intro C hC
      exact starting_weighted_fiber_sum s I hI C hL hR D0 H0 etaMinus etaPlus t u b0
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Reversing the whole far array gives the printed root starting multiplier.
This is the full starting-interval root transform, with arbitrary core b0. -/
theorem rootTransform_starting (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left = A s) (hR : B s < I.right)
    (D0 H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    nearFarTransform (tripleLift s D0 t) (-tripleLift s H0 t)
      (ordinaryLift s etaMinus etaPlus t b0) I =
      ((etaPlus + t (collapseInterval s I hI).right) / 2) *
        nearFarTransform D0 (-H0) b0 (collapseInterval s I hI) := by
  rw [← tripleLift_neg, nearFarTransform_starting s I hI hL hR]
  simp only [Pi.neg_apply, sub_neg_eq_add]

/-- The parent starting interval has at least two leaves, so its unit entry is zero. -/
theorem boundaryUnitArray_starting_zero (s : Fin n) (I : BoundaryInterval (n + 1))
    (hL : I.left = A s) (hR : B s < I.right) : boundaryUnitArray (R := ℚ) I = 0 := by
  have hl : I.left.val = s.val := congrArg Fin.val hL
  have hr : s.val + 1 < I.right.val := hR
  have hn : I.right.val ≠ I.left.val + 1 := by omega
  simp only [boundaryUnitArray, if_neg hn]

/-- Every actual starting ordinary coordinate is proved with the canonical
core inverse. One-leaf cores use the actual cyclic successor; larger cores
have a zero core unit entry. Unary compositions were included in the full sum. -/
theorem ordinaryLift_equation_starting (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left = A s) (hR : B s < I.right)
    (H0 : TripleArray n ℚ) (t : Fin n → ℚ) :
    nearFarTransform (parentNear s t) (tripleLift s H0 t)
      (ordinaryLift s (t (cyclicPred s)) (t (cyclicSucc s)) t
        (nearFarInverse (coreNear s t) H0 boundaryUnitArray)) I = boundaryUnitArray I := by
  change nearFarTransform (tripleLift s (coreNear s t) t) (tripleLift s H0 t) _ I = _
  rw [nearFarTransform_starting s I hI hL hR, nearFarTransform_inverse,
    boundaryUnitArray_starting_zero s I hL hR]
  by_cases hu : (collapseInterval s I hI).leaves = 1
  · have he := start_unit_endpoint s I hL hR hu
    change collapse s I.right = cyclicSucc s at he
    change ((t (cyclicSucc s) - t (collapse s I.right)) / 2) * _ = 0
    rw [he]
    simp
  · have hj := (collapseInterval s I hI).increasing
    have hn : (collapseInterval s I hI).right.val ≠
        (collapseInterval s I hI).left.val + 1 := by
      intro he
      apply hu
      change (collapseInterval s I hI).right.val -
        (collapseInterval s I hI).left.val = 1
      omega
    simp only [boundaryUnitArray, if_neg hn, mul_zero]

end
end SM.SoftDuplication
