import SM.FiniteChiStability
import Mathlib.Topology.Order.LeftRightNhds
import SM.CrossingCriterion
import SM.ContinuousGeometry
import Mathlib.Topology.Instances.Sign
import Mathlib.Data.Fin.Tuple.Basic
import SM.SinglePointTriple
import SM.CriticalSourceResponse
import SM.InsertionIndices
import SM.RootBoundary
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.SuccPred
import SM.InteriorCutSet
import Mathlib.Data.Subtype
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import SM.NearFar
import SM.CompositionCutSet
import SM.ConsecutiveTriples
import SM.FarOnlyOutput
import SM.ConsecutiveCuts
import SM.InteriorCutIndex
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import SM.CompositionSegments
import SM.NearFarTriangular
import SM.SegmentStability
import SM.G1Consequences
import SM.GenericTopology
import SM.CyclicChambers
import SM.SoftDuplicationIndices
import SM.SoftDuplicationCutFibers
import SM.SoftDuplicationPresentations
import SM.OrderedBoundaryTransport
import SM.SoftDuplicationStartingChildren
import SM.SoftDuplicationArrays
import SM.SoftDuplicationSpanningCutPresentations
import SM.CutSetNearFar
import SM.CutSetNearFarNeighbors
import SM.SoftDuplicationSpanningCutNeighbors
import SM.SoftDuplicationStartingGatePositions
import SM.SoftDuplicationSpanningCutGatePositions
import SM.SoftDuplicationSectionTriples
import SM.SoftDuplicationStartingGateProducts

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftDuplicationSpanningCutGateProducts.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Actual zero row near/far values are the complete core entries. -/
theorem spanning_zero_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (D0 H0 : TripleArray n ℚ) (tD tH : Fin n → ℚ)
    (x : {x : Fin n // x ∈ C.interior.val}) :
    tripleLift s D0 tD ((spanningCutSet s I hI C hL hR hs 0).nearAtCut
      (spanningInteriorZeroEquiv s I hI C hL hR hs x)) = D0 (C.nearAtCut x) ∧
    tripleLift s H0 tH ((spanningCutSet s I hI C hL hR hs 0).farAtCut
      (spanningInteriorZeroEquiv s I hI C hL hR hs x)) = H0 (C.farAtCut x) := by
  constructor
  · rw [spanning_zero_nearTriple, tripleLift_startingOld]
  · rw [spanning_zero_farTriple, tripleLift_startingOld]

/-- Actual one row near/far values are the complete core entries. -/
theorem spanning_one_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (D0 H0 : TripleArray n ℚ) (tD tH : Fin n → ℚ)
    (x : {x : Fin n // x ∈ C.interior.val}) :
    tripleLift s D0 tD ((spanningCutSet s I hI C hL hR hs 1).nearAtCut
      (spanningInteriorOneEquiv s I hI C hL hR hs x)) = D0 (C.nearAtCut x) ∧
    tripleLift s H0 tH ((spanningCutSet s I hI C hL hR hs 1).farAtCut
      (spanningInteriorOneEquiv s I hI C hL hR hs x)) = H0 (C.farAtCut x) := by
  constructor
  · rw [spanning_one_nearTriple, tripleLift_startingTail]
  · rw [spanning_one_farTriple, tripleLift_startingTail]

/-- All inherited both-row gates have the actual core values, including A at core s. -/
theorem spanning_two_inherited_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (H0 : TripleArray n ℚ) (t u : Fin n → ℚ)
    (x : {x : Fin n // x ∈ C.interior.val}) :
    tripleLift s (coreNear s t) t ((spanningCutSet s I hI C hL hR hs 2).nearAtCut
      (spanningInteriorTwoEquiv s I hI C hL hR hs (Sum.inr x))) = coreNear s t (C.nearAtCut x) ∧
    tripleLift s H0 u ((spanningCutSet s I hI C hL hR hs 2).farAtCut
      (spanningInteriorTwoEquiv s I hI C hL hR hs (Sum.inr x))) = H0 (C.farAtCut x) := by
  constructor
  · by_cases hx : x.val = s
    · have he : x = spanningCoreCut s I hI C hL hR hs := Subtype.ext hx
      subst x
      have hp := spanning_two_A_near_positions s I hI C hL hR hs
      rw [tripleLift_upper s (coreNear s t) t _ ⟨hp.2.1, hp.2.2⟩,
        hp.1, collapse_old, spanning_coreNear_value]
    · rcases lt_or_gt_of_ne hx with hl | hr
      · rw [spanning_two_nearTriple_of_lt s I hI C hL hR hs x hl, tripleLift_startingOld]
      · rw [spanning_two_nearTriple_of_gt s I hI C hL hR hs x hr, tripleLift_startingTail]
  · rw [spanning_two_farTriple, tripleLift_startingOld]

/-- The additional B gate has near t(R) and the same actual core far value at s. -/
theorem spanning_two_new_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (D0 H0 : TripleArray n ℚ) (t u : Fin n → ℚ) :
    tripleLift s D0 t ((spanningCutSet s I hI C hL hR hs 2).nearAtCut
      (spanningInteriorTwoEquiv s I hI C hL hR hs (Sum.inl ()))) =
        t (spanningRightNeighbor s I hI C hL hR hs) ∧
    tripleLift s H0 u ((spanningCutSet s I hI C hL hR hs 2).farAtCut
      (spanningInteriorTwoEquiv s I hI C hL hR hs (Sum.inl ()))) =
        H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs)) := by
  have hp := spanning_two_B_near_positions s I hI C hL hR hs
  constructor
  · rw [tripleLift_lower s D0 t _ ⟨hp.1, hp.2.1⟩, hp.2.2, collapse_startingTail]
  · rw [spanning_two_B_farTriple, tripleLift_startingTail]

/-- The complete zero row gate product is exactly the core product, with no division. -/
theorem spanning_zero_gate_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (D0 H0 : TripleArray n ℚ) (tD tH : Fin n → ℚ) :
    cutGateProduct (spanningCutSet s I hI C hL hR hs 0)
      (tripleLift s D0 tD) (tripleLift s H0 tH) = cutGateProduct C D0 H0 := by
  unfold cutGateProduct
  symm
  apply Fintype.prod_equiv (spanningInteriorZeroEquiv s I hI C hL hR hs)
  intro x
  have h := spanning_zero_gate_values s I hI C hL hR hs D0 H0 tD tH x
  rw [h.1, h.2]

/-- The complete one row gate product is exactly the core product, with no division. -/
theorem spanning_one_gate_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (D0 H0 : TripleArray n ℚ) (tD tH : Fin n → ℚ) :
    cutGateProduct (spanningCutSet s I hI C hL hR hs 1)
      (tripleLift s D0 tD) (tripleLift s H0 tH) = cutGateProduct C D0 H0 := by
  unfold cutGateProduct
  symm
  apply Fintype.prod_equiv (spanningInteriorOneEquiv s I hI C hL hR hs)
  intro x
  have h := spanning_one_gate_values s I hI C hL hR hs D0 H0 tD tH x
  rw [h.1, h.2]

/-- The complete both-row gate product adds just the B gate to every core gate. -/
theorem spanning_two_gate_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (H0 : TripleArray n ℚ) (t u : Fin n → ℚ) :
    cutGateProduct (spanningCutSet s I hI C hL hR hs 2)
      (tripleLift s (coreNear s t) t) (tripleLift s H0 u) =
      ((t (spanningRightNeighbor s I hI C hL hR hs) -
        H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) / 2) *
        cutGateProduct C (coreNear s t) H0 := by
  calc
    _ = ∏ x : Unit ⊕ {x : Fin n // x ∈ C.interior.val},
        (tripleLift s (coreNear s t) t ((spanningCutSet s I hI C hL hR hs 2).nearAtCut
            (spanningInteriorTwoEquiv s I hI C hL hR hs x)) -
          tripleLift s H0 u ((spanningCutSet s I hI C hL hR hs 2).farAtCut
            (spanningInteriorTwoEquiv s I hI C hL hR hs x))) / 2 :=
      (Fintype.prod_equiv (spanningInteriorTwoEquiv s I hI C hL hR hs) _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      simp only [Fintype.prod_unique]
      have h := spanning_two_new_gate_values s I hI C hL hR hs (coreNear s t) H0 t u
      rw [h.1, h.2]
      congr 1
      apply Finset.prod_congr rfl
      intro x hx
      have h := spanning_two_inherited_gate_values s I hI C hL hR hs H0 t u x
      rw [h.1, h.2]

end
end SM.SoftDuplication
