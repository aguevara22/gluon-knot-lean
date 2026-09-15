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
import SM.SoftDuplicationSpanningCutGateProducts
import SM.SoftDuplicationStartingChildFactors
import SM.SoftDuplicationSpanningOneCutChildFactors
import SM.SoftDuplicationSpanningBothChildren
import SM.SoftDuplicationSpanningBothChildFactors
import SM.SoftDuplicationSpanningCoreCancellation
import SM.SoftDuplicationSpanningEmptyChildren
import SM.SoftDuplicationSpanningEmptyGates
import SM.SoftDuplicationAvoiding
import SM.SoftDuplicationAvoidingCompositions
import SM.SoftDuplicationAvoidingUnit
import SM.SoftDuplicationAvoidingTransform
import SM.SoftDuplicationSpanningEmptyWeights
import SM.SoftDuplicationTransformSetup
import SM.BoundaryTripleSupports
import SM.CanonicalTripleSigns
import SM.SoftInsertionIndices
import SM.SoftInsertionSuccessors
import SM.SoftInsertionTuple
import SM.SoftLocalDeterminants
import SM.SoftFamilyG1
import SM.SoftAttachmentSigns
import SM.SoftFarSignFamily
import SM.SoftParentEdges
import SM.SoftRootBoundary
import SM.SoftDuplicationScalars
import SM.SoftGeometricDuplication
import SM.SoftDuplicationNeighbors

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftDuplicationSpanningTransform.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The A-only row retains all core gates and receives the actual right-child multiplier. -/
theorem spanning_zero_summand (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (D0 H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (spanningCutSet s I hI C hL hR hs 0).nearFarSummand
      (tripleLift s D0 t) (tripleLift s H0 u) (ordinaryLift s etaMinus etaPlus t b0) =
      ((etaPlus - t (spanningRightNeighbor s I hI C hL hR hs)) / 2) *
        C.nearFarSummand D0 H0 b0 := by
  rw [nearFarSummand_eq_cutGateProduct, spanning_zero_gate_product,
    spanning_zero_child_product, nearFarSummand_eq_cutGateProduct]
  ring

/-- The B-only row retains all core gates and receives the actual left-child multiplier. -/
theorem spanning_one_summand (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (D0 H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (spanningCutSet s I hI C hL hR hs 1).nearFarSummand
      (tripleLift s D0 t) (tripleLift s H0 u) (ordinaryLift s etaMinus etaPlus t b0) =
      ((etaMinus - t (spanningLeftNeighbor s I hI C hL hR hs)) / 2) *
        C.nearFarSummand D0 H0 b0 := by
  rw [nearFarSummand_eq_cutGateProduct, spanning_one_gate_product,
    spanning_one_child_product, nearFarSummand_eq_cutGateProduct]
  ring

/-- The both-cut row contributes exactly the new B gate; its singleton child has value one. -/
theorem spanning_two_summand (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (spanningCutSet s I hI C hL hR hs 2).nearFarSummand
      (tripleLift s (coreNear s t) t) (tripleLift s H0 u)
      (ordinaryLift s etaMinus etaPlus t b0) =
      ((t (spanningRightNeighbor s I hI C hL hR hs) -
        H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) / 2) *
        C.nearFarSummand (coreNear s t) H0 b0 := by
  rw [nearFarSummand_eq_cutGateProduct, spanning_two_gate_product,
    spanning_two_child_product, nearFarSummand_eq_cutGateProduct]
  ring

/-- Sum the complete actual three-row fiber. Its residual is a scalar times the
complete core summand, and the local square relation kills it with every exterior retained. -/
theorem spanning_cut_weighted_fiber_sum (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ)
    (hsq : (H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) ^ 2 =
      (t (spanningLeftNeighbor s I hI C hL hR hs)) ^ 2) :
    (∑ Q : CutFiber s I hI C, (expandCuts s I hI C Q).nearFarSummand
      (tripleLift s (coreNear s t) t) (tripleLift s H0 u)
      (ordinaryLift s etaMinus etaPlus t b0)) =
      ((etaMinus + etaPlus) / 2) * C.nearFarSummand (coreNear s t) H0 b0 := by
  rw [sum_spanningRows s I hI C hL hR hs]
  change (spanningCutSet s I hI C hL hR hs 0).nearFarSummand _ _ _ +
    (spanningCutSet s I hI C hL hR hs 1).nearFarSummand _ _ _ +
    (spanningCutSet s I hI C hL hR hs 2).nearFarSummand _ _ _ = _
  rw [spanning_zero_summand, spanning_one_summand, spanning_two_summand]
  calc
    _ = ((etaMinus + etaPlus) / 2) * C.nearFarSummand (coreNear s t) H0 b0 -
        ((t (spanningLeftNeighbor s I hI C hL hR hs) +
          H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) / 2) *
          C.nearFarSummand (coreNear s t) H0 b0 := by ring
    _ = _ := by
      rw [spanning_core_summand_cancellation s I hI C hL hR hs H0 t b0 hsq, sub_zero]

/-- Every actual collapsed composition is included, whether or not it cuts at s.
Only off-s sign squares are used; the no-cut branch includes unary compositions. -/
theorem spanning_weighted_fiber_sum (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right)
    (H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ)
    (hH : ∀ T, (H0 T) ^ 2 = 1) (ht : ∀ k, k ≠ s → (t k) ^ 2 = 1) :
    (∑ Q : CutFiber s I hI C, (expandCuts s I hI C Q).nearFarSummand
      (tripleLift s (coreNear s t) t) (tripleLift s H0 u)
      (ordinaryLift s etaMinus etaPlus t b0)) =
      ((etaMinus + etaPlus) / 2) * C.nearFarSummand (coreNear s t) H0 b0 := by
  by_cases hs : s ∈ C.cuts
  · exact spanning_cut_weighted_fiber_sum s I hI C hL hR hs H0 etaMinus etaPlus t u b0
      (spanning_core_far_square_of_signs s I hI C hL hR hs H0 t hH ht)
  · exact emptySpanning_weighted_fiber_sum s I hI C hL hR hs
      (coreNear s t) H0 etaMinus etaPlus t u b0

/-- Sum all actual fibers to obtain the complete strictly spanning transform.
No supplied solution or nonzero factor hypothesis enters this identity. -/
theorem nearFarTransform_spanning (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left < A s) (hR : B s < I.right)
    (H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ)
    (hH : ∀ T, (H0 T) ^ 2 = 1) (ht : ∀ k, k ≠ s → (t k) ^ 2 = 1) :
    nearFarTransform (tripleLift s (coreNear s t) t) (tripleLift s H0 u)
      (ordinaryLift s etaMinus etaPlus t b0) I =
      ((etaMinus + etaPlus) / 2) *
        nearFarTransform (coreNear s t) H0 b0 (collapseInterval s I hI) := by
  rw [nearFarTransform_eq_cutFiber_sum s I hI, nearFarTransform_eq_cutSet_sum]
  calc
    _ = ∑ C : BoundaryCutSet (collapseInterval s I hI),
        ((etaMinus + etaPlus) / 2) * C.nearFarSummand (coreNear s t) H0 b0 := by
      apply Finset.sum_congr rfl
      intro C hC
      exact spanning_weighted_fiber_sum s I hI C hL hR H0 etaMinus etaPlus t u b0 hH ht
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Reverse the whole far array while retaining the same ordinary child array.
The far square condition survives negation, and the spanning multiplier remains k. -/
theorem rootTransform_spanning (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left < A s) (hR : B s < I.right)
    (H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ)
    (hH : ∀ T, (H0 T) ^ 2 = 1) (ht : ∀ k, k ≠ s → (t k) ^ 2 = 1) :
    nearFarTransform (tripleLift s (coreNear s t) t) (-tripleLift s H0 u)
      (ordinaryLift s etaMinus etaPlus t b0) I =
      ((etaMinus + etaPlus) / 2) *
        nearFarTransform (coreNear s t) (-H0) b0 (collapseInterval s I hI) := by
  rw [← tripleLift_neg s H0 u]
  apply nearFarTransform_spanning s I hI hL hR (-H0) etaMinus etaPlus t (-u) b0 ?_ ht
  intro T
  simpa only [Pi.neg_apply, neg_sq] using hH T

/-- A strictly spanning parent has more than one leaf, so its unit entry vanishes. -/
theorem boundaryUnitArray_spanning_zero (s : Fin n) (I : BoundaryInterval (n + 1))
    (hL : I.left < A s) (hR : B s < I.right) : boundaryUnitArray (R := ℚ) I = 0 := by
  have hl : I.left.val < s.val := hL
  have hr : s.val + 1 < I.right.val := hR
  have hn : I.right.val ≠ I.left.val + 1 := by omega
  simp only [boundaryUnitArray, if_neg hn]

/-- The actual collapsed spanning interval strictly contains s and also has a zero unit entry. -/
theorem boundaryUnitArray_core_spanning_zero (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left < A s) (hR : B s < I.right) :
    boundaryUnitArray (R := ℚ) (collapseInterval s I hI) = 0 := by
  have hb := span_collapsed_bounds s I hL hR
  have hl : (collapseInterval s I hI).left.val < s.val := hb.1
  have hr : s.val < (collapseInterval s I hI).right.val := hb.2
  have hn : (collapseInterval s I hI).right.val ≠
      (collapseInterval s I hI).left.val + 1 := by omega
  simp only [boundaryUnitArray, if_neg hn]

/-- The proposed ordinary array satisfies the actual spanning coordinate with
canonical core inverse and the actual cyclic-neighbor eta values. -/
theorem ordinaryLift_equation_spanning (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left < A s) (hR : B s < I.right)
    (H0 : TripleArray n ℚ) (t : Fin n → ℚ)
    (hH : ∀ T, (H0 T) ^ 2 = 1) (ht : ∀ k, k ≠ s → (t k) ^ 2 = 1) :
    nearFarTransform (parentNear s t) (tripleLift s H0 t)
      (ordinaryLift s (t (cyclicPred s)) (t (cyclicSucc s)) t
        (nearFarInverse (coreNear s t) H0 boundaryUnitArray)) I = boundaryUnitArray I := by
  change nearFarTransform (tripleLift s (coreNear s t) t) (tripleLift s H0 t) _ I = _
  rw [nearFarTransform_spanning s I hI hL hR H0 (t (cyclicPred s)) (t (cyclicSucc s)) t t
      (nearFarInverse (coreNear s t) H0 boundaryUnitArray) hH ht,
    nearFarTransform_inverse, boundaryUnitArray_core_spanning_zero s I hI hL hR,
    boundaryUnitArray_spanning_zero s I hL hR, mul_zero]

end
end SM.SoftDuplication
