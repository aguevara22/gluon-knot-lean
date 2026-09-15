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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftDuplicationAvoidingUnit.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

noncomputable section
variable {n : ℕ}

/-- Avoiding the consecutive pair means lying entirely on one of its two sides.
Both an interval ending at A and an interval starting at B are included. -/
theorem avoiding_interval_side_iff (s : Fin n) (I : BoundaryInterval (n + 1)) :
    (¬ (I.left ≤ A s ∧ B s ≤ I.right)) ↔ I.right ≤ A s ∨ B s ≤ I.left := by
  change (¬ (I.left.val ≤ s.val ∧ s.val + 1 ≤ I.right.val)) ↔
    I.right.val ≤ s.val ∨ s.val + 1 ≤ I.left.val
  have hi : I.left.val < I.right.val := I.increasing
  omega

/-- On an avoiding interval collapse subtracts the same amount from both
endpoints, so it preserves the actual number of leaves. -/
theorem collapseInterval_leaves_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) :
    (collapseInterval s I hI).leaves = I.leaves := by
  have hi : I.left.val < I.right.val := I.increasing
  change (collapse s I.right).val - (collapse s I.left).val = I.right.val - I.left.val
  rw [collapse_val, collapse_val]
  rcases (avoiding_interval_side_iff s I).mp havoid with hr | hl
  · have hrv : I.right.val ≤ s.val := hr
    have hlv : I.left.val ≤ s.val := by omega
    rw [if_pos hrv, if_pos hlv]
  · have hlv : s.val + 1 ≤ I.left.val := hl
    have hln : ¬ I.left.val ≤ s.val := by omega
    have hrn : ¬ I.right.val ≤ s.val := by omega
    rw [if_neg hrn, if_neg hln]
    omega

/-- The required unit coordinate survives the actual avoiding collapse. -/
theorem collapseInterval_unit_avoiding {R : Type*} [CommRing R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) :
    boundaryUnitArray (R := R) (collapseInterval s I hI) = boundaryUnitArray (R := R) I := by
  have hl := collapseInterval_leaves_avoiding s I hI havoid
  have hp : I.left.val < I.right.val := I.increasing
  have hc : (collapseInterval s I hI).left.val < (collapseInterval s I hI).right.val :=
    (collapseInterval s I hI).increasing
  unfold BoundaryInterval.leaves at hl
  have he : (collapseInterval s I hI).right.val = (collapseInterval s I hI).left.val + 1 ↔
      I.right.val = I.left.val + 1 := by omega
  simp only [boundaryUnitArray, he]

end
end SM.SoftDuplication
