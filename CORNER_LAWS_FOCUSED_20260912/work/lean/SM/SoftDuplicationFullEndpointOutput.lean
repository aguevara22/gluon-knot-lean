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
import SM.SoftDuplicationSpanningTransform
import SM.SoftDuplicationStartingTransform
import SM.SoftDuplicationEndingChildren
import SM.SoftDuplicationEndingGatePositions
import SM.SoftDuplicationEndingGateProducts
import SM.SoftDuplicationEndingChildFactors
import SM.SoftDuplicationEndingTransform

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftDuplicationFullEndpointOutput.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

noncomputable section
variable {n : ℕ} [NeZero n]

/-- At the first position the actual full parent interval is a starting interval. -/
theorem full_start_bounds (hn : 3 ≤ n) (s : Fin n) (hs : s.val = 0) :
    (fullBoundaryInterval (by omega : 3 ≤ n + 1)).left = A s ∧
      B s < (fullBoundaryInterval (by omega : 3 ≤ n + 1)).right := by
  constructor
  · apply Fin.ext
    exact hs.symm
  · change s.val + 1 < n + 1 - 1
    omega

/-- At the last position the actual full parent interval is an ending interval. -/
theorem full_end_bounds (hn : 3 ≤ n) (s : Fin n) (hs : s.val = n - 1) :
    (fullBoundaryInterval (by omega : 3 ≤ n + 1)).left < A s ∧
      (fullBoundaryInterval (by omega : 3 ≤ n + 1)).right = B s := by
  constructor
  · change 0 < s.val
    omega
  · apply Fin.ext
    change n + 1 - 1 = s.val + 1
    omega

/-- The last endpoint of the core full word is the first vertex's cyclic predecessor. -/
theorem full_right_is_pred (hn : 3 ≤ n) (s : Fin n) (hs : s.val = 0) :
    (fullBoundaryInterval hn).right = cyclicPred s := by
  apply Fin.ext
  exact (cyclicPred_val_zero s hs).symm

/-- The first endpoint of the core full word is the last vertex's cyclic successor. -/
theorem full_left_is_succ (hn : 3 ≤ n) (s : Fin n) (hs : s.val = n - 1) :
    (fullBoundaryInterval hn).left = cyclicSucc s := by
  apply Fin.ext
  exact (cyclicSucc_val_last s hs).symm

/-- The complete auxiliary root transform has multiplier k at the first position.
This keeps arbitrary core arrays and b0; geometric identification remains separate. -/
theorem rootTransform_full_start (hn : 3 ≤ n) (s : Fin n) (hs : s.val = 0)
    (D0 H0 : TripleArray n ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    nearFarTransform (tripleLift s D0 t) (-tripleLift s H0 t)
      (ordinaryLift s (t (cyclicPred s)) (t (cyclicSucc s)) t b0)
      (fullBoundaryInterval (by omega : 3 ≤ n + 1)) =
      ((t (cyclicPred s) + t (cyclicSucc s)) / 2) *
        nearFarTransform D0 (-H0) b0 (fullBoundaryInterval hn) := by
  have hb := full_start_bounds hn s hs
  calc
    _ = ((t (cyclicSucc s) + t (fullBoundaryInterval hn).right) / 2) *
        nearFarTransform D0 (-H0) b0 (fullBoundaryInterval hn) := by
      simpa only [collapse_fullInterval hn s] using
        (rootTransform_starting s (fullBoundaryInterval (by omega : 3 ≤ n + 1))
          (fullInterval_not_duplicate hn s) hb.1 hb.2 D0 H0
          (t (cyclicPred s)) (t (cyclicSucc s)) t b0)
    _ = _ := by
      rw [full_right_is_pred hn s hs]
      ring

/-- The complete auxiliary root transform has the same multiplier k at the last position. -/
theorem rootTransform_full_end (hn : 3 ≤ n) (s : Fin n) (hs : s.val = n - 1)
    (D0 H0 : TripleArray n ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    nearFarTransform (tripleLift s D0 t) (-tripleLift s H0 t)
      (ordinaryLift s (t (cyclicPred s)) (t (cyclicSucc s)) t b0)
      (fullBoundaryInterval (by omega : 3 ≤ n + 1)) =
      ((t (cyclicPred s) + t (cyclicSucc s)) / 2) *
        nearFarTransform D0 (-H0) b0 (fullBoundaryInterval hn) := by
  have hb := full_end_bounds hn s hs
  calc
    _ = ((t (cyclicPred s) + t (fullBoundaryInterval hn).left) / 2) *
        nearFarTransform D0 (-H0) b0 (fullBoundaryInterval hn) := by
      simpa only [collapse_fullInterval hn s] using
        (rootTransform_ending s (fullBoundaryInterval (by omega : 3 ≤ n + 1))
          (fullInterval_not_duplicate hn s) hb.1 hb.2 D0 H0
          (t (cyclicPred s)) (t (cyclicSucc s)) t b0)
    _ = _ := by rw [full_left_is_succ hn s hs]

end
end SM.SoftDuplication
