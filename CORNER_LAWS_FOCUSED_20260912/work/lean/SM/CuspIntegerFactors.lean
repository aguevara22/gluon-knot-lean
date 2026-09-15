import SM.CuspRotation
import SM.CuspDefinition
import SM.GermTurnSigns
import SM.NamedWallPredicates
import SM.FusionIndices
import SM.DeletionG1
import SM.UnorderedWallTriples
import SM.RestrictedWordRoot
import SM.GermTurnSigns
import SM.EuclideanPlane
import Mathlib.Data.Sign.Basic
import SM.GermNeighborhood
import SM.CriticalSourceResponse
import SM.FiniteChiStability
import SM.BoundaryTripleSupports
import SM.CriticalContractionPositions
import SM.CriticalContractionBounds
import SM.ContractedGeometricWord
import SM.ContractedIntervals
import SM.ContractedCompositions
import SM.OffLeafContraction
import SM.UniqueChangingChild
import SM.ContractedChildResponse
import SM.NonunaryContraction
import SM.ContractionPropagation
import SM.ContractionOutput
import SM.CollinearGateSigns
import SM.BoundaryGateSigns
import SM.FarOnlyOutputLocality
import SM.BoundaryArrayStability
import SM.WallArrayNeighborhood
import SM.WallGapValues
import SM.BoundaryGapGates
import SM.GeometricGapResponse
import SM.ContractedGeometricArray
import SM.GeometricProperResponse
import SM.ProperSpanGermResponse
import SM.FullSpanGermResponse
import SM.CriticalAffineData
import SM.SignedCriticalJump
import SM.SingleTripleTreeResponse
import SM.RestrictedCriticalG1
import SM.IntegerCriticalGaps
import SM.IntegerSingleTripleResponse
import SM.UnorderedCriticalTriple
import SM.UnorderedIntegerSingleTripleResponse
import SM.FlatBoundaryPositions
import SM.FlatAffineSigns
import SM.IncidentFlatGapTuples
import SM.FlatIntegerFactors
import SM.FlatIncidentResponse
import SM.FlatIncidentAllSizes
import SM.FlatContractionArithmetic
import SM.TupleArityTransport
import SM.NonincidentFlatContraction
import SM.FlatNonincidentResponse
import SM.TurnResponseOrientation
import SM.FlatAllRootResponse
import SM.GermNearbyChirotope
import SM.FlatSourceResponse
import SM.CuspAffineSigns

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CuspIntegerFactors.body.lean (prototype CuspSourceResponse, kernel session 68098, receipt
CuspSourceResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The exact integer gap factors for the source cusp table, with the
left gap singleton and the right gap nonleaf. -/
theorem integer_wall_factor_left_leaf_pos_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : t.leftInterval.leaves = 1) (hR : 2 ≤ t.rightInterval.leaves) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = criticalIntervalIntegerOutput P g t hZ t.rightInterval t.rightInterval_excludes_span) := by
  have hl := critical_integer_leaf_values P g t hZ t.leftInterval t.leftInterval_excludes_span hL 1
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  constructor
  · rw [hl.2.1]
    simp [criticalGapUInteger, he, show (-1 : SignType) ≠ 1 by decide]
  · rw [hl.2.2]
    simp [criticalGapVInteger, he, show (-1 : SignType) ≠ 1 by decide]

/-- The exact integer gap factors for the source cusp table, with the
left gap singleton and the right gap nonleaf. -/
theorem integer_wall_factor_left_leaf_pos_neg (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : t.leftInterval.leaves = 1) (hR : 2 ≤ t.rightInterval.leaves) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span (-1) = criticalIntervalIntegerOutput P g t hZ t.rightInterval t.rightInterval_excludes_span) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span (-1) = 0) := by
  have hl := critical_integer_leaf_values P g t hZ t.leftInterval t.leftInterval_excludes_span hL 1
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  constructor
  · rw [hl.2.1]
    simp [criticalGapUInteger, he, show (-1 : SignType) ≠ 1 by decide]
  · rw [hl.2.2]
    simp [criticalGapVInteger, he, show (-1 : SignType) ≠ 1 by decide]

/-- The exact integer gap factors for the source cusp table, with the
right gap singleton and the left gap nonleaf. -/
theorem integer_wall_factor_right_leaf_neg_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : t.rightInterval.leaves = 1) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span (-1) *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = criticalIntervalIntegerOutput P g t hZ t.leftInterval t.leftInterval_excludes_span) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span (-1) *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0) := by
  have hl := critical_integer_leaf_values P g t hZ t.rightInterval t.rightInterval_excludes_span hR 1
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  constructor
  · rw [hl.2.1]
    simp [criticalGapUInteger, he, show (-1 : SignType) ≠ 1 by decide]
  · rw [hl.2.2]
    simp [criticalGapVInteger, he, show (-1 : SignType) ≠ 1 by decide]

/-- The exact integer gap factors for the source cusp table, with the
right gap singleton and the left gap nonleaf. -/
theorem integer_wall_factor_right_leaf_pos_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : t.rightInterval.leaves = 1) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = criticalIntervalIntegerOutput P g t hZ t.leftInterval t.leftInterval_excludes_span) := by
  have hl := critical_integer_leaf_values P g t hZ t.rightInterval t.rightInterval_excludes_span hR 1
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  constructor
  · rw [hl.2.1]
    simp [criticalGapUInteger, he, show (-1 : SignType) ≠ 1 by decide]
  · rw [hl.2.2]
    simp [criticalGapVInteger, he, show (-1 : SignType) ≠ 1 by decide]

end
end SM
