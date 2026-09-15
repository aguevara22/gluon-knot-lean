import SM.TreeChamber
import SM.ContactHalfTuples
import SM.FusionIndices
import SM.NamedWallSides
import SM.UnorderedWallTriples
import Mathlib.Tactic
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
import SM.FlatBoundaryPositions
import SM.FlatContractionArithmetic
import SM.ContactBoundaryPositions
import SM.ContactRootPartition
import SM.ContactHalfRoots
import SM.ContactContractionLabels
import SM.FlatIntegerFactors
import SM.TupleArityTransport
import SM.ContactGapTuples
import SM.ContactGapWords
import SM.ContactIntegerFactors
import SM.ContactContractionCoefficients
import SM.CuspIntegerFactors
import SM.ContactAffineSigns
import SM.ContactSignedResponse
import SM.ContactSourceResponse

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SilentIntegerFactors.body.lean (prototype TripleSilentTreeLaws, kernel session 2126, receipt
TripleSilentTreeLaws-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem integer_U_product_zero_of_left_nonleaf_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (εR : SignType) :
    criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span εR = 0 := by
  have hE := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  simp only [criticalGapUInteger, ite_true, hE, zero_mul]

theorem integer_U_product_zero_of_right_nonleaf_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hR : 2 ≤ t.rightInterval.leaves) (εL : SignType) :
    criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span εL *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0 := by
  have hE := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  simp only [criticalGapUInteger, ite_true, hE, mul_zero]

/-- With two nonleaf gaps, one positive epsilon suffices to annihilate the
proper-span source product, whatever the other allowed sign is. -/
theorem integer_U_product_zero_of_nonleaves_one_positive (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : 2 ≤ t.rightInterval.leaves)
    (εL εR : SignType) (hε : εL = 1 ∨ εR = 1) :
    criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span εL *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span εR = 0 := by
  rcases hε with rfl | rfl
  · exact integer_U_product_zero_of_left_nonleaf_pos P g t hZ hL εR
  · exact integer_U_product_zero_of_right_nonleaf_pos P g t hZ hR εL

/-- Opposite epsilons on two nonleaf gaps annihilate both products required
by the FULL-span response. No amplitude is canceled or assumed nonzero. -/
theorem integer_UV_products_zero_of_nonleaves_opposite (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : 2 ≤ t.rightInterval.leaves)
    (εL εR : SignType) (hε : (εL = 1 ∧ εR = -1) ∨ (εL = -1 ∧ εR = 1)) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span εL *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span εR = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span εL *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span εR = 0) := by
  have hEL := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  have hER := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  rcases hε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp [criticalGapUInteger, criticalGapVInteger, hEL, hER,
    show (-1 : SignType) ≠ 1 by decide]

end
end SM
