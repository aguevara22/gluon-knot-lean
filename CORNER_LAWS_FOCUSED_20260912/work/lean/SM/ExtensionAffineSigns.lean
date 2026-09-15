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
import SM.SilentIntegerFactors

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/ExtensionAffineSigns.body.lean (prototype TripleSilentTreeLaws, kernel session 2126, receipt
TripleSilentTreeLaws-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section

/-- For the base root the critical order is B,X,A. The two exterior ranges
give the two opposite epsilon pairs, with neither epsilon zero. -/
theorem extension_epsilons_base (r : ℝ) (hr : r < 0 ∨ 1 < r) :
    (wallLeftEpsilon 1 r 0 = 1 ∧ wallRightEpsilon 1 r 0 = -1) ∨
      (wallLeftEpsilon 1 r 0 = -1 ∧ wallRightEpsilon 1 r 0 = 1) := by
  rcases hr with hr | hr
  · left
    constructor
    · apply sign_eq_one_iff.mpr
      change 0 < (r - 1) / (0 - 1)
      exact div_pos_of_neg_of_neg (by linarith) (by norm_num)
    · apply sign_eq_neg_one_iff.mpr
      change (0 - r) / (0 - 1) < 0
      exact div_neg_of_pos_of_neg (by linarith) (by norm_num)
  · right
    constructor
    · apply sign_eq_neg_one_iff.mpr
      change (r - 1) / (0 - 1) < 0
      exact div_neg_of_pos_of_neg (by linarith) (by norm_num)
    · apply sign_eq_one_iff.mpr
      change 0 < (0 - r) / (0 - 1)
      exact div_pos_of_neg_of_neg (by linarith) (by norm_num)

/-- On the original X-to-A arc the cut order is A,B,X. The nonleaf right
gap has positive epsilon for either allowed exterior coordinate range. -/
theorem extension_right_epsilon_first_arc (r : ℝ) (hr : r < 0 ∨ 1 < r) :
    wallRightEpsilon 0 1 r = 1 := by
  apply sign_eq_one_iff.mpr
  change 0 < (r - 1) / (r - 0)
  rcases hr with hr | hr
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · exact div_pos (by linarith) (by linarith)

/-- On the original B-to-X arc the cut order is X,A,B. The nonleaf left
gap has positive epsilon for either allowed exterior coordinate range. -/
theorem extension_left_epsilon_second_arc (r : ℝ) (hr : r < 0 ∨ 1 < r) :
    wallLeftEpsilon r 0 1 = 1 := by
  apply sign_eq_one_iff.mpr
  change 0 < (0 - r) / (1 - r)
  rcases hr with hr | hr
  · exact div_pos (by linarith) (by linarith)
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)

variable {n : ℕ} [NeZero n]

/-- The actual extension line witness supplies the affine scalar. Closed
segment exclusion forces it outside [0,1], and central regularity supplies
the nonzero direction B-A. No interior-contact or cusp premise is used. -/
theorem WallGerm.extension_exterior_affine (w : WallGerm n) (M a : ZMod n)
    (hn : 3 ≤ n) (he : w.ExtensionAt M a) :
    ∃ r : ℝ, (r < 0 ∨ 1 < r) ∧
      w.center (a + 1) - w.center a ≠ 0 ∧
      w.center a = w.center a + (0 : ℝ) • (w.center (a + 1) - w.center a) ∧
      w.center (a + 1) = w.center a + (1 : ℝ) • (w.center (a + 1) - w.center a) ∧
      w.center M = w.center a + r • (w.center (a + 1) - w.center a) := by
  have hreg := w.extension_regular hn he
  have hω : edge w.center a ≠ 0 := (hreg a).2.1
  obtain ⟨r, hX⟩ := he.2.2.2.1
  have hr : r < 0 ∨ 1 < r := by
    by_cases hr0 : r < 0
    · exact Or.inl hr0
    · right
      exact lt_of_not_ge (fun hr1 =>
        he.2.2.2.2.1 ⟨r, le_of_not_gt hr0, hr1, hX⟩)
  refine ⟨r, hr, ?_, ?_, ?_, ?_⟩
  · simpa only [edge] using hω
  · simp
  · simp
  · simpa only [edgePoint, edge] using hX

end
end SM
