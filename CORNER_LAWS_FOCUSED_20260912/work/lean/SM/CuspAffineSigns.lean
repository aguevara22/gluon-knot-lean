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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CuspAffineSigns.body.lean (prototype CuspSourceResponse, kernel session 68098, receipt
CuspSourceResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section

/-- Incoming root, cut order M,B,A, with the cusp point beyond B. -/
theorem cusp_epsilons_incoming_gt_one (r : ℝ) (hr : 1 < r) :
    wallLeftEpsilon r 1 0 = 1 ∧ wallRightEpsilon r 1 0 = 1 := by
  constructor
  · apply sign_eq_one_iff.mpr
    change 0 < (1 - r) / (0 - r)
    exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · apply sign_eq_one_iff.mpr
    change 0 < (0 - 1) / (0 - r)
    exact div_pos_of_neg_of_neg (by norm_num) (by linarith)

/-- Incoming root, cut order M,B,A, with the cusp point before A. -/
theorem cusp_epsilons_incoming_lt_zero (r : ℝ) (hr : r < 0) :
    wallLeftEpsilon r 1 0 = 1 ∧ wallRightEpsilon r 1 0 = -1 := by
  constructor
  · apply sign_eq_one_iff.mpr
    change 0 < (1 - r) / (0 - r)
    exact div_pos (by linarith) (by linarith)
  · apply sign_eq_neg_one_iff.mpr
    change (0 - 1) / (0 - r) < 0
    exact div_neg_of_neg_of_pos (by norm_num) (by linarith)

/-- Outgoing root, cut order B,A,M, with the cusp point beyond B. -/
theorem cusp_epsilons_outgoing_gt_one (r : ℝ) (hr : 1 < r) :
    wallLeftEpsilon 1 0 r = -1 ∧ wallRightEpsilon 1 0 r = 1 := by
  constructor
  · apply sign_eq_neg_one_iff.mpr
    change (0 - 1) / (r - 1) < 0
    exact div_neg_of_neg_of_pos (by norm_num) (by linarith)
  · apply sign_eq_one_iff.mpr
    change 0 < (r - 0) / (r - 1)
    exact div_pos (by linarith) (by linarith)

/-- Outgoing root, cut order B,A,M, with the cusp point before A. -/
theorem cusp_epsilons_outgoing_lt_zero (r : ℝ) (hr : r < 0) :
    wallLeftEpsilon 1 0 r = 1 ∧ wallRightEpsilon 1 0 r = 1 := by
  constructor
  · apply sign_eq_one_iff.mpr
    change 0 < (0 - 1) / (r - 1)
    exact div_pos_of_neg_of_neg (by norm_num) (by linarith)
  · apply sign_eq_one_iff.mpr
    change 0 < (r - 0) / (r - 1)
    exact div_pos_of_neg_of_neg (by linarith) (by linarith)

variable {n : ℕ} [NeZero n]

/-- Construct the source line coordinates from the actual cusp predicate.
The direction is B-A and the scalar is obtained from the vanishing determinant.
The exterior clause excludes the entire closed parameter interval [0,1]. -/
theorem WallGerm.cusp_exterior_affine (w : WallGerm n) (j : ZMod n)
    (hc : w.CuspAt j) :
    ∃ r : ℝ, (r < 0 ∨ 1 < r) ∧
      w.center (j + 1) - w.center (j - 1) ≠ 0 ∧
      w.center (j - 1) = w.center (j - 1) +
        (0 : ℝ) • (w.center (j + 1) - w.center (j - 1)) ∧
      w.center j = w.center (j - 1) +
        r • (w.center (j + 1) - w.center (j - 1)) ∧
      w.center (j + 1) = w.center (j - 1) +
        (1 : ℝ) • (w.center (j + 1) - w.center (j - 1)) := by
  have hi := singlePointTriple_vertices_injective hc.1 hc.2.1
  have hAB : w.center (j - 1) ≠ w.center (j + 1) :=
    fun he => prev_ne_next (by have hn := hc.1; omega) j (hi he)
  have hω : w.center (j + 1) - w.center (j - 1) ≠ 0 :=
    sub_ne_zero.mpr hAB.symm
  have hz := singlePointTriple_turn_zero hc.2.1
  have hd : det (w.center j - w.center (j - 1))
      (w.center (j + 1) - w.center (j - 1)) = 0 := sign_eq_zero_iff.mp hz
  have hd' : det (w.center (j + 1) - w.center (j - 1))
      (w.center j - w.center (j - 1)) = 0 := by
    rw [det_swap, hd, neg_zero]
  let r := planeDot (w.center (j + 1) - w.center (j - 1))
      (w.center j - w.center (j - 1)) /
    planeDot (w.center (j + 1) - w.center (j - 1))
      (w.center (j + 1) - w.center (j - 1))
  have he : w.center j - w.center (j - 1) =
      r • (w.center (j + 1) - w.center (j - 1)) := scalar_of_det_zero hω hd'
  have hm : w.center j = w.center (j - 1) +
      r • (w.center (j + 1) - w.center (j - 1)) := by
    rw [← he]
    abel
  have hr : r < 0 ∨ 1 < r := by
    by_cases hr0 : r < 0
    · exact Or.inl hr0
    · right
      exact lt_of_not_ge (fun hr1 =>
        hc.2.2.2.1 ⟨r, le_of_not_gt hr0, hr1, hm⟩)
  refine ⟨r, hr, hω, ?_, hm, ?_⟩
  · simp
  · simp

end
end SM
