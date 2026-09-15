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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/TurnResponseOrientation.body.lean (prototype FlatSourceResponse, kernel session 25627, receipt
FlatSourceResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.WallGerm

noncomputable section
variable {n : ℕ}

/-- Actual punctured parameters with right/left turn signs occupy opposite
time sides. The proof uses the existing connected generic-side constancy,
not any convention identifying positive time with the source right side. -/
theorem turn_right_left_opposite_time_sides (w : WallGerm n) (j : ZMod n)
    (sRight sLeft : w.Parameter)
    (hRight0 : sRight.val ≠ 0) (hLeft0 : sLeft.val ≠ 0)
    (hRight : turn (w.curve sRight) j = -1)
    (hLeft : turn (w.curve sLeft) j = 1) :
    (sLeft.val < 0 ∧ 0 < sRight.val) ∨
      (sRight.val < 0 ∧ 0 < sLeft.val) := by
  obtain ⟨b, r, hr⟩ := w.sideTime_surjective_punctured sRight hRight0
  obtain ⟨c, l, hl⟩ := w.sideTime_surjective_punctured sLeft hLeft0
  have hbc : b ≠ c := by
    intro heq
    subst c
    have he : turn (w.curve (w.sideTime b r)) j =
        turn (w.curve (w.sideTime b l)) j :=
      w.side_turn_constant b r l j
    rw [hr, hl, hRight, hLeft] at he
    norm_num at he
  cases b <;> cases c
  · exact (hbc rfl).elim
  · right
    constructor
    · rw [← hr]
      change -r.val < 0
      linarith [r.property.1]
    · rw [← hl]
      change 0 < l.val
      exact l.property.1
  · left
    constructor
    · rw [← hl]
      change -l.val < 0
      linarith [l.property.1]
    · rw [← hr]
      change 0 < r.val
      exact r.property.1
  · exact (hbc rfl).elim

/-- Orient a fixed signed integer response by the source's actual turn
convention: right has turn -1 and left has turn +1. The signed response
and the conclusion cover independent parameters in the same positive
radius. F is arbitrary; no chamber constancy of F is assumed. -/
theorem turn_response_right_minus_left (w : WallGerm n) (j : ZMod n)
    (F : w.Parameter → ℤ) (C d : ℤ) (δ : ℝ)
    (hd : d = -1 ∨ d = 1) (hδ : 0 < δ) (hδr : δ ≤ w.radius)
    (hresponse :
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
          (F sPlus - F sMinus = d * C))
    (sRight sLeft : w.Parameter)
    (hRight0 : sRight.val ≠ 0) (hLeft0 : sLeft.val ≠ 0)
    (hRight : turn (w.curve sRight) j = -1)
    (hLeft : turn (w.curve sLeft) j = 1)
    (hRightNear : |sRight.val| < δ) (hLeftNear : |sLeft.val| < δ) :
    F sRight - F sLeft = C := by
  rcases w.turn_right_left_opposite_time_sides j sRight sLeft
      hRight0 hLeft0 hRight hLeft with ⟨hMinus, hPlus⟩ | ⟨hMinus, hPlus⟩
  · have h := hresponse sLeft sRight hMinus hPlus hLeftNear hRightNear
    have hj := h.1
    rw [hRight, hLeft] at hj
    have hdpos : d = 1 := by
      norm_num at hj
      omega
    simpa only [hdpos, one_mul] using h.2
  · have h := hresponse sRight sLeft hMinus hPlus hRightNear hLeftNear
    have hj := h.1
    rw [hLeft, hRight] at hj
    have hdneg : d = -1 := by
      norm_num at hj
      omega
    have hF : F sLeft - F sRight = -C := by
      simpa only [hdneg, neg_one_mul] using h.2
    omega

end
end SM.WallGerm
