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
import SM.SoftDuplicationFullEndpointOutput
import SM.SoftDuplicationOrdinaryIdentification
import SM.SoftAmplitudeGeometric

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftAmplitudeSectors.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The printed soft multiplier is computed in the rationals after casting both
attachment signs through the integers; no integer division is used. -/
def softAmplitudeMultiplier (P : LabelledTuple n) (j : ZMod n) (q : Plane) : ℚ :=
  ((((softAttachmentMinus P j q : SignType) : ℤ) : ℚ) +
    (((softAttachmentPlus P j q : SignType) : ℤ) : ℚ)) / 2

/-- In the source same-sign sector, both attachment signs equal the negative turn. -/
theorem softAmplitudeMultiplier_same_sign (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (hsector : softAttachmentMinus P j q = -turn P j ∧
      softAttachmentPlus P j q = -turn P j) :
    softAmplitudeMultiplier P j q = -(((turn P j : SignType) : ℤ) : ℚ) := by
  simp only [softAmplitudeMultiplier, hsector.1, hsector.2, SignType.coe_neg, Int.cast_neg]
  ring

/-- Distinct admissible attachment signs are the two opposite nonzero signs,
so their rational average is zero. Nonzeroness is derived from admissibility. -/
theorem softAmplitudeMultiplier_mixed (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (hq : SoftAdmissible P j q)
    (hsector : softAttachmentMinus P j q ≠ softAttachmentPlus P j q) :
    softAmplitudeMultiplier P j q = 0 := by
  have hn := softAttachment_signs_nonzero hq
  cases hm : softAttachmentMinus P j q <;>
    cases hp : softAttachmentPlus P j q <;>
    simp_all [softAmplitudeMultiplier]

/-- In the source loop sector, both attachment signs equal the turn. -/
theorem softAmplitudeMultiplier_loop (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (hsector : softAttachmentMinus P j q = turn P j ∧
      softAttachmentPlus P j q = turn P j) :
    softAmplitudeMultiplier P j q = (((turn P j : SignType) : ℤ) : ℚ) := by
  simp only [softAmplitudeMultiplier, hsector.1, hsector.2]
  ring

/-- Faithful rational casting gives the same-sign integer coefficient law. -/
theorem softAmplitude_integer_same_sign (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (hsector : softAttachmentMinus P j q = -turn P j ∧
      softAttachmentPlus P j q = -turn P j)
    (X Y : ℤ) (hXY : (X : ℚ) = softAmplitudeMultiplier P j q * (Y : ℚ)) :
    X = -(turn P j : ℤ) * Y := by
  rw [softAmplitudeMultiplier_same_sign P j q hsector] at hXY
  apply Int.cast_injective (α := ℚ)
  simpa only [Int.cast_mul, Int.cast_neg] using hXY

/-- The mixed sector gives a zero integer coefficient without any assumption on Y. -/
theorem softAmplitude_integer_mixed (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (hq : SoftAdmissible P j q)
    (hsector : softAttachmentMinus P j q ≠ softAttachmentPlus P j q)
    (X Y : ℤ) (hXY : (X : ℚ) = softAmplitudeMultiplier P j q * (Y : ℚ)) :
    X = 0 := by
  rw [softAmplitudeMultiplier_mixed P j q hq hsector, zero_mul] at hXY
  apply Int.cast_injective (α := ℚ)
  simpa only [Int.cast_zero] using hXY

/-- Faithful rational casting gives the loop-sector integer coefficient law. -/
theorem softAmplitude_integer_loop (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (hsector : softAttachmentMinus P j q = turn P j ∧
      softAttachmentPlus P j q = turn P j)
    (X Y : ℤ) (hXY : (X : ℚ) = softAmplitudeMultiplier P j q * (Y : ℚ)) :
    X = (turn P j : ℤ) * Y := by
  rw [softAmplitudeMultiplier_loop P j q hsector] at hXY
  apply Int.cast_injective (α := ℚ)
  simpa only [Int.cast_mul] using hXY

end
end SM.SoftDuplication
