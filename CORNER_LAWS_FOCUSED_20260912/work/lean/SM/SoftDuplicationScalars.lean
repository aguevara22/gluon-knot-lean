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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftDuplicationScalars.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

/-- Two presentations at an interval starting at the duplicated occurrence.
The intermediate t-value cancels in both ordinary and root transforms. -/
theorem first_ordinary (eta tX tY : ℚ) :
    (eta - tX) / 2 + (tX - tY) / 2 = (eta - tY) / 2 := by
  ring

theorem first_root (eta tX tY : ℚ) :
    (eta - tX) / 2 + (tX + tY) / 2 = (eta + tY) / 2 := by
  ring

/-- The same cancellation applies to the last child, with the last boundary
and exterior endpoint playing the ordered roles from the source. -/
theorem last_ordinary (eta tY tX : ℚ) :
    (eta - tY) / 2 + (tY - tX) / 2 = (eta - tX) / 2 := by
  ring

theorem last_root (eta tY tX : ℚ) :
    (eta - tY) / 2 + (tY + tX) / 2 = (eta + tX) / 2 := by
  ring

/-- The exact residual for a spanning ordinary top before any sign identity.
This is not asserted zero for arbitrary independent far scalars. -/
theorem ordinary_residual (a b h : ℚ) :
    -(a + b) / 2 * ((a - h) / 2) + ((a - h) * (b - h)) / 4 =
      (h ^ 2 - a ^ 2) / 4 := by
  ring

/-- The root residual has the same value with the far signs reversed. -/
theorem root_residual (a b h : ℚ) :
    -(a + b) / 2 * ((a + h) / 2) + ((a + h) * (b + h)) / 4 =
      (h ^ 2 - a ^ 2) / 4 := by
  ring

/-- A nonzero SignType supplies precisely the square identity consumed below. -/
theorem sign_square (a : SignType) (ha : a ≠ 0) :
    (((a : ℤ) : ℚ)) ^ 2 = 1 := by
  cases a <;> norm_num at *

/-- Sum of the B-only, A-only and both-cut presentations at an ordinary top.
Only equality of a^2 and h^2 is needed; b and the neighbor data are arbitrary. -/
theorem three_ordinary (etaMinus etaPlus a b h : ℚ) (hsq : h ^ 2 = a ^ 2) :
    ((etaMinus - a) / 2) * ((a - h) / 2) +
      ((etaPlus - b) / 2) * ((a - h) / 2) +
      ((a - h) / 2) * ((b - h) / 2) =
        ((etaMinus + etaPlus) / 2) * ((a - h) / 2) := by
  calc
    _ = ((etaMinus + etaPlus) / 2) * ((a - h) / 2) +
        (h ^ 2 - a ^ 2) / 4 := by ring
    _ = _ := by rw [hsq]; ring

theorem three_root (etaMinus etaPlus a b h : ℚ) (hsq : h ^ 2 = a ^ 2) :
    ((etaMinus - a) / 2) * ((a + h) / 2) +
      ((etaPlus - b) / 2) * ((a + h) / 2) +
      ((a + h) / 2) * ((b + h) / 2) =
        ((etaMinus + etaPlus) / 2) * ((a + h) / 2) := by
  calc
    _ = ((etaMinus + etaPlus) / 2) * ((a + h) / 2) +
        (h ^ 2 - a ^ 2) / 4 := by ring
    _ = _ := by rw [hsq]; ring

/-- The three-row identities can be multiplied by any common exterior
product, including zero. No cancellation or division by that product occurs. -/
theorem three_ordinary_with_exterior (etaMinus etaPlus a b h F : ℚ)
    (hsq : h ^ 2 = a ^ 2) :
    (((etaMinus - a) / 2) * ((a - h) / 2)) * F +
      (((etaPlus - b) / 2) * ((a - h) / 2)) * F +
      (((a - h) / 2) * ((b - h) / 2)) * F =
        (((etaMinus + etaPlus) / 2) * ((a - h) / 2)) * F := by
  rw [← add_mul, ← add_mul, three_ordinary etaMinus etaPlus a b h hsq]

theorem three_root_with_exterior (etaMinus etaPlus a b h F : ℚ)
    (hsq : h ^ 2 = a ^ 2) :
    (((etaMinus - a) / 2) * ((a + h) / 2)) * F +
      (((etaPlus - b) / 2) * ((a + h) / 2)) * F +
      (((a + h) / 2) * ((b + h) / 2)) * F =
        (((etaMinus + etaPlus) / 2) * ((a + h) / 2)) * F := by
  rw [← add_mul, ← add_mul, three_root etaMinus etaPlus a b h hsq]

end SM.SoftDuplication
