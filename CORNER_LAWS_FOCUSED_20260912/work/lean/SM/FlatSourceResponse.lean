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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/FlatSourceResponse.body.lean (prototype FlatSourceResponse, kernel session 25627, receipt
FlatSourceResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The flat law for the actual rooted tree coefficient at every source
root and every pair of punctured right/left representatives in the germ.
Connected-side chirotope constancy removes the local radius restriction. -/
theorem flat_right_minus_left (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.FlatAt j) (sRight sLeft : w.Parameter)
    (hRight0 : sRight.val ≠ 0) (hLeft0 : sLeft.val ≠ 0)
    (hRight : turn (w.curve sRight) j = -1) (hLeft : turn (w.curve sLeft) j = 1) :
    treeCoefficient (w.curve sRight) (w.generic_punctured sRight hRight0).1 g
        (by have := hf.1; omega) -
      treeCoefficient (w.curve sLeft) (w.generic_punctured sLeft hLeft0).1 g
        (by have := hf.1; omega) =
      treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
        (fusionIndex j g) (by have := hf.1; omega) := by
  obtain ⟨δ, hδ, hδr, hresponse⟩ := w.flat_right_minus_left_near j g hf
  obtain ⟨r, hr0, hrNear, hrChi⟩ := w.nearby_same_chirotope δ hδ hδr sRight hRight0
  obtain ⟨l, hl0, hlNear, hlChi⟩ := w.nearby_same_chirotope δ hδ hδr sLeft hLeft0
  have hrTurn : turn (w.curve r) j = -1 := (hrChi (j - 1) j (j + 1)).trans hRight
  have hlTurn : turn (w.curve l) j = 1 := (hlChi (j - 1) j (j + 1)).trans hLeft
  have he := hresponse r l hr0 hl0 hrTurn hlTurn hrNear hlNear
  have hrCoeff := treeCoefficient_eq_of_chi (w.generic_punctured r hr0).1
    (w.generic_punctured sRight hRight0).1 hrChi g (by have := hf.1; omega)
  have hlCoeff := treeCoefficient_eq_of_chi (w.generic_punctured l hl0).1
    (w.generic_punctured sLeft hLeft0).1 hlChi g (by have := hf.1; omega)
  rw [hrCoeff, hlCoeff] at he
  exact he

end
end SM.WallGerm
