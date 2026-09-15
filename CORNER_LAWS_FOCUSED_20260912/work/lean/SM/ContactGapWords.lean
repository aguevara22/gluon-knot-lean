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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/ContactGapWords.body.lean (prototype ContactSourceResponse, kernel session 96621, receipt
ContactSourceResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- At the contacted base root, the entire B-to-X gap is the second half.
Its arity equality and starting label are derived from the actual cut. -/
theorem contactBaseTriple_left_word (P : LabelledTuple n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) :
    ∃ hsize : (contactBaseTriple M a hn hc).leftInterval.leaves + 1 = secondHalfSize M a,
      (fun u : ZMod (secondHalfSize M a) => restrictedWordTuple P a
        (contactBaseTriple M a hn hc).leftInterval ((ZMod.ringEquivCongr hsize).symm u)) =
        secondHalf P M a := by
  have hd := contactDistance_bounds hn hc
  have hg := (contactBaseTriple_gaps M a hn hc).1
  have hs : (contactBaseTriple M a hn hc).leftInterval.leaves + 1 = secondHalfSize M a := by
    unfold secondHalfSize
    omega
  refine ⟨hs, restrictedWord_eq_secondHalf P a M a _ hs ?_⟩
  exact (contactBaseTriple_labels M a hn hc).1

/-- At the base root, the whole X-to-A gap is the first half shifted by -1,
so its local closing edge is the physical a-to-M edge. -/
theorem contactBaseTriple_right_word (P : LabelledTuple n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) :
    ∃ hsize : (contactBaseTriple M a hn hc).rightInterval.leaves + 1 = firstHalfSize M a,
      (fun u : ZMod (firstHalfSize M a) => restrictedWordTuple P a
        (contactBaseTriple M a hn hc).rightInterval ((ZMod.ringEquivCongr hsize).symm u)) =
        shift (-1) (firstHalf P M a) := by
  have hg := (contactBaseTriple_gaps M a hn hc).2
  have hs : (contactBaseTriple M a hn hc).rightInterval.leaves + 1 = firstHalfSize M a := by
    unfold firstHalfSize
    omega
  refine ⟨hs, restrictedWord_eq_shift_firstHalf P a M a _ hs ?_⟩
  exact (contactBaseTriple_labels M a hn hc).2.1

/-- Every root of the first inherited arc leaves exactly the same complete
B-to-X gap, including the endpoint-adjacent root at M. -/
theorem contactFirstArcTriple_right_word (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a) :
    ∃ hsize : (contactFirstArcTriple g M a hn hc hu).rightInterval.leaves + 1 = secondHalfSize M a,
      (fun u : ZMod (secondHalfSize M a) => restrictedWordTuple P g
        (contactFirstArcTriple g M a hn hc hu).rightInterval ((ZMod.ringEquivCongr hsize).symm u)) =
        secondHalf P M a := by
  have hd := contactDistance_bounds hn hc
  have hg := (contactFirstArcTriple_gaps g M a hn hc hu).2
  have hs : (contactFirstArcTriple g M a hn hc hu).rightInterval.leaves + 1 = secondHalfSize M a := by
    unfold secondHalfSize
    omega
  refine ⟨hs, restrictedWord_eq_secondHalf P g M a _ hs ?_⟩
  exact (contactFirstArcTriple_labels g M a hn hc hu).2.1

/-- Every root of the second inherited arc leaves the complete X-to-A gap,
including the endpoint-adjacent root ending at M. -/
theorem contactSecondArcTriple_left_word (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val) :
    ∃ hsize : (contactSecondArcTriple g M a hn hc hu).leftInterval.leaves + 1 = firstHalfSize M a,
      (fun u : ZMod (firstHalfSize M a) => restrictedWordTuple P g
        (contactSecondArcTriple g M a hn hc hu).leftInterval ((ZMod.ringEquivCongr hsize).symm u)) =
        shift (-1) (firstHalf P M a) := by
  have hg := (contactSecondArcTriple_gaps g M a hn hc hu).1
  have hs : (contactSecondArcTriple g M a hn hc hu).leftInterval.leaves + 1 = firstHalfSize M a := by
    unfold firstHalfSize
    omega
  refine ⟨hs, restrictedWord_eq_shift_firstHalf P g M a _ hs ?_⟩
  exact (contactSecondArcTriple_labels g M a hn hc hu).1

end
end SM
