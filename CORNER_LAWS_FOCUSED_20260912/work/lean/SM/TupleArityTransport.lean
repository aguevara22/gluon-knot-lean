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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/TupleArityTransport.body.lean (prototype FlatSourceResponse, kernel session 25627, receipt
FlatSourceResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
variable {n q : ℕ} [NeZero n] [NeZero q]

/-- Reindexing by a proved equality of sizes preserves G1 by equality
induction. This assumes no invariance under an arbitrary permutation. -/
theorem g1_reindex_size (h : n = q) (P : LabelledTuple n) (hP : G1 P) :
    G1 (fun i : ZMod q => P ((ZMod.ringEquivCongr h).symm i)) := by
  subst q
  cases n <;> exact hP

/-- The same equality induction transports the full coefficient and its
actual root. No cyclic covariance or root independence is assumed here. -/
theorem treeCoefficient_reindex_size (h : n = q) (P : LabelledTuple n) (hP : G1 P)
    (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient (fun i : ZMod q => P ((ZMod.ringEquivCongr h).symm i))
      (g1_reindex_size h P hP) (ZMod.ringEquivCongr h g) (by omega) = treeCoefficient P hP g hn := by
  subst q
  cases n <;> rfl

/-- A proved pointwise tuple identity after size transport identifies the
two coefficients at root zero, including their dependent G1 witnesses. -/
theorem treeCoefficient_of_reindexed_tuple_eq (h : n = q)
    (P : LabelledTuple n) (Q : LabelledTuple q) (hP : G1 P) (hQ : G1 Q)
    (he : (fun i : ZMod q => P ((ZMod.ringEquivCongr h).symm i)) = Q) (hn : 3 ≤ n) :
    treeCoefficient P hP 0 hn = treeCoefficient Q hQ 0 (by omega) := by
  subst q
  cases n
  all_goals
    have hpq : P = Q := he
    clear he
    subst Q
    rfl

end
end SM
