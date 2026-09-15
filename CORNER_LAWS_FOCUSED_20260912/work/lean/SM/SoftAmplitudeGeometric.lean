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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftAmplitudeGeometric.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Specialize complete far-only duplication to actual parent and core rooted
tree coefficients. The conditional far-array equality is the physical one;
all sign-square hypotheses are derived from the polygon and admissible vector. -/
theorem soft_treeCoefficient_of_far_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : G1 P) (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q)
    (ε : ℝ) (hQ : G1 (softInsertion P j q ε)) (g : ZMod n)
    (hpull : geometricBoundaryArray (R := ℚ) (softInsertion P j q ε) (softParentEdge j g) =
      tripleLift (softRootPosition j g) (geometricBoundaryArray P g) (softRootFarData P j g q)) :
    (treeCoefficient (softInsertion P j q ε) hQ (softParentEdge j g)
      (by omega : 3 ≤ n + 1) : ℚ) =
      ((((softAttachmentMinus P j q : ℤ) : ℚ) +
        ((softAttachmentPlus P j q : ℤ) : ℚ)) / 2) * (treeCoefficient P hP g hn : ℚ) := by
  rw [treeCoefficient_farOnly (R := ℚ) (softInsertion P j q ε) hQ (softParentEdge j g)
      (by omega : 3 ≤ n + 1), treeCoefficient_farOnly (R := ℚ) P hP g hn, hpull]
  rw [farOnlyOutput_duplication hn (softRootPosition j g) (geometricBoundaryArray P g)
    (softRootFarData P j g q) (geometricBoundaryArray_square hP g) (softRootFarData_square hq g)]
  rw [(softRootFarData_cyclic_attachments P j g q).1,
    (softRootFarData_cyclic_attachments P j g q).2]

/-- One positive radius gives the rooted coefficient identity for every actual
nonsoft root corresponding to a core root. The parent G1 proof and all far-data
identities are constructed locally; no recurrence, output law or child G1 is assumed. -/
theorem soft_treeCoefficient_uniform (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : G1 P) (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ hQ : G1 (softInsertion P j q ε), ∀ g : ZMod n,
        (treeCoefficient (softInsertion P j q ε) hQ (softParentEdge j g)
          (by omega : 3 ≤ n + 1) : ℚ) =
          ((((softAttachmentMinus P j q : ℤ) : ℚ) +
            ((softAttachmentPlus P j q : ℤ) : ℚ)) / 2) * (treeCoefficient P hP g hn : ℚ) := by
  obtain ⟨δ, hδ, hf⟩ := soft_geometric_duplication_data hn hP j q hq
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨hQ, hdata⟩ := hf ε hε hεδ
  refine ⟨hQ, ?_⟩
  intro g
  exact soft_treeCoefficient_of_far_data hn hP j q hq ε hQ g (hdata g).1

end
end SM.SoftDuplication
