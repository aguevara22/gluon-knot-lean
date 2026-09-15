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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/GermNearbyChirotope.body.lean (prototype FlatSourceResponse, kernel session 25627, receipt
FlatSourceResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.WallGerm

noncomputable section
variable {n : ℕ}

/-- Every actual punctured parameter has a representative arbitrarily close
to the center on the same connected generic side, with the entire chirotope
unchanged. The representative is explicitly constructed at distance δ/2. -/
theorem nearby_same_chirotope (w : WallGerm n) (δ : ℝ) (hδ : 0 < δ) (hδr : δ ≤ w.radius)
    (s : w.Parameter) (hs : s.val ≠ 0) :
    ∃ u : w.Parameter, u.val ≠ 0 ∧ |u.val| < δ ∧
      ∀ i j k : ZMod n, chi (w.curve u) i j k = chi (w.curve s) i j k := by
  obtain ⟨b, r, hr⟩ := w.sideTime_surjective_punctured s hs
  let t0 : w.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  refine ⟨w.sideTime b t0, w.sideTime_ne_zero b t0, ?_, ?_⟩
  · have hv : |(w.sideTime b t0).val| = δ / 2 := by
      cases b <;> simp [sideTime, t0, abs_of_pos (by linarith : 0 < δ / 2)]
    rw [hv]
    linarith
  · intro i j k
    have hc := generic_family_chi_constant (w.continuous_sideTuple b) t0 r i j k
    change chi (w.curve (w.sideTime b t0)) i j k = chi (w.curve (w.sideTime b r)) i j k at hc
    rw [hr] at hc
    exact hc

end
end SM.WallGerm
