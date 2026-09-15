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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/FlatAllRootResponse.body.lean (prototype FlatSourceResponse, kernel session 25627, receipt
FlatSourceResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Exhaust all physical roots using the two incident cases and the proved
nonincident contraction. No root condition remains as a hypothesis. -/
theorem flat_signed_response_all_roots (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.FlatAt j) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g
            (by have := hf.1; omega) -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g
            (by have := hf.1; omega) =
          d * treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j g) (by have := hf.1; omega)) := by
  by_cases hg : incident j g
  · exact w.flat_incident_signed_response_all_sizes j g hf hg
  · exact w.flat_nonincident_signed_response j g hf hg

/-- Source right-minus-left orientation of the actual coefficient response,
for every root and independent nearby punctured parameters. -/
theorem flat_right_minus_left_near (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.FlatAt j) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sRight sLeft : w.Parameter, ∀ hRight0 : sRight.val ≠ 0, ∀ hLeft0 : sLeft.val ≠ 0,
        turn (w.curve sRight) j = -1 → turn (w.curve sLeft) j = 1 →
        |sRight.val| < δ → |sLeft.val| < δ →
        treeCoefficient (w.curve sRight) (w.generic_punctured sRight hRight0).1 g
            (by have := hf.1; omega) -
          treeCoefficient (w.curve sLeft) (w.generic_punctured sLeft hLeft0).1 g
            (by have := hf.1; omega) =
          treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j g) (by have := hf.1; omega) := by
  classical
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ := w.flat_signed_response_all_roots j g hf
  let F : w.Parameter → ℤ := fun s =>
    if hs : s.val ≠ 0 then
      treeCoefficient (w.curve s) (w.generic_punctured s hs).1 g (by have := hf.1; omega)
    else 0
  have hFresponse :
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
          (F sPlus - F sMinus = d *
            treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
              (fusionIndex j g) (by have := hf.1; omega)) := by
    intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
    simpa only [F, dif_pos (ne_of_gt hPlus), dif_pos (ne_of_lt hMinus)] using
      hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  refine ⟨δ, hδ, hrad, ?_⟩
  intro sRight sLeft hRight0 hLeft0 hRight hLeft hRightNear hLeftNear
  have h := w.turn_response_right_minus_left j F
    (treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
      (fusionIndex j g) (by have := hf.1; omega)) d δ hd hδ hrad hFresponse
    sRight sLeft hRight0 hLeft0 hRight hLeft hRightNear hLeftNear
  simpa only [F, dif_pos hRight0, dif_pos hLeft0] using h

end
end SM.WallGerm
