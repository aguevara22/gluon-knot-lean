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
import SM.CuspAffineSigns
import SM.CuspIntegerFactors
import SM.CuspSignedResponse
import SM.CuspOrientedResponse

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CuspSourceResponse.body.lean (prototype CuspSourceResponse, kernel session 68098, receipt
CuspSourceResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Actual loop/no-loop normalization. The existing principal-angle rotation
jump is combined with the independently proved integer coefficient response.
The source may be threaded; no emptiness or root independence is assumed. -/
theorem cusp_loop_tree_response (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.CuspAt j) {b : Bool} (hb : CuspCase w.center j b)
    (s t : w.SideParameter) :
    (turn (w.sideTuple (w.cuspLoopSide b j) s).val j = -1 ∨
      turn (w.sideTuple (w.cuspLoopSide b j) s).val j = 1) ∧
    (rotationNumber (w.sideTuple (w.cuspLoopSide b j) s).val -
      rotationNumber (w.sideTuple (!(w.cuspLoopSide b j)) t).val =
        (turn (w.sideTuple (w.cuspLoopSide b j) s).val j : ℝ)) ∧
    (treeCoefficient (w.sideTuple (w.cuspLoopSide b j) s).val
        (w.sideTuple (w.cuspLoopSide b j) s).property.1 g (by have := hf.1; omega) -
      treeCoefficient (w.sideTuple (!(w.cuspLoopSide b j)) t).val
        (w.sideTuple (!(w.cuspLoopSide b j)) t).property.1 g (by have := hf.1; omega) =
      -(turn (w.sideTuple (w.cuspLoopSide b j) s).val j : ℤ) *
        treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
          (fusionIndex j g) (by have := hf.1; omega)) := by
  have hrot := w.cusp_rotation_jump hf hb s t
  have hturns := w.cusp_loop_turns hf hb s t
  refine ⟨hrot.2, hrot.1, ?_⟩
  rcases hturns.2.2.2 with hNeg | hPos
  · have hNo : turn (w.sideTuple (!(w.cuspLoopSide b j)) t).val j = 1 := by
      have h := congrArg (fun z : SignType => -z) hturns.2.2.1
      simpa only [hNeg, neg_neg] using h.symm
    have hC := w.cusp_negative_minus_positive j g hf
      (w.sideTime (w.cuspLoopSide b j) s) (w.sideTime (!(w.cuspLoopSide b j)) t)
      (w.sideTime_ne_zero _ s) (w.sideTime_ne_zero _ t) hNeg hNo
    simp only [hNeg, SignType.coe_neg_one, neg_neg, one_mul]
    simpa only [sideTuple] using hC
  · have hNo : turn (w.sideTuple (!(w.cuspLoopSide b j)) t).val j = -1 := by
      have h := congrArg (fun z : SignType => -z) hturns.2.2.1
      simpa only [hPos, neg_neg] using h.symm
    have hC := w.cusp_negative_minus_positive j g hf
      (w.sideTime (!(w.cuspLoopSide b j)) t) (w.sideTime (w.cuspLoopSide b j) s)
      (w.sideTime_ne_zero _ t) (w.sideTime_ne_zero _ s) hNo hPos
    have hrev := congrArg (fun z : ℤ => -z) hC
    simp only [hPos, SignType.coe_one, neg_one_mul]
    simpa only [sideTuple, neg_sub] using hrev

/-- Source thm:A-S4 with a derived unique central case and a single integer
rotation jump chosen before all side representatives and all physical roots.
Deletion G1 is proved from the source singleton critical support. -/
theorem cusp_tree_law (w : WallGerm (n + 1)) (j : ZMod (n + 1)) (hf : w.CuspAt j) :
    ∃ b : Bool, CuspCase w.center j b ∧
      (∀ b' : Bool, CuspCase w.center j b' → b' = b) ∧
      ∃ κ : ℤ, (κ = -1 ∨ κ = 1) ∧
        ∀ s t : w.SideParameter,
          (rotationNumber (w.sideTuple (w.cuspLoopSide b j) s).val -
            rotationNumber (w.sideTuple (!(w.cuspLoopSide b j)) t).val = (κ : ℝ)) ∧
          ∀ g : ZMod (n + 1),
            treeCoefficient (w.sideTuple (w.cuspLoopSide b j) s).val
                (w.sideTuple (w.cuspLoopSide b j) s).property.1 g (by have := hf.1; omega) -
              treeCoefficient (w.sideTuple (!(w.cuspLoopSide b j)) t).val
                (w.sideTuple (!(w.cuspLoopSide b j)) t).property.1 g (by have := hf.1; omega) =
              -κ * treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
                (fusionIndex j g) (by have := hf.1; omega) := by
  obtain ⟨b, hb, huniq⟩ := w.cusp_case_existsUnique hf
  let κ : ℤ := (turn (w.sideTuple (w.cuspLoopSide b j) w.sideBase).val j : ℤ)
  have hκ := (w.cusp_rotation_jump hf hb w.sideBase w.sideBase).2
  refine ⟨b, hb, huniq, κ, ?_, ?_⟩
  · rcases hκ with hNeg | hPos
    · left
      simp only [κ, hNeg, SignType.coe_neg_one]
    · right
      simp only [κ, hPos, SignType.coe_one]
  · intro s t
    have hturn := w.side_turn_constant (w.cuspLoopSide b j) s w.sideBase j
    refine ⟨?_, ?_⟩
    · have hrot := (w.cusp_rotation_jump hf hb s t).1
      simpa only [κ, SignType.intCast_cast, hturn] using hrot
    · intro g
      have hC := (w.cusp_loop_tree_response j g hf hb s t).2.2
      simpa only [κ, hturn] using hC

end
end SM.WallGerm
