import SM.TreeChamber
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
import SM.ContactGapWords
import SM.ContactIntegerFactors
import SM.ContactContractionCoefficients
import SM.CuspIntegerFactors
import SM.ContactAffineSigns
import SM.ContactSignedResponse
import SM.ContactSourceResponse
import SM.SilentIntegerFactors
import SM.ExtensionAffineSigns
import SM.GermTreeEquality
import SM.ExtensionTreeResponse
import SM.PureCutBoundaryBounds
import SM.PureCutTreeResponse

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/TripleTreeData.body.lean (prototype TripleSilentTreeLaws, kernel session 2126, receipt
TripleSilentTreeLaws-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- At a G1 center every chirotope on either entire generic germ side agrees
with its central value. Repeated labels are handled separately, without
requiring the nongeneric wall center to be a generic tuple. -/
theorem g1_center_side_chi (w : WallGerm n) (hG1 : G1 w.center) :
    ∀ b : Bool, ∀ t : w.SideParameter, ∀ i j k : ZMod n,
      chi (w.sideTuple b t).val i j k = chi w.center i j k := by
  have hnear := w.continuous_curve.continuousAt.eventually
    (finite_nonzero_chi_persists (P := w.center))
  obtain ⟨δ, hδ, hδr, hlocal⟩ := (w.eventually_center_iff_radius _).mp hnear
  let q : w.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have hq : q.val < δ := by dsimp [q]; linarith
  intro b t i j k
  by_cases hij : i = j
  · subst j
    simp
  by_cases hjk : j = k
  · subst k
    simp
  by_cases hik : i = k
  · subst k
    simp
  have habs : |(w.sideTime b q).val| = q.val := by
    cases b <;> simp [sideTime, abs_of_pos q.property.1]
  have hc := hlocal (w.sideTime b q) (by rw [habs]; exact hq) i j k (hG1 i j k hij hjk hik)
  exact (generic_family_chi_constant (w.continuous_sideTuple b) t q i j k).trans hc

/-- Source thm:A-R3E(i): every ordinary/root composition weight, every open
sum and the complete rooted output agree at a triple wall. Both side points
and the physical root are arbitrary; G1 at the center is derived. -/
theorem triple_wall_tree_data (w : WallGerm n) (e f k : ZMod n)
    (hn : 3 ≤ n) (ht : w.TripleAt e f k) (g : ZMod n) (s t : w.SideParameter) :
    TreeDataEqual (w.sideTuple true t).val (w.sideTuple false s).val
      (w.sideTuple true t).property.1 (w.sideTuple false s).property.1 g hn := by
  have hc : G1 w.center := (w.pointZeros_empty_iff).mp ht.1
  have hchi : ∀ i j k, chi (w.sideTuple true t).val i j k =
      chi (w.sideTuple false s).val i j k := by
    intro i j k
    exact (w.g1_center_side_chi hc true t i j k).trans (w.g1_center_side_chi hc false s i j k).symm
  exact tree_data_eq_of_chi (w.sideTuple true t).property.1 (w.sideTuple false s).property.1 hchi g hn

end
end SM.WallGerm
