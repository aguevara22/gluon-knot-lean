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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/PureCutTreeResponse.body.lean (prototype TripleSilentTreeLaws, kernel session 2126, receipt
TripleSilentTreeLaws-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Every pure-cut root has two nonleaf gaps and a proper critical span.
One positive epsilon annihilates the source product for every line order;
no equality of the individual open sums is asserted. -/
theorem pure_cut_tree_silent_near (w : WallGerm n) (i j k : ZMod n)
    (hn : 3 ≤ n) (hc : w.PureCutAt i j k) (g : ZMod n) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn = 0 := by
  have hcard : ({i, j, k} : Finset (ZMod n)).card = 3 := (singlePointTriple_data hc.2.1).1
  have hn6 := noConsecutive_size hcard hc.1
  have hinj := singlePointTriple_vertices_injective (by omega : 4 ≤ n) hc.2.1
  have hsep : (({i, j, k} : Finset (ZMod n)) : Set (ZMod n)).Pairwise
      (fun a b => w.center a ≠ w.center b) := by
    intro a ha b hb hab
    exact hinj.ne hab
  obtain ⟨t, ht, huniq⟩ := w.single_triple_boundary_data g {i, j, k} hc.2.1 hsep i j k rfl hc.2.2.2
  have hZt : pointZeroTriples w.center = {t.vertexSet g} := by
    rw [ht.1]
    exact hc.2.1
  have hnc : NoConsecutive (t.vertexSet g) := by rw [ht.1]; exact hc.1
  obtain ⟨p, ω, x, y, z, hω, hx, hy, hz, hyx, hzy, hzx⟩ :=
    critical_boundary_affine_data w.center g t hZt ht.2.1.1 ht.2.1.2.1 ht.2.1.2.2
  obtain ⟨d, hd, δ, hδ, hδr, hresponse⟩ :=
    w.single_triple_integer_response_of_affine g hn t hZt hc.2.2.1 ht.2.2
      p ω x y z hω hx hy hz hyx hzy hzx
  have hL := pureCut_left_gap_nonleaf g t hnc
  have hR := pureCut_right_gap_nonleaf g t hnc
  have hproper := pureCut_span_proper g hn t hnc
  have hzero := integer_U_product_zero_of_nonleaves_one_positive w.center g t hZt hL hR
    (wallLeftEpsilon x y z) (wallRightEpsilon x y z) (wall_epsilon_positive x y z hzx)
  refine ⟨δ, hδ, hδr, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := (hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus).2
  rw [dif_pos hproper, hzero, zero_mul, mul_zero] at hr
  exact hr

/-- Source pure-cut silence for every physical root and arbitrary independent
points on the two germ sides, with no remaining radius restriction. -/
theorem pure_cut_tree_silent (w : WallGerm n) (i j k : ZMod n)
    (hn : 3 ≤ n) (hc : w.PureCutAt i j k) (g : ZMod n) (s t : w.SideParameter) :
    treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn =
      treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn := by
  obtain ⟨δ, hδ, hδr, hresponse⟩ := w.pure_cut_tree_silent_near i j k hn hc g
  exact w.tree_sides_equal_of_local_zero g hn δ hδ hδr hresponse s t

end
end SM.WallGerm
