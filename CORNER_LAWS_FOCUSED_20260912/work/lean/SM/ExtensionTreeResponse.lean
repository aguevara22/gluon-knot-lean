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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/ExtensionTreeResponse.body.lean (prototype TripleSilentTreeLaws, kernel session 2126, receipt
TripleSilentTreeLaws-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- At the exterior base root both full-span products vanish: their opposite
epsilons each place a zero nonleaf unit factor in the required product. -/
theorem extension_base_tree_silent_near (w : WallGerm n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.ExtensionAt M a) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 a hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 a hn = 0 := by
  let t := contactBaseTriple M a hn hc.1
  have hlabels := contactBaseTriple_labels M a hn hc.1
  have horder : CyclicContactBoundaryOrder a M a t := Or.inr (Or.inl hlabels)
  have hZt : pointZeroTriples w.center = {t.vertexSet a} := by
    rw [contactBaseTriple_support]
    exact hc.2.1
  obtain ⟨r, hr, hω, hA, hB, hX⟩ := w.extension_exterior_affine M a hn hc
  have hchange := w.contact_boundary_chi_signChanges a M a t horder hc.2.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hδr, hresponse⟩ :=
    w.single_triple_integer_response_of_affine a hn t hZt hc.2.2.1 hchange
      (w.center a) (w.center (a + 1) - w.center a) 1 r 0 hω
      ((congrArg w.center hlabels.1).trans hB)
      ((congrArg w.center hlabels.2.1).trans hX)
      ((congrArg w.center hlabels.2.2).trans hA)
      (by rcases hr with hr | hr <;> linarith) (by rcases hr with hr | hr <;> linarith) (by norm_num)
  have hgaps := contactBaseTriple_gaps M a hn hc.1
  have hdist := contactDistance_bounds hn hc.1
  have hL : 2 ≤ t.leftInterval.leaves := by dsimp only [t]; omega
  have hR : 2 ≤ t.rightInterval.leaves := by dsimp only [t]; omega
  have hzero := integer_UV_products_zero_of_nonleaves_opposite w.center a t hZt hL hR
    (wallLeftEpsilon 1 r 0) (wallRightEpsilon 1 r 0) (extension_epsilons_base r hr)
  have hfull : ¬ t.spanInterval ≠ fullBoundaryInterval hn :=
    not_ne_iff.mpr (contactBaseTriple_full M a hn hc.1)
  refine ⟨δ, hδ, hδr, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have he := (hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus).2
  rw [dif_neg hfull, hzero.1, hzero.2, add_zero, mul_zero] at he
  exact he

/-- Every first-arc exterior root has positive right epsilon and a nonleaf
right gap, so the proper-span source product vanishes in both exterior ranges. -/
theorem extension_first_arc_tree_silent_near (w : WallGerm n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.ExtensionAt M a) (hu : (g - M).val < contactDistance M a) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn = 0 := by
  let t := contactFirstArcTriple g M a hn hc.1 hu
  have hlabels := contactFirstArcTriple_labels g M a hn hc.1 hu
  have horder : CyclicContactBoundaryOrder g M a t := Or.inl hlabels
  have hZt : pointZeroTriples w.center = {t.vertexSet g} := by
    rw [contactFirstArcTriple_support]
    exact hc.2.1
  obtain ⟨r, hr, hω, hA, hB, hX⟩ := w.extension_exterior_affine M a hn hc
  have hchange := w.contact_boundary_chi_signChanges g M a t horder hc.2.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hδr, hresponse⟩ :=
    w.single_triple_integer_response_of_affine g hn t hZt hc.2.2.1 hchange
      (w.center a) (w.center (a + 1) - w.center a) 0 1 r hω
      ((congrArg w.center hlabels.1).trans hA)
      ((congrArg w.center hlabels.2.1).trans hB)
      ((congrArg w.center hlabels.2.2).trans hX)
      (by norm_num) (by rcases hr with hr | hr <;> linarith) (by rcases hr with hr | hr <;> linarith)
  have hgaps := contactFirstArcTriple_gaps g M a hn hc.1 hu
  have hdist := contactDistance_bounds hn hc.1
  have hR : 2 ≤ t.rightInterval.leaves := by dsimp only [t]; omega
  have hε := extension_right_epsilon_first_arc r hr
  have hzero := integer_U_product_zero_of_right_nonleaf_pos w.center g t hZt hR (wallLeftEpsilon 0 1 r)
  have hproper := contactFirstArcTriple_proper g M a hn hc.1 hu
  refine ⟨δ, hδ, hδr, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have he := (hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus).2
  rw [dif_pos hproper, hε, hzero, zero_mul, mul_zero] at he
  exact he

/-- Every second-arc exterior root has positive left epsilon and a nonleaf
left gap. Root endpoints are retained by the exact index-domain inequality. -/
theorem extension_second_arc_tree_silent_near (w : WallGerm n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.ExtensionAt M a) (hu : contactDistance M a < (g - M).val) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn = 0 := by
  let t := contactSecondArcTriple g M a hn hc.1 hu
  have hlabels := contactSecondArcTriple_labels g M a hn hc.1 hu
  have horder : CyclicContactBoundaryOrder g M a t := Or.inr (Or.inr hlabels)
  have hZt : pointZeroTriples w.center = {t.vertexSet g} := by
    rw [contactSecondArcTriple_support]
    exact hc.2.1
  obtain ⟨r, hr, hω, hA, hB, hX⟩ := w.extension_exterior_affine M a hn hc
  have hchange := w.contact_boundary_chi_signChanges g M a t horder hc.2.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hδr, hresponse⟩ :=
    w.single_triple_integer_response_of_affine g hn t hZt hc.2.2.1 hchange
      (w.center a) (w.center (a + 1) - w.center a) r 0 1 hω
      ((congrArg w.center hlabels.1).trans hX)
      ((congrArg w.center hlabels.2.1).trans hA)
      ((congrArg w.center hlabels.2.2).trans hB)
      (by rcases hr with hr | hr <;> linarith) (by norm_num) (by rcases hr with hr | hr <;> linarith)
  have hgaps := contactSecondArcTriple_gaps g M a hn hc.1 hu
  have hdist := contactDistance_bounds hn hc.1
  have hL : 2 ≤ t.leftInterval.leaves := by dsimp only [t]; omega
  have hε := extension_left_epsilon_second_arc r hr
  have hzero := integer_U_product_zero_of_left_nonleaf_pos w.center g t hZt hL (wallRightEpsilon r 0 1)
  have hproper := contactSecondArcTriple_proper g M a hn hc.1 hu
  refine ⟨δ, hδ, hδr, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have he := (hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus).2
  rw [dif_pos hproper, hε, hzero, zero_mul, mul_zero] at he
  exact he

/-- The exterior root cases are exhaustive, including every edge incident
to a critical vertex. No consecutive cusp/flat wall is added to the domain. -/
theorem extension_tree_silent_near (w : WallGerm n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.ExtensionAt M a) (g : ZMod n) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn = 0 := by
  by_cases hg : g = a
  · subst g
    exact w.extension_base_tree_silent_near M a hn hc
  · by_cases hu : (g - M).val < contactDistance M a
    · exact w.extension_first_arc_tree_silent_near g M a hn hc hu
    · have hne : (g - M).val ≠ contactDistance M a := by
        intro he
        apply hg
        apply sub_left_injective
        exact ZMod.val_injective n he
      have hs : contactDistance M a < (g - M).val := by omega
      exact w.extension_second_arc_tree_silent_near g M a hn hc hs

/-- Source exterior-extension silence for every root and arbitrary independent
points on the complete two sides, with no remaining radius restriction. -/
theorem extension_tree_silent (w : WallGerm n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.ExtensionAt M a) (g : ZMod n) (s t : w.SideParameter) :
    treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn =
      treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn := by
  obtain ⟨δ, hδ, hδr, hresponse⟩ := w.extension_tree_silent_near M a hn hc g
  exact w.tree_sides_equal_of_local_zero g hn δ hδ hδr hresponse s t

end
end SM.WallGerm
