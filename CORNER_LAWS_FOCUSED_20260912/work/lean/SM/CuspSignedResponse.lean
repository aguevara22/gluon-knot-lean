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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CuspSignedResponse.body.lean (prototype CuspSourceResponse, kernel session 68098, receipt
CuspSourceResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Cusp signed deletion response on the actual source domain. The line
coordinate is proved exterior, and all physical roots retain their exact
induced deletion labels; no flat betweenness premise is used. -/
theorem cusp_nonincident_signed_response (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.CuspAt j) (hg : ¬ incident j g) :
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
  obtain ⟨k, hk⟩ := boundaryIndex_surjective g j
  have hb := boundaryIndex_nonincident_interior g j k hk hg
  let t := consecutiveBoundaryTriple k hb.1 hb.2
  have hlabels := consecutiveBoundaryTriple_labels g j k hb.1 hb.2 hk
  have horder : CyclicTurnBoundaryOrder g j t := Or.inl hlabels
  have hZt : pointZeroTriples w.center = {t.vertexSet g} := by
    rw [nonincident_flat_contracted_support g j k hb.1 hb.2 hk]
    exact hf.2.1
  obtain ⟨r, hr, hω, hA, hM, hB⟩ := w.cusp_exterior_affine j hf
  have hchange := w.flat_boundary_chi_signChanges g j t horder hf.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine g (by have := hf.1; omega) t hZt hf.2.2.1 hchange
      (w.center (j - 1)) (w.center (j + 1) - w.center (j - 1)) 0 r 1 hω
      ((congrArg w.center hlabels.1).trans hA)
      ((congrArg w.center hlabels.2.1).trans hM)
      ((congrArg w.center hlabels.2.2).trans hB)
      (by rcases hr with hr | hr <;> linarith) (by rcases hr with hr | hr <;> linarith) (by norm_num)
  have hproper := consecutiveBoundaryTriple_proper hf.1 k hb.1 hb.2
  have hgaps := consecutiveBoundaryTriple_gaps k hb.1 hb.2
  have hfactors := integer_wall_factor_two_leaves w.center g t hZt hgaps.1 hgaps.2
    (wallLeftEpsilon 0 r 1) (wallRightEpsilon 0 r 1)
  have hcoeff := nonincident_flat_contracted_coefficient w.center g j k hb.1 hb.2 hk hg
    hf.2.1 (by have := hf.1; omega)
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  rw [dif_pos hproper, hfactors, one_mul, hcoeff] at hr
  refine ⟨?_, hr.2⟩
  simpa only [flat_boundary_geometric_sign _ g j t horder, sub_neg_eq_add] using hr.1


variable {m : ℕ}

/-- Cusp signed deletion response on the actual source domain. The line
coordinate is proved exterior, and all physical roots retain their exact
induced deletion labels; no flat betweenness premise is used. -/
theorem cusp_incoming_signed_response (w : WallGerm (m + 4)) (j : ZMod (m + 4))
    (hf : w.CuspAt j) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 (j - 1) (by omega) -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 (j - 1) (by omega) =
          d * treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j (j - 1)) (by omega)) := by
  let t := incomingFlatTriple (n := m + 4) (by omega)
  have hlabels := incomingFlatTriple_labels (n := m + 4) (by omega) j
  have horder : CyclicTurnBoundaryOrder (j - 1) j t := Or.inr (Or.inl hlabels)
  have hZt : pointZeroTriples w.center = {t.vertexSet (j - 1)} := by
    simpa only [t, incomingFlatTriple_support, pointZeros] using hf.2.1
  obtain ⟨r, hr, hω, hA, hM, hB⟩ := w.cusp_exterior_affine j hf
  have hchange := w.flat_boundary_chi_signChanges (j - 1) j t horder hf.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine (j - 1) (by omega) t hZt hf.2.2.1 hchange
      (w.center (j - 1)) (w.center (j + 1) - w.center (j - 1)) r 1 0 hω
      ((congrArg w.center hlabels.1).trans hM)
      ((congrArg w.center hlabels.2.1).trans hB)
      ((congrArg w.center hlabels.2.2).trans hA)
      (by rcases hr with hr | hr <;> linarith) (by norm_num) (by rcases hr with hr | hr <;> linarith)
  have hintervals := incomingFlatTriple_intervals (n := m + 4) (by omega)
  have hfull : ¬ t.spanInterval ≠ fullBoundaryInterval (by omega) := not_ne_iff.mpr hintervals.1
  have hgap : criticalIntervalIntegerOutput w.center (j - 1) t hZt t.rightInterval t.rightInterval_excludes_span =
      treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
        (fusionIndex j (j - 1)) (by omega) := incoming_flat_integer_gap w.center j hf.2.1
  have hfactor : (criticalGapUInteger w.center (j - 1) t hZt t.leftInterval t.leftInterval_excludes_span
        (wallLeftEpsilon r 1 0) *
      criticalGapUInteger w.center (j - 1) t hZt t.rightInterval t.rightInterval_excludes_span
        (wallRightEpsilon r 1 0)) + (criticalGapVInteger w.center (j - 1) t hZt t.leftInterval t.leftInterval_excludes_span
        (wallLeftEpsilon r 1 0) *
      criticalGapVInteger w.center (j - 1) t hZt t.rightInterval t.rightInterval_excludes_span
        (wallRightEpsilon r 1 0)) =
      criticalIntervalIntegerOutput w.center (j - 1) t hZt t.rightInterval t.rightInterval_excludes_span := by
    rcases hr with hr | hr
    · have hε := cusp_epsilons_incoming_lt_zero r hr
      have hfac := integer_wall_factor_left_leaf_pos_neg w.center (j - 1) t hZt hintervals.2.1 (by change 2 ≤ m + 2; omega)
      rw [hε.1, hε.2, hfac.1, hfac.2, add_zero]
    · have hε := cusp_epsilons_incoming_gt_one r hr
      have hfac := integer_wall_factor_left_leaf_pos_pos w.center (j - 1) t hZt hintervals.2.1 (by change 2 ≤ m + 2; omega)
      rw [hε.1, hε.2, hfac.1, hfac.2, zero_add]
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  rw [dif_neg hfull, hfactor, hgap] at hr
  refine ⟨?_, hr.2⟩
  simpa only [flat_boundary_geometric_sign _ (j - 1) j t horder, sub_neg_eq_add] using hr.1

/-- Cusp signed deletion response on the actual source domain. The line
coordinate is proved exterior, and all physical roots retain their exact
induced deletion labels; no flat betweenness premise is used. -/
theorem cusp_outgoing_signed_response (w : WallGerm (m + 4)) (j : ZMod (m + 4))
    (hf : w.CuspAt j) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 j (by omega) -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 j (by omega) =
          d * treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j j) (by omega)) := by
  let t := outgoingFlatTriple (n := m + 4) (by omega)
  have hlabels := outgoingFlatTriple_labels (n := m + 4) (by omega) j
  have horder : CyclicTurnBoundaryOrder j j t := Or.inr (Or.inr hlabels)
  have hZt : pointZeroTriples w.center = {t.vertexSet j} := by
    simpa only [t, outgoingFlatTriple_support, pointZeros] using hf.2.1
  obtain ⟨r, hr, hω, hA, hM, hB⟩ := w.cusp_exterior_affine j hf
  have hchange := w.flat_boundary_chi_signChanges j j t horder hf.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine j (by omega) t hZt hf.2.2.1 hchange
      (w.center (j - 1)) (w.center (j + 1) - w.center (j - 1)) 1 0 r hω
      ((congrArg w.center hlabels.1).trans hB)
      ((congrArg w.center hlabels.2.1).trans hA)
      ((congrArg w.center hlabels.2.2).trans hM)
      (by norm_num) (by rcases hr with hr | hr <;> linarith) (by rcases hr with hr | hr <;> linarith)
  have hintervals := outgoingFlatTriple_intervals (n := m + 4) (by omega)
  have hfull : ¬ t.spanInterval ≠ fullBoundaryInterval (by omega) := not_ne_iff.mpr hintervals.1
  have hgap : criticalIntervalIntegerOutput w.center j t hZt t.leftInterval t.leftInterval_excludes_span =
      treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
        (fusionIndex j j) (by omega) := outgoing_flat_integer_gap w.center j hf.2.1
  have hfactor : (criticalGapUInteger w.center j t hZt t.leftInterval t.leftInterval_excludes_span
        (wallLeftEpsilon 1 0 r) *
      criticalGapUInteger w.center j t hZt t.rightInterval t.rightInterval_excludes_span
        (wallRightEpsilon 1 0 r)) + (criticalGapVInteger w.center j t hZt t.leftInterval t.leftInterval_excludes_span
        (wallLeftEpsilon 1 0 r) *
      criticalGapVInteger w.center j t hZt t.rightInterval t.rightInterval_excludes_span
        (wallRightEpsilon 1 0 r)) =
      criticalIntervalIntegerOutput w.center j t hZt t.leftInterval t.leftInterval_excludes_span := by
    rcases hr with hr | hr
    · have hε := cusp_epsilons_outgoing_lt_zero r hr
      have hfac := integer_wall_factor_right_leaf_pos_pos w.center j t hZt (by change 2 ≤ m + 2; omega) hintervals.2.2
      rw [hε.1, hε.2, hfac.1, hfac.2, zero_add]
    · have hε := cusp_epsilons_outgoing_gt_one r hr
      have hfac := integer_wall_factor_right_leaf_neg_pos w.center j t hZt (by change 2 ≤ m + 2; omega) hintervals.2.2
      rw [hε.1, hε.2, hfac.1, hfac.2, add_zero]
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  rw [dif_neg hfull, hfactor, hgap] at hr
  refine ⟨?_, hr.2⟩
  simpa only [flat_boundary_geometric_sign _ j j t horder, sub_neg_eq_add] using hr.1

/-- Cusp signed deletion response on the actual source domain. The line
coordinate is proved exterior, and all physical roots retain their exact
induced deletion labels; no flat betweenness premise is used. -/
theorem cusp_incident_signed_response_all_sizes (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.CuspAt j) (hg : incident j g) :
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
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by have := hf.1; omega⟩
  rcases hg with hg | hg
  · subst g
    exact w.cusp_incoming_signed_response j hf
  · subst g
    exact w.cusp_outgoing_signed_response j hf


/-- Cusp signed deletion response on the actual source domain. The line
coordinate is proved exterior, and all physical roots retain their exact
induced deletion labels; no flat betweenness premise is used. -/
theorem cusp_signed_response_all_roots (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.CuspAt j) :
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
  · exact w.cusp_incident_signed_response_all_sizes j g hf hg
  · exact w.cusp_nonincident_signed_response j g hf hg

end
end SM.WallGerm
