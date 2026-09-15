namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- The base-root full-span response is the product of the two actual half
coefficients in source order. The doubled far-sign jump fixes its orientation. -/
theorem contact_base_signed_response (w : WallGerm n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.VertexEdgeAt M a) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(chi (w.curve sPlus) a (a + 1) M : ℤ) +
          (chi (w.curve sMinus) a (a + 1) M : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 a hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 a hn =
          d * (treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1)
            (-1) (contactHalfSizes_bounds hn hc.1).1.1 *
            treeCoefficient (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1)
              0 (contactHalfSizes_bounds hn hc.1).2.1)) := by
  let t := contactBaseTriple M a hn hc.1
  have hlabels := contactBaseTriple_labels M a hn hc.1
  have horder : CyclicContactBoundaryOrder a M a t := Or.inr (Or.inl hlabels)
  have hZt : pointZeroTriples w.center = {t.vertexSet a} := by
    rw [contactBaseTriple_support]
    exact hc.2.1
  obtain ⟨r, hr0, hr1, hω, hA, hB, hX⟩ := w.contact_interior_affine M a hn hc
  have hchange := w.contact_boundary_chi_signChanges a M a t horder hc.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine a hn t hZt hc.2.2.1 hchange
      (w.center a) (w.center (a + 1) - w.center a) 1 r 0 hω
      ((congrArg w.center hlabels.1).trans hB)
      ((congrArg w.center hlabels.2.1).trans hX)
      ((congrArg w.center hlabels.2.2).trans hA)
      (by linarith) (by linarith) (by norm_num)
  have hε := contact_epsilons_base r hr0 hr1
  have hgaps := contactBaseTriple_gaps M a hn hc.1
  have hdist := contactDistance_bounds hn hc.1
  have hL : 2 ≤ t.leftInterval.leaves := by dsimp only [t]; omega
  have hR : 2 ≤ t.rightInterval.leaves := by dsimp only [t]; omega
  have hfac := integer_wall_factor_two_nonleaves_pos_pos w.center a t hZt hL hR
  have hleft := contactBaseTriple_left_integer_gap w.center M a hn hc.1 hc.2.1
  have hright := contactBaseTriple_right_integer_gap w.center M a hn hc.1 hc.2.1
  have hfull : ¬ t.spanInterval ≠ fullBoundaryInterval hn :=
    not_ne_iff.mpr (contactBaseTriple_full M a hn hc.1)
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  rw [dif_neg hfull, hε.1, hε.2, hfac.1, hfac.2, zero_add, hleft, hright] at hr
  refine ⟨?_, ?_⟩
  · simpa only [contact_boundary_geometric_sign _ a M a t horder, sub_neg_eq_add] using hr.1
  · simpa only [mul_comm] using hr.2

/-- On the first inherited arc the proper contraction is the complete first
half at the same physical root; the other factor is the actual second half. -/
theorem contact_first_arc_signed_response (w : WallGerm n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.VertexEdgeAt M a) (hu : (g - M).val < contactDistance M a) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(chi (w.curve sPlus) a (a + 1) M : ℤ) +
          (chi (w.curve sMinus) a (a + 1) M : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn =
          d * (treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1)
            ((g - M).val : ZMod (firstHalfSize M a)) (contactHalfSizes_bounds hn hc.1).1.1 *
            treeCoefficient (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1)
              0 (contactHalfSizes_bounds hn hc.1).2.1)) := by
  let t := contactFirstArcTriple g M a hn hc.1 hu
  have hlabels := contactFirstArcTriple_labels g M a hn hc.1 hu
  have horder : CyclicContactBoundaryOrder g M a t := Or.inl hlabels
  have hZt : pointZeroTriples w.center = {t.vertexSet g} := by
    rw [contactFirstArcTriple_support]
    exact hc.2.1
  obtain ⟨r, hr0, hr1, hω, hA, hB, hX⟩ := w.contact_interior_affine M a hn hc
  have hchange := w.contact_boundary_chi_signChanges g M a t horder hc.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine g hn t hZt hc.2.2.1 hchange
      (w.center a) (w.center (a + 1) - w.center a) 0 1 r hω
      ((congrArg w.center hlabels.1).trans hA)
      ((congrArg w.center hlabels.2.1).trans hB)
      ((congrArg w.center hlabels.2.2).trans hX)
      (by norm_num) (by linarith) (by linarith)
  have hε := contact_epsilons_first_arc r hr0 hr1
  have hgaps := contactFirstArcTriple_gaps g M a hn hc.1 hu
  have hdist := contactDistance_bounds hn hc.1
  have hR : 2 ≤ t.rightInterval.leaves := by dsimp only [t]; omega
  have hfac := integer_wall_factor_left_leaf_pos_neg w.center g t hZt hgaps.1 hR
  have hgap := contactFirstArcTriple_right_integer_gap w.center g M a hn hc.1 hu hc.2.1
  have hcoeff := contactFirstArc_contracted_coefficient w.center g M a hn hc.1 hu hc.2.1
  have hproper := contactFirstArcTriple_proper g M a hn hc.1 hu
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  rw [dif_pos hproper, hε.1, hε.2, hfac.1, hgap, hcoeff] at hr
  refine ⟨?_, ?_⟩
  · simpa only [contact_boundary_geometric_sign _ g M a t horder, sub_neg_eq_add] using hr.1
  · simpa only [mul_comm] using hr.2

/-- On the second inherited arc the first-half closing factor multiplies the
complete second-half contraction at the original physical root. -/
theorem contact_second_arc_signed_response (w : WallGerm n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.VertexEdgeAt M a) (hu : contactDistance M a < (g - M).val) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(chi (w.curve sPlus) a (a + 1) M : ℤ) +
          (chi (w.curve sMinus) a (a + 1) M : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn =
          d * (treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1)
            (-1) (contactHalfSizes_bounds hn hc.1).1.1 *
            treeCoefficient (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1)
              ((g - a).val : ZMod (secondHalfSize M a)) (contactHalfSizes_bounds hn hc.1).2.1)) := by
  let t := contactSecondArcTriple g M a hn hc.1 hu
  have hlabels := contactSecondArcTriple_labels g M a hn hc.1 hu
  have horder : CyclicContactBoundaryOrder g M a t := Or.inr (Or.inr hlabels)
  have hZt : pointZeroTriples w.center = {t.vertexSet g} := by
    rw [contactSecondArcTriple_support]
    exact hc.2.1
  obtain ⟨r, hr0, hr1, hω, hA, hB, hX⟩ := w.contact_interior_affine M a hn hc
  have hchange := w.contact_boundary_chi_signChanges g M a t horder hc.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine g hn t hZt hc.2.2.1 hchange
      (w.center a) (w.center (a + 1) - w.center a) r 0 1 hω
      ((congrArg w.center hlabels.1).trans hX)
      ((congrArg w.center hlabels.2.1).trans hA)
      ((congrArg w.center hlabels.2.2).trans hB)
      (by linarith) (by norm_num) (by linarith)
  have hε := contact_epsilons_second_arc r hr0 hr1
  have hgaps := contactSecondArcTriple_gaps g M a hn hc.1 hu
  have hdist := contactDistance_bounds hn hc.1
  have hL : 2 ≤ t.leftInterval.leaves := by dsimp only [t]; omega
  have hfac := integer_wall_factor_right_leaf_neg_pos w.center g t hZt hL hgaps.2
  have hgap := contactSecondArcTriple_left_integer_gap w.center g M a hn hc.1 hu hc.2.1
  have hcoeff := contactSecondArc_contracted_coefficient w.center g M a hn hc.1 hu hc.2.1
  have hproper := contactSecondArcTriple_proper g M a hn hc.1 hu
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  rw [dif_pos hproper, hε.1, hε.2, hfac.1, hgap, hcoeff] at hr
  refine ⟨?_, hr.2⟩
  simpa only [contact_boundary_geometric_sign _ g M a t horder, sub_neg_eq_add] using hr.1

/-- The three source root cases exhaust every original physical edge.
No extra endpoint or root-seam exception is needed. -/
theorem contact_signed_response_all_roots (w : WallGerm n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.VertexEdgeAt M a) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(chi (w.curve sPlus) a (a + 1) M : ℤ) +
          (chi (w.curve sMinus) a (a + 1) M : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn =
          d * (treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1)
            (contactHalfRoots M a g).1 (contactHalfSizes_bounds hn hc.1).1.1 *
            treeCoefficient (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1)
              (contactHalfRoots M a g).2 (contactHalfSizes_bounds hn hc.1).2.1)) := by
  by_cases hg : g = a
  · subst g
    simpa only [contactHalfRoots_base, Prod.fst, Prod.snd] using w.contact_base_signed_response M a hn hc
  · by_cases hu : (g - M).val < contactDistance M a
    · simpa only [contactHalfRoots, if_neg hg, if_pos hu, Prod.fst, Prod.snd] using
        w.contact_first_arc_signed_response g M a hn hc hu
    · have hne : (g - M).val ≠ contactDistance M a := by
        intro he
        apply hg
        apply sub_left_injective
        exact ZMod.val_injective n he
      have hs : contactDistance M a < (g - M).val := by omega
      simpa only [contactHalfRoots, if_neg hg, if_neg hu, Prod.fst, Prod.snd] using
        w.contact_second_arc_signed_response g M a hn hc hs

end
end SM.WallGerm
