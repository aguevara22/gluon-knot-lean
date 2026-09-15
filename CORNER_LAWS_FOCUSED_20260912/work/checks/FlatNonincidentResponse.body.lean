namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- The nonincident flat response uses the actual center deletion and fused
physical root. Both singleton gaps and the proper span are proved from FlatAt. -/
theorem flat_nonincident_signed_response (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.FlatAt j) (hg : ¬ incident j g) :
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
  obtain ⟨r, hr0, hr1, hω, hA, hM, hB⟩ := strictBetween_flat_affine
    (w.center (j - 1)) (w.center j) (w.center (j + 1)) hf.2.2.2.1
  have hchange := w.flat_boundary_chi_signChanges g j t horder hf.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine g (by have := hf.1; omega) t hZt hf.2.2.1 hchange
      (w.center (j - 1)) (w.center (j + 1) - w.center (j - 1)) 0 r 1 hω
      ((congrArg w.center hlabels.1).trans hA)
      ((congrArg w.center hlabels.2.1).trans hM)
      ((congrArg w.center hlabels.2.2).trans hB)
      (by linarith) (by linarith) (by norm_num)
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

end
end SM.WallGerm
