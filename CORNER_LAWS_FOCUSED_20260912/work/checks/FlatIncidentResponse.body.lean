namespace SM.WallGerm

noncomputable section
variable {m : ℕ}
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Assemble the incoming incident response from actual affine, gap and
deletion-root identities. The sign is fixed before the independent side points. -/
theorem flat_incoming_signed_response (w : WallGerm (m + 4)) (j : ZMod (m + 4))
    (hf : w.FlatAt j) :
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
  obtain ⟨r, hr0, hr1, hω, hA, hM, hB⟩ := strictBetween_flat_affine
    (w.center (j - 1)) (w.center j) (w.center (j + 1)) hf.2.2.2.1
  have hchange := w.flat_boundary_chi_signChanges (j - 1) j t horder hf.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine (j - 1) (by omega) t hZt hf.2.2.1 hchange
      (w.center (j - 1)) (w.center (j + 1) - w.center (j - 1)) r 1 0 hω
      ((congrArg w.center hlabels.1).trans hM)
      ((congrArg w.center hlabels.2.1).trans hB)
      ((congrArg w.center hlabels.2.2).trans hA)
      (by linarith) (by norm_num) (by linarith)
  have hintervals := incomingFlatTriple_intervals (n := m + 4) (by omega)
  have hfull : ¬ t.spanInterval ≠ fullBoundaryInterval (by omega) := not_ne_iff.mpr hintervals.1
  have hε := flat_epsilons_incoming r hr0 hr1
  have hfactors := integer_wall_factor_left_leaf w.center (j - 1) t hZt
    hintervals.2.1 (by change 2 ≤ m + 2; omega)
  have hgap : criticalIntervalIntegerOutput w.center (j - 1) t hZt t.rightInterval t.rightInterval_excludes_span =
      treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
        (fusionIndex j (j - 1)) (by omega) := incoming_flat_integer_gap w.center j hf.2.1
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  rw [dif_neg hfull, hε.1, hε.2, hfactors.1, hfactors.2, zero_add, hgap] at hr
  refine ⟨?_, hr.2⟩
  simpa only [flat_boundary_geometric_sign _ (j - 1) j t horder, sub_neg_eq_add] using hr.1

/-- Assemble the outgoing incident response from actual affine, gap and
deletion-root identities. The sign is fixed before the independent side points. -/
theorem flat_outgoing_signed_response (w : WallGerm (m + 4)) (j : ZMod (m + 4))
    (hf : w.FlatAt j) :
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
  obtain ⟨r, hr0, hr1, hω, hA, hM, hB⟩ := strictBetween_flat_affine
    (w.center (j - 1)) (w.center j) (w.center (j + 1)) hf.2.2.2.1
  have hchange := w.flat_boundary_chi_signChanges j j t horder hf.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine j (by omega) t hZt hf.2.2.1 hchange
      (w.center (j - 1)) (w.center (j + 1) - w.center (j - 1)) 1 0 r hω
      ((congrArg w.center hlabels.1).trans hB)
      ((congrArg w.center hlabels.2.1).trans hA)
      ((congrArg w.center hlabels.2.2).trans hM)
      (by norm_num) (by linarith) (by linarith)
  have hintervals := outgoingFlatTriple_intervals (n := m + 4) (by omega)
  have hfull : ¬ t.spanInterval ≠ fullBoundaryInterval (by omega) := not_ne_iff.mpr hintervals.1
  have hε := flat_epsilons_outgoing r hr0 hr1
  have hfactors := integer_wall_factor_right_leaf w.center j t hZt
    (by change 2 ≤ m + 2; omega) hintervals.2.2
  have hgap : criticalIntervalIntegerOutput w.center j t hZt t.leftInterval t.leftInterval_excludes_span =
      treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
        (fusionIndex j j) (by omega) := outgoing_flat_integer_gap w.center j hf.2.1
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  rw [dif_neg hfull, hε.1, hε.2, hfactors.1, hfactors.2, zero_add, hgap] at hr
  refine ⟨?_, hr.2⟩
  simpa only [flat_boundary_geometric_sign _ j j t horder, sub_neg_eq_add] using hr.1

/-- Both incident physical roots, with no assumption about which time side
is the source right side. That final turn-side normalization remains separate. -/
theorem flat_incident_signed_response (w : WallGerm (m + 4)) (j g : ZMod (m + 4))
    (hf : w.FlatAt j) (hg : incident j g) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g (by omega) -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g (by omega) =
          d * treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j g) (by omega)) := by
  rcases hg with h | h
  · subst g
    exact w.flat_incoming_signed_response j hf
  · subst g
    exact w.flat_outgoing_signed_response j hf

end
end SM.WallGerm
