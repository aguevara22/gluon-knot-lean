namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- At the zero-parameter limit every old corner other than j has its
original turn, including the next corner whose incoming edge is the return. -/
theorem softInsertion_old_turn_zero (P : LabelledTuple n) (j k : ZMod n) (q : Plane)
    (hkj : k ≠ j) : turn (softInsertion P j q 0) (softOldIndex j k) = turn P k := by
  by_cases hk : k = j + 1
  · subst k
    have hi : softOldIndex j (j + 1) - 1 = softNewIndex j := by
      rw [← softNewIndex_next, add_sub_cancel_right]
    rw [turn_det, hi, edge_softInsertion_return, zero_smul, sub_zero,
      edge_softInsertion_old P j (j + 1) q 0 hkj, turn_det, add_sub_cancel_right]
  · have hp : k - 1 ≠ j := by
      intro h
      apply hk
      linear_combination h
    have hs := softOldIndex_next j (k - 1) hp
    rw [sub_add_cancel] at hs
    have hi : softOldIndex j k - 1 = softOldIndex j (k - 1) := by
      rw [hs, add_sub_cancel_right]
    rw [turn_det, hi, edge_softInsertion_old P j (k - 1) q 0 hp,
      edge_softInsertion_old P j k q 0 hkj, turn_det]

/-- Finitely many nonzero old turns persist simultaneously. No genericity
at the duplicate-vertex zero-parameter tuple is assumed. -/
theorem softInsertion_old_turns_persist (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ∀ k : ZMod n, k ≠ j →
      turn (softInsertion P j q ε) (softOldIndex j k) = turn P k := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  apply eventually_all.mpr
  intro k
  by_cases hk : k = j
  · exact Eventually.of_forall (fun _ h => (h hk).elim)
  · have hz : turn (softInsertion P j q 0) (softOldIndex j k) ≠ 0 := by
      rw [softInsertion_old_turn_zero P j k q hk, turn_det]
      exact sign_ne_zero.mpr (g1_turn_nonzero hn hP k)
    have he := ((continuous_softInsertion P j q).continuousAt :
      ContinuousAt (softInsertion P j q) (0 : ℝ)).eventually (chi_locally_constant_of_ne_zero hz)
    filter_upwards [he] with ε hε _
    change turn (softInsertion P j q ε) (softOldIndex j k) =
      turn (softInsertion P j q 0) (softOldIndex j k) at hε
    exact hε.trans (softInsertion_old_turn_zero P j k q hk)

theorem softInsertion_return_tendsto (P : LabelledTuple n) (j : ZMod n) (q : Plane) :
    Tendsto (fun ε : ℝ => edge (softInsertion P j q ε) (softNewIndex j))
      (𝓝 (0 : ℝ)) (𝓝 (edge P j)) := by
  have hc : Continuous (fun ε : ℝ => edge P j - ε • q) := by fun_prop
  simpa only [edge_softInsertion_return, zero_smul, sub_zero] using hc.tendsto 0

/-- The turn and direction-sign clauses of lem:soft-generic on one common
positive interval. The direction limit is softInsertion_return_tendsto. -/
theorem softInsertion_small_turns (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      (∀ k : ZMod n, k ≠ j → turn (softInsertion P j q ε) (softOldIndex j k) = turn P k) ∧
      turn (softInsertion P j q ε) (softOldIndex j j) = -softAttachmentMinus P j q ∧
      turn (softInsertion P j q ε) (softNewIndex j) = -softAttachmentPlus P j q ∧
      SignType.sign (det (edge P (j - 1)) (edge (softInsertion P j q ε) (softNewIndex j))) =
        turn P j ∧
      SignType.sign (det (edge (softInsertion P j q ε) (softNewIndex j)) (edge P (j - 1))) =
        -turn P j := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨δ₁, hδ₁, holds⟩ := Metric.eventually_nhds_iff.mp (softInsertion_old_turns_persist hn hP j q)
  have hT : det (P j - P (j - 1)) (P (j + 1) - P j) ≠ 0 := by
    simpa only [edge, sub_add_cancel] using g1_turn_nonzero hn hP j
  obtain ⟨δ₂, hδ₂, hsign⟩ := softLocal_small_signs (P j) (P (j - 1)) (P (j + 1)) q hT
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro ε hε hεδ
  have hε₁ : dist ε 0 < δ₁ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hε] using
      lt_of_lt_of_le hεδ (min_le_left δ₁ δ₂)
  have hε₂ : |ε| < δ₂ := by
    simpa only [abs_of_pos hε] using lt_of_lt_of_le hεδ (min_le_right δ₁ δ₂)
  have ht := softInsertion_attachment_turns hn P j q ε hε
  have hd : SignType.sign (det (edge P (j - 1))
      (edge (softInsertion P j q ε) (softNewIndex j))) = turn P j := by
    rw [edge_softInsertion_return, turn_det]
    simpa only [softLocalReturn, edge, sub_add_cancel] using (hsign ε hε₂).1
  refine ⟨holds hε₁, ht.1, ht.2, hd, ?_⟩
  rw [det_swap, Left.sign_neg, hd]

end
end SM
