namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- There is no parent edge strictly between a predecessor and its successor
in the cyclic numerical edge order. This includes the residue-zero cut. -/
theorem soft_parent_no_cyclic_edge_between (j k : ZMod n) :
    ¬ (((j - 1).val < k.val ∧ k.val < j.val) ∨
      (k.val < j.val ∧ j.val < (j - 1).val) ∨
      (j.val < (j - 1).val ∧ (j - 1).val < k.val)) := by
  have hk := ZMod.val_lt k
  have hj := ZMod.val_lt j
  by_cases hz : j = 0
  · subst j
    have hv : ((0 : ZMod n) - 1).val = n - 1 := canonicalPosition_val_zero
    rw [hv, ZMod.val_zero]
    omega
  · have hv : (j - 1).val = j.val - 1 := canonicalPosition_val_nonzero j hz
    rw [hv]
    omega

/-- Every point on a corresponding parent edge is outside the short inserted
arc if it precedes the incoming endpoint on that edge and follows the return
endpoint on that edge. No visit or chamber premise is hidden here. -/
theorem soft_parent_traversal_arc_empty (hn : 3 ≤ n) (j k : ZMod n)
    (a x b : TraversalPoint (n + 1))
    (ha : a.1 = softParentEdge j (j - 1)) (hx : x.1 = softParentEdge j k)
    (hb : b.1 = softParentEdge j j)
    (hin : k = j - 1 → x.2.val ≤ a.2.val)
    (hout : k = j → b.2.val ≤ x.2.val) : ¬ traversalBetween a x b := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hpj : j - 1 ≠ j := prev_ne_self j
  intro h
  unfold traversalBetween at h
  simp only [traversalKey_lt_iff, ha, hx, hb, softParentEdge_val_lt_iff,
    (softParentEdge_injective j).eq_iff] at h
  by_cases hkprev : k = j - 1
  · have hpar := hin hkprev
    subst k
    simp only [lt_self_iff_false, true_and, false_or, hpj, Ne.symm hpj,
      false_and, or_false] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · omega
    · linarith
  · by_cases hkj : k = j
    · have hpar := hout hkj
      subst k
      simp only [lt_self_iff_false, true_and, false_or, hpj, Ne.symm hpj,
        false_and, or_false] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · linarith
      · linarith
      · omega
    · simp only [hkprev, Ne.symm hkprev, hkj, Ne.symm hkj, hpj, Ne.symm hpj,
        false_and, or_false] at h
      exact soft_parent_no_cyclic_edge_between j k h

end
end SM
