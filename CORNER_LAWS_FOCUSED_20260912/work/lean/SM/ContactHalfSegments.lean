import SM.ChildRelabel

/-! The closed cut segments, including their endpoints, are actual positive
subsegments of the parent's contact edge, as stated in def:deletion-halves. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem firstHalf_segment_subset {P : LabelledTuple n} {M a : ZMod n}
    (hm : P M ∈ edgeInterior P a) (i : ZMod (firstHalfSize M a)) :
    edgeSegment (firstHalf P M a) i ⊆ edgeSegment P (firstHalfIndex M a i) := by
  intro x hx
  obtain ⟨t, ht0, ht1, ht⟩ := hx
  by_cases hi : i = -1
  · subst i
    rw [firstHalfIndex_last]
    obtain ⟨r, hr0, hr1, hr⟩ := hm
    refine ⟨r * t, mul_nonneg hr0.le ht0, by nlinarith, ?_⟩
    exact ht.trans (edgePoint_firstHalf_cut hr t)
  · exact ⟨t, ht0, ht1, ht.trans (edgePoint_firstHalf P M a hi t)⟩

theorem secondHalf_segment_subset (hn : 3 ≤ n) {M a : ZMod n} (h : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (i : ZMod (secondHalfSize M a)) :
    edgeSegment (secondHalf P M a) i ⊆ edgeSegment P (secondHalfEdgeIndex M a i) := by
  intro x hx
  obtain ⟨t, ht0, ht1, ht⟩ := hx
  by_cases hi : i = 0
  · subst i
    rw [secondHalfEdgeIndex_zero]
    obtain ⟨r, hr0, hr1, hr⟩ := hm
    refine ⟨r + (1 - r) * t, by nlinarith, by nlinarith, ?_⟩
    exact ht.trans (edgePoint_secondHalf_cut hn h hr t)
  · exact ⟨t, ht0, ht1, ht.trans (edgePoint_secondHalf P M a hi t)⟩

end SM
