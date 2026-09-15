namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- The shrinking soft segment is disjoint from every parent edge not
incident to the attachment vertex. Compact closed-segment stability applies
even though the soft direction is zero at the limiting parameter. -/
theorem softEdge_disjoint_old_persists (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j k : ZMod n) (q : Plane) (hkj : k ≠ j) (hkp : k ≠ j - 1) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      Disjoint (edgeSegment (softInsertion P j q ε) (softOldIndex j j))
        (edgeSegment (softInsertion P j q ε) (softOldIndex j k)) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hjnext : j ≠ k + 1 := by
    intro h
    apply hkp
    linear_combination -h
  have hoff := g1_vertex_not_mem_edge hP k j (next_ne_self k).symm (Ne.symm hkj) hjnext
  have hd : ¬ segmentsMeet (P j) (P k) ((0 : ℝ) • q) (edge P k) := by
    rintro ⟨s, t, _, _, ht0, ht1, he⟩
    apply hoff
    refine ⟨t, ht0, ht1, ?_⟩
    simpa only [zero_smul, smul_zero, add_zero, edgePoint] using he
  have he := disjoint_segments_persist
    (a := fun _ : ℝ => P j) (b := fun _ : ℝ => P k)
    (u := fun ε : ℝ => ε • q) (v := fun _ : ℝ => edge P k)
    continuousAt_const continuousAt_const (by fun_prop) continuousAt_const hd
  filter_upwards [he] with ε hε
  apply Set.disjoint_left.mpr
  rintro x ⟨s, hs0, hs1, hs⟩ ⟨t, ht0, ht1, ht⟩
  apply hε
  refine ⟨s, t, hs0, hs1, ht0, ht1, ?_⟩
  simpa only [edgePoint, softInsertion_old, edge_softInsertion_soft,
    edge_softInsertion_old P j k q ε hkj] using hs.symm.trans ht

theorem softEdge_disjoint_all_old_persists (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ∀ k : ZMod n, k ≠ j → k ≠ j - 1 →
      Disjoint (edgeSegment (softInsertion P j q ε) (softOldIndex j j))
        (edgeSegment (softInsertion P j q ε) (softOldIndex j k)) := by
  apply eventually_all.mpr
  intro k
  by_cases hk : k = j
  · exact Eventually.of_forall (fun _ h _ => (h hk).elim)
  · by_cases hp : k = j - 1
    · exact Eventually.of_forall (fun _ _ h => (h hp).elim)
    · exact (softEdge_disjoint_old_persists hn hP j k q hk hp).mono (fun _ h _ _ => h)

/-- The complete soft-edge contact clause: its only contacts with other
edges are precisely the two incident endpoints, on one positive interval.
The exclusion quantifies over every enlarged edge, using exhaustive labels. -/
theorem softEdge_only_incident_contacts (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      edgeSegment (softInsertion P j q ε) (softOldIndex j j) ∩
        edgeSegment (softInsertion P j q ε) (softOldIndex j (j - 1)) = {P j} ∧
      edgeSegment (softInsertion P j q ε) (softOldIndex j j) ∩
        edgeSegment (softInsertion P j q ε) (softNewIndex j) = {P j + ε • q} ∧
      ∀ a : ZMod (n + 1), a ≠ softOldIndex j j → a ≠ softOldIndex j (j - 1) →
        a ≠ softNewIndex j →
        Disjoint (edgeSegment (softInsertion P j q ε) (softOldIndex j j))
          (edgeSegment (softInsertion P j q ε) a) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  haveI : Fact (1 < n + 1) := ⟨by omega⟩
  obtain ⟨δ₁, hδ₁, hdisjoint⟩ := Metric.eventually_nhds_iff.mp
    (softEdge_disjoint_all_old_persists hn hP j q)
  obtain ⟨δ₂, hδ₂, hG1⟩ := softInsertion_small_G1 hP j q hq
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro ε hε hεδ
  have hε₁ : dist ε 0 < δ₁ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hε] using
      lt_of_lt_of_le hεδ (min_le_left δ₁ δ₂)
  have hg := hG1 ε hε (lt_of_lt_of_le hεδ (min_le_right δ₁ δ₂))
  have hi := g1_successive_intersection (by omega : 3 ≤ n + 1) hg (softOldIndex j (j - 1))
  have hs := softOldIndex_next j (j - 1) (prev_ne_self j)
  rw [sub_add_cancel] at hs
  rw [← hs, softInsertion_old] at hi
  have hr := g1_successive_intersection (by omega : 3 ≤ n + 1) hg (softOldIndex j j)
  rw [softOldIndex_attachment_next, softInsertion_new] at hr
  refine ⟨?_, hr, ?_⟩
  · simpa only [Set.inter_comm] using hi
  · intro a ha hp hnew
    rcases soft_indices_exhaust j a with he | ⟨k, rfl⟩
    · exact (hnew he).elim
    · exact hdisjoint hε₁ k (fun h => ha (congrArg (softOldIndex j) h))
        (fun h => hp (congrArg (softOldIndex j) h))

end
end SM
