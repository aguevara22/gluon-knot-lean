namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- Every remote parent pair keeps its closed-segment intersection status.
The disjoint branch permits parallel directions and needs only compactness. -/
theorem soft_parent_pair_intersection_persists (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j k l : ZMod n) (q : Plane) (hr : remote k l) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      (edgeSegment (softInsertion P j q ε) (softParentEdge j k) ∩
        edgeSegment (softInsertion P j q ε) (softParentEdge j l)).Nonempty ↔
      (edgeSegment P k ∩ edgeSegment P l).Nonempty := by
  by_cases hc : IsCrossing P {k, l}
  · have he := softParent_crossing_parameters_persist hn hP j k l q hc
    filter_upwards [he] with ε hε
    exact iff_of_true ((isCrossing_pair _ _ _ (softParentEdge_remote j k l hr)).mp hε.2.2.2.2)
      ((isCrossing_pair P k l hr).mp hc)
  · have hd : ¬ segmentsMeet (P k) (P l) (edge P k) (edge P l) := by
      intro hm
      exact hc ((isCrossing_pair P k l hr).mpr ((segmentsMeet_edges_iff P k l).mp hm))
    have hd0 : ¬ segmentsMeet (softInsertion P j q 0 (softParentEdge j k))
        (softInsertion P j q 0 (softParentEdge j l))
        (edge (softInsertion P j q 0) (softParentEdge j k))
        (edge (softInsertion P j q 0) (softParentEdge j l)) := by
      simpa only [softInsertion_parent_zero, edge_softInsertion_parent_zero] using hd
    have he := disjoint_segments_persist
      (continuous_softParent_vertex P j k q).continuousAt
      (continuous_softParent_vertex P j l q).continuousAt
      (continuous_softParent_edge P j k q).continuousAt
      (continuous_softParent_edge P j l q).continuousAt hd0
    filter_upwards [he] with ε hε
    exact iff_of_false
      (fun hm => hε ((segmentsMeet_edges_iff _ _ _).mpr hm))
      (fun hm => hd ((segmentsMeet_edges_iff P k l).mpr hm))

theorem soft_parent_crossing_pair_persists (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j k l : ZMod n) (q : Plane) (hr : remote k l) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      IsCrossing (softInsertion P j q ε) {softParentEdge j k, softParentEdge j l} ↔
        IsCrossing P {k, l} := by
  filter_upwards [soft_parent_pair_intersection_persists hn hP j k l q hr] with ε hε
  rw [isCrossing_pair _ _ _ (softParentEdge_remote j k l hr), isCrossing_pair P k l hr]
  exact hε

theorem soft_all_remote_pairs_persist (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ∀ k l : ZMod n, remote k l →
      (IsCrossing (softInsertion P j q ε) {softParentEdge j k, softParentEdge j l} ↔
        IsCrossing P {k, l}) := by
  apply eventually_all.mpr
  intro k
  apply eventually_all.mpr
  intro l
  by_cases hr : remote k l
  · exact (soft_parent_crossing_pair_persists hn hP j k l q hr).mono (fun _ h _ => h)
  · exact Eventually.of_forall (fun _ h => (hr h).elim)

theorem soft_small_remote_pairs (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    ∃ δ > 0, ∀ ε : ℝ, |ε| < δ → ∀ k l : ZMod n, remote k l →
      (IsCrossing (softInsertion P j q ε) {softParentEdge j k, softParentEdge j l} ↔
        IsCrossing P {k, l}) := by
  obtain ⟨δ, hδ, hmem⟩ := Metric.eventually_nhds_iff.mp
    (soft_all_remote_pairs_persist hn hP j q)
  exact ⟨δ, hδ, fun ε hε => hmem (by simpa only [Real.dist_eq, sub_zero] using hε)⟩

/-- Parent G2 supplies strict separation of distinct crossing visits on
one edge. Their actual transported parameters therefore retain their order. -/
theorem soft_inherited_parameter_order (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j k l m : ZMod n) (q : Plane) (hlm : l ≠ m)
    (hkl : IsCrossing P {k, l}) (hkm : IsCrossing P {k, m}) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      (edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) <
        edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j m) ↔
      edgeParameter P k l < edgeParameter P k m) := by
  have hl := continuousAt_softParentParameter P j k l q
    (crossing_edgeParameter_det_ne_zero hn hP.1 hkl)
  have hm := continuousAt_softParentParameter P j k m q
    (crossing_edgeParameter_det_ne_zero hn hP.1 hkm)
  have hne := generic_edgeParameters_ne hn hP hlm hkl hkm
  have he := continuousAt_preserves_parameter_order hl hm
    (by simpa only [softParentParameter_zero] using hne)
  simpa only [softParentParameter_zero] using he

/-- A single neighborhood preserves every inherited comparison, including
the identical-visit case. Child Generic is not assumed. -/
theorem soft_all_inherited_orders_persist (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ∀ k l m : ZMod n,
      IsCrossing P {k, l} → IsCrossing P {k, m} →
      (edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) <
        edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j m) ↔
      edgeParameter P k l < edgeParameter P k m) := by
  apply eventually_all.mpr
  intro k
  apply eventually_all.mpr
  intro l
  apply eventually_all.mpr
  intro m
  by_cases hkl : IsCrossing P {k, l}
  · by_cases hkm : IsCrossing P {k, m}
    · by_cases hlm : l = m
      · subst m
        exact Eventually.of_forall (fun _ _ _ => by simp only [lt_self_iff_false])
      · exact (soft_inherited_parameter_order hn hP j k l m q hlm hkl hkm).mono
          (fun _ h _ _ => h)
    · exact Eventually.of_forall (fun _ _ h => (hkm h).elim)
  · exact Eventually.of_forall (fun _ h _ => (hkl h).elim)

end
end SM
