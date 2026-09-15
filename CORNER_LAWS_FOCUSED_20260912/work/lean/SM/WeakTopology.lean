import SM.WeakGeometry

/-! Openness of the full weak locus, including disjoint collinear remote pairs.
Polygonal connectedness and the Euclidean-ball clause are assembled separately. -/

namespace SM

open Filter Topology

variable {n : ℕ}

theorem vertex_on_edge_iff_meet (P : LabelledTuple n) (k i : ZMod n) :
    P k ∈ edgeSegment P i ↔ segmentsMeet (P k) (P i) 0 (edge P i) := by
  constructor
  · rintro ⟨r, hr0, hr1, hr⟩
    exact ⟨0, r, le_rfl, by norm_num, hr0, hr1, by simpa [edgePoint] using hr⟩
  · rintro ⟨s, r, _, _, hr0, hr1, heq⟩
    exact ⟨r, hr0, hr1, by simpa [edgePoint] using heq⟩

theorem segmentsMeet_edges_iff (P : LabelledTuple n) (i j : ZMod n) :
    segmentsMeet (P i) (P j) (edge P i) (edge P j) ↔
      (edgeSegment P i ∩ edgeSegment P j).Nonempty :=
  segmentsMeet_iff (P i) (P j) (edge P i) (edge P j)

theorem vertex_exclusion_persists [NeZero n] {P : LabelledTuple n}
    (hP : ∀ k i, ¬ incident k i → P k ∉ edgeSegment P i) :
    ∀ᶠ Q in 𝓝 P, ∀ k i, ¬ incident k i → Q k ∉ edgeSegment Q i := by
  refine eventually_all.mpr fun k => eventually_all.mpr fun i => ?_
  by_cases hi : ¬ incident k i
  · have hnot : ¬ segmentsMeet (P k) (P i) 0 (edge P i) :=
      fun h => hP k i hi ((vertex_on_edge_iff_meet P k i).mpr h)
    have he := disjoint_segments_persist (continuous_vertex k).continuousAt
      (continuous_vertex i).continuousAt (continuousAt_const (y := (0 : Plane)))
      (continuous_edge i).continuousAt hnot
    exact he.mono fun Q hQ _ hx => hQ ((vertex_on_edge_iff_meet Q k i).mp hx)
  · exact Eventually.of_forall (fun _ ht => (hi ht).elim)

theorem weak_remote_regular_persists [NeZero n] {P : LabelledTuple n} (hP : WeakGeneric P) :
    ∀ᶠ Q in 𝓝 P, ∀ i j, remote i j →
      (∀ x, x ∈ edgeSegment Q i → x ∈ edgeSegment Q j → det (edge Q i) (edge Q j) ≠ 0) ∧
      (∀ x y, x ∈ edgeSegment Q i → x ∈ edgeSegment Q j →
        y ∈ edgeSegment Q i → y ∈ edgeSegment Q j → x = y) := by
  refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
  by_cases hr : remote i j
  · by_cases hm : (edgeSegment P i ∩ edgeSegment P j).Nonempty
    · obtain ⟨x, hi, hj⟩ := hm
      have hd := (hP.2.2.2.1 i j hr).1 x hi hj
      have he := continuousAt_preserves_transversality (continuous_edge i).continuousAt
        (continuous_edge j).continuousAt hd
      exact he.mono fun Q hQ _ => ⟨fun _ _ _ => hQ,
        fun _ _ hi hj hi' hj' => transverse_segments_unique hQ hi hj hi' hj'⟩
    · have hd : ¬ segmentsMeet (P i) (P j) (edge P i) (edge P j) :=
        fun h => hm ((segmentsMeet_edges_iff P i j).mp h)
      have he := disjoint_segments_persist (continuous_vertex i).continuousAt
        (continuous_vertex j).continuousAt (continuous_edge i).continuousAt
        (continuous_edge j).continuousAt hd
      filter_upwards [he] with Q hQ _
      have hnone : ¬ (edgeSegment Q i ∩ edgeSegment Q j).Nonempty :=
        fun h => hQ ((segmentsMeet_edges_iff Q i j).mpr h)
      exact ⟨fun x hi hj => (hnone ⟨x, hi, hj⟩).elim,
        fun x _ hi hj _ _ => (hnone ⟨x, hi, hj⟩).elim⟩
  · exact Eventually.of_forall (fun _ ht => (hr ht).elim)

theorem weak_generic_persists [NeZero n] {P : LabelledTuple n} (hP : WeakGeneric P) :
    ∀ᶠ Q in 𝓝 P, WeakGeneric Q := by
  have he : ∀ᶠ Q in 𝓝 P, ∀ i, edge Q i ≠ 0 :=
    eventually_all.mpr fun i => (continuous_edge i).continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds (hP.1 i))
  have ht : ∀ᶠ Q in 𝓝 P, ∀ i, turn Q i ≠ 0 := by
    refine eventually_all.mpr fun i => ?_
    have hd : det (edge P (i - 1)) (edge P i) ≠ 0 :=
      sign_ne_zero.mp (by simpa only [turn_det] using hP.2.1 i)
    exact (continuousAt_preserves_transversality (continuous_edge (i - 1)).continuousAt
      (continuous_edge i).continuousAt hd).mono fun Q hQ => by
        rw [turn_det]
        exact sign_ne_zero.mpr hQ
  have hv := vertex_exclusion_persists hP.2.2.1
  have hr := weak_remote_regular_persists hP
  have hcentral := (weak_base_g2_iff_no_remote_closed_triples hP.1 hP.2.1 hP.2.2.1).mp hP.2.2.2.2
  have hc : ∀ᶠ Q in 𝓝 P, ∀ i j k,
      (remote i j ∧ remote j k ∧ remote i k) → ¬ ClosedTripleMeet Q i j k := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun k => ?_
    by_cases hremote : remote i j ∧ remote j k ∧ remote i k
    · have hnot : ∀ᶠ Q in 𝓝 P, ¬ ClosedTripleMeet Q i j k :=
        (isClosed_closedTripleMeet i j k).isOpen_compl.mem_nhds
          (hcentral i j k hremote.1 hremote.2.1 hremote.2.2)
      exact hnot.mono (fun _ ht _ => ht)
    · exact Eventually.of_forall (fun _ ht => (hremote ht).elim)
  filter_upwards [he, ht, hv, hr, hc] with Q heQ htQ hvQ hrQ hcQ
  exact ⟨heQ, htQ, hvQ, hrQ, (weak_base_g2_iff_no_remote_closed_triples heQ htQ hvQ).mpr
    (fun i j k hij hjk hik => hcQ i j k ⟨hij, hjk, hik⟩)⟩

theorem isOpen_WeakGeneric [NeZero n] : IsOpen (weakLocus n) :=
  isOpen_iff_mem_nhds.mpr fun _ hP => weak_generic_persists hP

end SM
