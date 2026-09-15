import SM.WallSegmentStability

/-! Topological foundations for prop:chambers. All sets below retain the actual
coordinate geometry of Generic; openness alone is not the full source claim. -/

namespace SM

open Filter Topology

variable {n : ℕ}

theorem continuous_vertex (i : ZMod n) :
    Continuous (fun P : LabelledTuple n => P i) := continuous_apply i

theorem continuous_edge (i : ZMod n) : Continuous (fun P : LabelledTuple n => edge P i) :=
  (continuous_vertex (i + 1)).sub (continuous_vertex i)

theorem continuous_area (i j k : ZMod n) :
    Continuous (fun P : LabelledTuple n => det (P j - P i) (P k - P i)) := by
  rw [continuous_iff_continuousAt]
  intro P
  exact continuousAt_det ((continuous_vertex j).continuousAt.sub
    (continuous_vertex i).continuousAt) ((continuous_vertex k).continuousAt.sub
    (continuous_vertex i).continuousAt)

theorem g1_persists [NeZero n] {P : LabelledTuple n} (hP : G1 P) :
    ∀ᶠ Q in 𝓝 P, G1 Q := by
  have hp : ∀ᶠ Q in 𝓝 P, ∀ i j k : ZMod n,
      (i ≠ j ∧ j ≠ k ∧ i ≠ k) → det (Q j - Q i) (Q k - Q i) ≠ 0 := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j =>
      eventually_all.mpr fun k => ?_
    by_cases h : i ≠ j ∧ j ≠ k ∧ i ≠ k
    · have hd := g1_area_ne_zero hP h.1 h.2.1 h.2.2
      exact ((continuous_area i j k).continuousAt.eventually
        (isOpen_compl_singleton.mem_nhds hd)).mono (fun _ ht _ => ht)
    · exact Eventually.of_forall (fun _ ht => (h ht).elim)
  exact hp.mono fun Q hQ i j k hij hjk hik => sign_ne_zero.mpr (hQ i j k ⟨hij, hjk, hik⟩)

theorem isOpen_G1 [NeZero n] : IsOpen {P : LabelledTuple n | G1 P} :=
  isOpen_iff_mem_nhds.mpr fun _ hP => g1_persists hP

theorem edgeInterior_subset_edgeSegment (P : LabelledTuple n) (i : ZMod n) :
    edgeInterior P i ⊆ edgeSegment P i := by
  rintro x ⟨s, hs0, hs1, hx⟩
  exact ⟨s, hs0.le, hs1.le, hx⟩

theorem g1_common_interiors_remote [NeZero n] [Nontrivial (ZMod n)]
    (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P) {i j : ZMod n} (hne : i ≠ j)
    {x : Plane} (hi : x ∈ edgeInterior P i) (hj : x ∈ edgeInterior P j) : remote i j := by
  intro hadj
  have hc : x ∈ edgeSegment P i ∩ edgeSegment P j :=
    ⟨edgeInterior_subset_edgeSegment P i hi, edgeInterior_subset_edgeSegment P j hj⟩
  rcases g1_adjacent_intersection hn hP hne hadj with ⟨he, hset⟩ | ⟨he, hset⟩
  · rw [hset] at hc
    have hx : x = P j := hc
    obtain ⟨t, ht0, _, ht⟩ := hj
    have hparam : t = 0 := edgePoint_injective (g1_edge_ne_zero hn hP j)
      (ht.symm.trans (hx.trans (edgePoint_zero P j).symm))
    exact (ne_of_gt ht0) hparam
  · rw [hset] at hc
    have hx : x = P i := hc
    obtain ⟨s, hs0, _, hs⟩ := hi
    have hparam : s = 0 := edgePoint_injective (g1_edge_ne_zero hn hP i)
      (hs.symm.trans (hx.trans (edgePoint_zero P i).symm))
    exact (ne_of_gt hs0) hparam

/-- A common point of three actual closed segments. -/
def ClosedTripleMeet (P : LabelledTuple n) (i j k : ZMod n) : Prop :=
  ∃ x : Plane, x ∈ edgeSegment P i ∧ x ∈ edgeSegment P j ∧ x ∈ edgeSegment P k

/-- Under G1, G2 can be tested by pairwise remote closed segments. -/
theorem g2_iff_no_remote_closed_triples [NeZero n] [Nontrivial (ZMod n)]
    (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P) :
    G2 P ↔ ∀ i j k, remote i j → remote j k → remote i k → ¬ ClosedTripleMeet P i j k := by
  constructor
  · intro hG i j k hij hjk hik
    rintro ⟨x, hi, hj, hk⟩
    obtain ⟨hii, hji, _⟩ := g1_remote_meeting hP hij hi hj
    obtain ⟨_, hki, _⟩ := g1_remote_meeting hP hik hi hk
    exact hG ⟨i, j, k, x, (remote_endpoints i j hij).1.symm,
      (remote_endpoints j k hjk).1.symm, (remote_endpoints i k hik).1.symm, hii, hji, hki⟩
  · intro hG
    rintro ⟨i, j, k, x, hij, hjk, hik, hi, hj, hk⟩
    exact hG i j k (g1_common_interiors_remote hn hP hij hi hj)
      (g1_common_interiors_remote hn hP hjk hj hk)
      (g1_common_interiors_remote hn hP hik hi hk)
      ⟨x, edgeInterior_subset_edgeSegment P i hi, edgeInterior_subset_edgeSegment P j hj,
        edgeInterior_subset_edgeSegment P k hk⟩

theorem isClosed_closedTripleMeet (i j k : ZMod n) :
    IsClosed {P : LabelledTuple n | ClosedTripleMeet P i j k} := by
  let E : Set (LabelledTuple n × (unitInterval × unitInterval × unitInterval)) :=
    {p | edgePoint p.1 i (p.2.1 : ℝ) = edgePoint p.1 j (p.2.2.1 : ℝ) ∧
      edgePoint p.1 i (p.2.1 : ℝ) = edgePoint p.1 k (p.2.2.2 : ℝ)}
  have hE : IsClosed E := by
    change IsClosed ({p : LabelledTuple n × (unitInterval × unitInterval × unitInterval) |
        edgePoint p.1 i (p.2.1 : ℝ) =
        edgePoint p.1 j (p.2.2.1 : ℝ)} ∩
      {p : LabelledTuple n × (unitInterval × unitInterval × unitInterval) |
        edgePoint p.1 i (p.2.1 : ℝ) = edgePoint p.1 k (p.2.2.2 : ℝ)})
    apply IsClosed.inter <;> apply isClosed_eq <;> dsimp [edgePoint, edge] <;> fun_prop
  have hproj := isClosedMap_fst_of_compactSpace E hE
  convert hproj using 1
  ext P
  constructor
  · rintro ⟨x, ⟨s, hs0, hs1, hs⟩, ⟨r, hr0, hr1, hr⟩, ⟨t, ht0, ht1, ht⟩⟩
    exact ⟨(P, (⟨s, hs0, hs1⟩, ⟨r, hr0, hr1⟩, ⟨t, ht0, ht1⟩)),
      ⟨hs.symm.trans hr, hs.symm.trans ht⟩, rfl⟩
  · rintro ⟨⟨P', s, r, t⟩, ⟨heq, heq'⟩, hP⟩
    dsimp at hP
    subst P'
    exact ⟨edgePoint P i s, ⟨s, s.property.1, s.property.2, rfl⟩,
      ⟨r, r.property.1, r.property.2, heq⟩, ⟨t, t.property.1, t.property.2, heq'⟩⟩

theorem generic_persists (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    ∀ᶠ Q in 𝓝 P, Generic Q := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hcentral := (g2_iff_no_remote_closed_triples hn hP.1).mp hP.2
  have htriples : ∀ᶠ Q in 𝓝 P, ∀ i j k : ZMod n,
      (remote i j ∧ remote j k ∧ remote i k) → ¬ ClosedTripleMeet Q i j k := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j =>
      eventually_all.mpr fun k => ?_
    by_cases hr : remote i j ∧ remote j k ∧ remote i k
    · have he : ∀ᶠ Q in 𝓝 P, ¬ ClosedTripleMeet Q i j k :=
        (isClosed_closedTripleMeet i j k).isOpen_compl.mem_nhds
          (hcentral i j k hr.1 hr.2.1 hr.2.2)
      exact he.mono (fun _ ht _ => ht)
    · exact Eventually.of_forall (fun _ ht => (hr ht).elim)
  filter_upwards [g1_persists hP.1, htriples] with Q hQ hT
  exact ⟨hQ, (g2_iff_no_remote_closed_triples hn hQ).mpr
    (fun i j k hij hjk hik => hT i j k ⟨hij, hjk, hik⟩)⟩

theorem isOpen_Generic (hn : 3 ≤ n) : IsOpen {P : LabelledTuple n | Generic P} :=
  isOpen_iff_mem_nhds.mpr fun _ hP => generic_persists hn hP

end SM
