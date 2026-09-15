import SM.Segment

/-! Full geometric consequences of SM (G1).
Source wording 'two adjacent edges' means two distinct edges. The source's
index relation also admits an edge as adjacent to itself; that self-pair is
not a pair of distinct edges and is not asserted to have singleton intersection.
This reading is explicitly recorded for independent source review. -/

namespace SM

variable {n : ℕ}

theorem edgePoint_zero (P : LabelledTuple n) (i : ZMod n) :
    edgePoint P i 0 = P i := by simp [edgePoint]

theorem edgePoint_one (P : LabelledTuple n) (i : ZMod n) :
    edgePoint P i 1 = P (i + 1) := by simp [edgePoint, edge]

theorem g1_successive_intersection [NeZero n] [Nontrivial (ZMod n)]
    (hn : 3 ≤ n) {P : LabelledTuple n} (h : G1 P) (i : ZMod n) :
    edgeSegment P i ∩ edgeSegment P (i + 1) = {P (i + 1)} := by
  have hd : det (edge P i) (edge P (i + 1)) ≠ 0 := by
    simpa only [add_sub_cancel_right] using g1_turn_nonzero hn h (i + 1)
  have hbase : edgePoint P i 1 = edgePoint P (i + 1) 0 := by
    rw [edgePoint_one, edgePoint_zero]
  ext x
  constructor
  · rintro ⟨⟨s, _, _, hs⟩, ⟨t, _, _, ht⟩⟩
    have hp := intersection_parameters_unique hd (hs.symm.trans ht) hbase
    change x = P (i + 1)
    rw [hs, hp.1, edgePoint_one]
  · intro hx
    have hx' : x = P (i + 1) := hx
    subst x
    exact ⟨⟨1, by norm_num, le_rfl, (edgePoint_one P i).symm⟩,
      ⟨0, le_rfl, by norm_num, (edgePoint_zero P (i + 1)).symm⟩⟩

theorem adjacent_distinct_cases {i j : ZMod n} (hne : i ≠ j) (h : adjacent i j) :
    j = i + 1 ∨ i = j + 1 := by
  rcases h with hneg | hzero | hpos
  · right
    linear_combination -hneg
  · exact (hne (sub_eq_zero.mp hzero).symm).elim
  · left
    linear_combination hpos

theorem g1_adjacent_intersection [NeZero n] [Nontrivial (ZMod n)]
    (hn : 3 ≤ n) {P : LabelledTuple n} (h : G1 P)
    {i j : ZMod n} (hne : i ≠ j) (hadj : adjacent i j) :
    (j = i + 1 ∧ edgeSegment P i ∩ edgeSegment P j = {P j}) ∨
    (i = j + 1 ∧ edgeSegment P i ∩ edgeSegment P j = {P i}) := by
  rcases adjacent_distinct_cases hne hadj with he | he
  · left
    refine ⟨he, ?_⟩
    subst j
    exact g1_successive_intersection hn h i
  · right
    refine ⟨he, ?_⟩
    subst i
    rw [Set.inter_comm]
    exact g1_successive_intersection hn h j

theorem g1_remote_meeting [Nontrivial (ZMod n)]
    {P : LabelledTuple n} (h : G1 P) {i j : ZMod n} (hr : remote i j)
    {x : Plane} (hxi : x ∈ edgeSegment P i) (hxj : x ∈ edgeSegment P j) :
    x ∈ edgeInterior P i ∧ x ∈ edgeInterior P j ∧
    det (edge P i) (edge P j) ≠ 0 ∧
    ∀ y, y ∈ edgeSegment P i → y ∈ edgeSegment P j → y = x := by
  obtain ⟨s, hs0, hs1, hs⟩ := hxi
  obtain ⟨t, ht0, ht1, ht⟩ := hxj
  have heq := hs.symm.trans ht
  have hd := g1_remote_intersection_det h hr heq
  obtain ⟨hs0', hs1', ht0', ht1'⟩ :=
    g1_remote_parameters_interior h hr hs0 hs1 ht0 ht1 heq
  refine ⟨⟨s, hs0', hs1', hs⟩, ⟨t, ht0', ht1', ht⟩, hd, ?_⟩
  intro y hyi hyj
  obtain ⟨s', _, _, hs'⟩ := hyi
  obtain ⟨t', _, _, ht'⟩ := hyj
  have hp := intersection_parameters_unique hd (hs'.symm.trans ht') heq
  rw [hs', hp.1, ← hs]

theorem g1_remote_dichotomy [Nontrivial (ZMod n)]
    {P : LabelledTuple n} (h : G1 P) {i j : ZMod n} (hr : remote i j) :
    Disjoint (edgeSegment P i) (edgeSegment P j) ∨
    ∃ x, edgeSegment P i ∩ edgeSegment P j = {x} ∧
      x ∈ edgeInterior P i ∧ x ∈ edgeInterior P j ∧
      IndependentPair (edge P i) (edge P j) := by
  classical
  by_cases hex : ∃ x, x ∈ edgeSegment P i ∧ x ∈ edgeSegment P j
  · obtain ⟨x, hxi, hxj⟩ := hex
    obtain ⟨hii, hij, hd, huniq⟩ := g1_remote_meeting h hr hxi hxj
    right
    refine ⟨x, ?_, hii, hij, independent_of_det_ne_zero hd⟩
    ext y
    constructor
    · rintro ⟨hyi, hyj⟩
      exact huniq y hyi hyj
    · intro hy
      have hy' : y = x := hy
      subst y
      exact ⟨hxi, hxj⟩
  · left
    exact Set.disjoint_left.mpr (fun x hxi hxj => hex ⟨x, hxi, hxj⟩)

/-- Every clause of SM lem:g1. Linear independence is expressed by its exact
two-vector definition (all zero linear combinations have zero coefficients).
The source's distinct-adjacent-edge reading is explicit in clause (iv). -/
theorem g1 (hn : 3 ≤ n) (P : LabelledTuple n) (h : G1 P) :
    Function.Injective P ∧
    (∀ i, edge P i ≠ 0) ∧
    (∀ i, turn P i = 1 ∨ turn P i = -1) ∧
    (∀ i, IndependentPair (edge P (i - 1)) (edge P i)) ∧
    (∀ i (t : ℝ), edge P i ≠ t • edge P (i - 1)) ∧
    (∀ i k, k ≠ i → k ≠ i + 1 → ∀ t : ℝ, P k ≠ edgePoint P i t) ∧
    (∀ i k, k ≠ i → k ≠ i + 1 → P k ∉ edgeSegment P i) ∧
    (∀ i j, i ≠ j → adjacent i j →
      (j = i + 1 ∧ edgeSegment P i ∩ edgeSegment P j = {P j}) ∨
      (i = j + 1 ∧ edgeSegment P i ∩ edgeSegment P j = {P i})) ∧
    (∀ i j, remote i j →
      Disjoint (edgeSegment P i) (edgeSegment P j) ∨
      ∃ x, edgeSegment P i ∩ edgeSegment P j = {x} ∧
        x ∈ edgeInterior P i ∧ x ∈ edgeInterior P j ∧
        IndependentPair (edge P i) (edge P j)) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  refine ⟨g1_vertices_injective hn h, g1_edge_ne_zero hn h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hz : turn P i ≠ 0 := by
      rw [turn_det]
      exact sign_ne_zero.mpr (g1_turn_nonzero hn h i)
    rcases SignType.trichotomy (turn P i) with hm | hz' | hp
    · exact Or.inr hm
    · exact (hz hz').elim
    · exact Or.inl hp
  · intro i
    exact independent_of_det_ne_zero (g1_turn_nonzero hn h i)
  · intro i t
    exact no_multiple_of_det_ne_zero (g1_turn_nonzero hn h i) t
  · intro i k hk0 hk1 t
    exact g1_vertex_off_edge_line h i k (next_ne_self i).symm hk0 hk1 t
  · intro i k hk0 hk1
    exact g1_vertex_not_mem_edge h i k (next_ne_self i).symm hk0 hk1
  · intro i j hne hadj
    exact g1_adjacent_intersection hn h hne hadj
  · intro i j hr
    exact g1_remote_dichotomy h hr

end SM
