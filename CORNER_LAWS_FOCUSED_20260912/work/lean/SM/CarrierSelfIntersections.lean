import SM.CarrierCrossings
import SM.CarrierNeighborSeparation
import SM.SmoothingDefinition

/-! Towards lem:carriers (iii), geometric part (sm-3-statesum.tex:54): self-intersections of a carrier are exactly its owned unselected crossings, transverse, not corners, no triple point. Written 2026-09-13 by a Claude Code prover subagent of the pod
executor (workflow prove-carriers-lemma / prove:carriers-iii-geom), checked with `lake env lean` (sorry-free, standard axioms) and
ported verbatim from work/drafts/CarriersSelfIntersections.lean (only this header added and #print lines removed). -/

/-! # lem:carriers (iii), geometric part: self-intersections of a carrier

Source: reference/SM/sm-3-statesum.tex, lem:carriers (lines 54-95), clause (iii) lines 84-90:
"A carrier's self-intersections are exactly the unselected crossings both of whose visits are
assigned to it. They are transverse, none is a corner, and no carrier has a triple point."
Proof: lines 222-240 ("Exactly the retained self-intersections").

Encoding (the finite successor model of the Carrier lane): the traced closed curve of the
carrier `q : Component hn hP S` is the concatenation of its segments
`smoothingSegment hn hP S a`, `u ∈ [0,1]`, over the marks `a` owned by `q`, the segment of `a`
running from the plane point of `a` to the plane point of `ρ_S a = smoothingSuccessor hn hP S a`.
A *parameter* of that closed curve is a pair `(a, u)` with `owner a = q` and `0 ≤ u < 1`
(`IsCarrierParameter`): the half-open pieces parametrize the closed curve bijectively (the joint
`σ_a(1) = σ_{ρ_S a}(0)` is the parameter `(ρ_S a, 0)`). A self-intersection of `q` is a point of the
plane with two distinct parameters (`IsSelfIntersection`), a triple point one with three
(`IsTriplePoint`). The number of passes of `q` through a point is the number of its parameters. -/

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-! ## 0. Vertices are not interior points of edges -/

/-- No original vertex lies in the open interior of any edge (G1): for a non-incident edge this
is `g1_vertex_off_edge_line`; for an incident edge the vertex is an endpoint. -/
theorem csi_vertex_not_mem_edgeInterior (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (k i : ZMod n) : P k ∉ edgeInterior P i := by
  have : Fact (1 < n) := ⟨by omega⟩
  rintro ⟨r, hr0, hr1, hr⟩
  have hne : edge P i ≠ 0 := g1_edge_ne_zero hn hP i
  by_cases hk0 : k = i
  · subst hk0
    have h0 : edgePoint P k 0 = edgePoint P k r := by rw [edgePoint_zero]; exact hr
    have := edgePoint_injective hne h0
    linarith
  · by_cases hk1 : k = i + 1
    · subst hk1
      have h1 : edgePoint P i 1 = edgePoint P i r := by rw [edgePoint_one]; exact hr
      have := edgePoint_injective hne h1
      linarith
    · exact g1_vertex_off_edge_line hP i k (next_ne_self i).symm hk0 hk1 r hr

/-- A crossing point is never an original vertex. -/
theorem csi_crossingPoint_ne_vertex (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (c : Crossing P) (k : ZMod n) : crossingPoint c ≠ P k := by
  have : Fact (1 < n) := ⟨by omega⟩
  intro he
  obtain ⟨i, j, hs, _, _⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hint := crossingPoint_interior hP c i hi
  rw [he] at hint
  exact csi_vertex_not_mem_edgeInterior hn hP k i hint

/-! ## 1. Parent edge and parameter interval of a carrier segment -/

/-- The parent original edge of the segment of `a`: the edge of the selected-slot image
`selectedMarkPerm S a` (the twin at a selected visit, `a` itself otherwise). -/
def csiEdge (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (S : Finset (Crossing P))
    (a : Mark P) : ZMod n :=
  (markPosition hn hP.1 (selectedMarkPerm S a)).1

/-- The start parameter of the segment of `a` on its parent edge. -/
def csiStart (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (S : Finset (Crossing P))
    (a : Mark P) : ℝ :=
  (markPosition hn hP.1 (selectedMarkPerm S a)).2.val

omit [NeZero n] in
theorem csiStart_nonneg (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) : 0 ≤ csiStart hn hP S a :=
  (markPosition hn hP.1 (selectedMarkPerm S a)).2.property.1

omit [NeZero n] in
theorem csiStart_lt_one (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) : csiStart hn hP S a < 1 :=
  (markPosition hn hP.1 (selectedMarkPerm S a)).2.property.2

theorem csi_smoothingSuccessor_eq (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) :
    smoothingSuccessor hn hP S a = markSuccessor hn hP (selectedMarkPerm S a) := rfl

theorem csi_evaluation_start (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) :
    traversalEvaluation P (markPosition hn hP.1 a) =
      edgePoint P (csiEdge hn hP S a) (csiStart hn hP S a) :=
  (selectedMarkPerm_evaluation hn hP.1 S a).symm

/-- The segment of `a` is the parent-edge parameter interval `[s, t]`, `s < t ≤ 1`, and its end
mark `ρ_S a` is either the mark at parameter `t` of the parent edge or the next original vertex
(`t = 1`). -/
theorem csi_segment_data (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) :
    ∃ t : ℝ, csiStart hn hP S a < t ∧ t ≤ 1 ∧
      (∀ u : ℝ, smoothingSegment hn hP S a u =
        edgePoint P (csiEdge hn hP S a) (csiStart hn hP S a + u * (t - csiStart hn hP S a))) ∧
      (((markPosition hn hP.1 (smoothingSuccessor hn hP S a)).1 = csiEdge hn hP S a ∧
          (markPosition hn hP.1 (smoothingSuccessor hn hP S a)).2.val = t) ∨
        (smoothingSuccessor hn hP S a = Sum.inl (csiEdge hn hP S a + 1) ∧ t = 1)) := by
  have hstart := csi_evaluation_start hn hP S a
  rcases markSuccessor_position_cases hn hP (selectedMarkPerm S a) with ⟨hi, ht⟩ | hv
  · refine ⟨(markPosition hn hP.1 (smoothingSuccessor hn hP S a)).2.val, ht,
      (markPosition hn hP.1 (smoothingSuccessor hn hP S a)).2.property.2.le, ?_, Or.inl ⟨hi, rfl⟩⟩
    intro u
    have hend : traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) =
        edgePoint P (csiEdge hn hP S a)
          (markPosition hn hP.1 (smoothingSuccessor hn hP S a)).2.val := by
      unfold traversalEvaluation
      rw [csi_smoothingSuccessor_eq, hi]
      rfl
    unfold smoothingSegment
    rw [hstart, hend, edgePoint_affine]
  · refine ⟨1, csiStart_lt_one hn hP S a, le_rfl, ?_, Or.inr ⟨hv, rfl⟩⟩
    intro u
    have hend : traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) =
        edgePoint P (csiEdge hn hP S a) 1 := by
      rw [csi_smoothingSuccessor_eq, hv, markPosition_evaluation_vertex, edgePoint_one]
      rfl
    unfold smoothingSegment
    rw [hstart, hend, edgePoint_affine]

/-! ## 2. No mark in the parameter gap of a segment -/

/-- No mark lies on the parent edge of the segment of `a` strictly between its start parameter
and its end parameter (the segment is a *consecutive* piece of the marked circle). The end
datum is either form of `csi_segment_data`. -/
theorem csi_no_mark_in_gap (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a m : Mark P) (t : ℝ)
    (hdata : ((markPosition hn hP.1 (smoothingSuccessor hn hP S a)).1 = csiEdge hn hP S a ∧
          (markPosition hn hP.1 (smoothingSuccessor hn hP S a)).2.val = t) ∨
        (smoothingSuccessor hn hP S a = Sum.inl (csiEdge hn hP S a + 1) ∧ t = 1))
    (hme : (markPosition hn hP.1 m).1 = csiEdge hn hP S a)
    (hlo : csiStart hn hP S a < (markPosition hn hP.1 m).2.val)
    (hhi : (markPosition hn hP.1 m).2.val < t) : False := by
  have : Fact (1 < n) := ⟨by omega⟩
  set a' := selectedMarkPerm S a with ha'
  set i := csiEdge hn hP S a with hi
  have hnb := markSuccessor_no_mark_between hn hP a' m
  rw [← csi_smoothingSuccessor_eq] at hnb
  apply hnb
  rw [← traversalBetween_shift i]
  -- shifted positions
  have hp : traversalShift i (markPosition hn hP.1 a') = ((0 : ZMod n), (markPosition hn hP.1 a').2) := by
    simp [traversalShift, i, csiEdge, a']
  have hq : traversalShift i (markPosition hn hP.1 m) = ((0 : ZMod n), (markPosition hn hP.1 m).2) := by
    apply Prod.ext
    · change (markPosition hn hP.1 m).1 - i = 0
      rw [hme]
      exact sub_self _
    · rfl
  have hk0 : ∀ s : Set.Ico (0 : ℝ) 1, traversalKey ((0 : ZMod n), s) = s.val := by
    intro s
    simp [traversalKey]
  rw [hp, hq]
  rcases hdata with ⟨hre, hrt⟩ | ⟨hv, ht1⟩
  · have hr : traversalShift i (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) =
        ((0 : ZMod n), (markPosition hn hP.1 (smoothingSuccessor hn hP S a)).2) := by
      apply Prod.ext
      · change (markPosition hn hP.1 (smoothingSuccessor hn hP S a)).1 - i = 0
        rw [hre]
        exact sub_self _
      · rfl
    rw [hr]
    left
    rw [hk0, hk0, hk0]
    exact ⟨hlo, hrt ▸ hhi⟩
  · let z : Set.Ico (0 : ℝ) 1 := ⟨0, le_rfl, zero_lt_one⟩
    have hr : traversalShift i (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) =
        ((1 : ZMod n), z) := by
      rw [hv]
      apply Prod.ext
      · change (i + 1) - i = 1
        abel
      · rfl
    have hk1 : traversalKey ((1 : ZMod n), z) = 1 := by
      simp [traversalKey, z, ZMod.val_one]
    rw [hr]
    left
    rw [hk0, hk0, hk1]
    exact ⟨hlo, ht1 ▸ hhi⟩

/-! ## 3. Distinct segments on one parent edge have disjoint half-open parameter intervals -/

/-- Auxiliary: with `csiStart a < csiStart b` on a common parent edge, the half-open pieces
`σ_a([0,1))` and `σ_b([0,1))` are disjoint, since the start mark of `b` would otherwise lie in
the gap of `a`. -/
theorem csi_same_edge_disjoint_of_lt (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a b : Mark P) (he : csiEdge hn hP S a = csiEdge hn hP S b)
    (hs : csiStart hn hP S a < csiStart hn hP S b) {u v : ℝ}
    (_hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (_hv1 : v < 1) :
    smoothingSegment hn hP S a u ≠ smoothingSegment hn hP S b v := by
  intro h
  have : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨ta, hsta, hta1, hfa, hdata⟩ := csi_segment_data hn hP S a
  obtain ⟨tb, hstb, htb1, hfb, _⟩ := csi_segment_data hn hP S b
  rw [hfa u, hfb v, he] at h
  have hr := edgePoint_injective (g1_edge_ne_zero hn hP.1 (csiEdge hn hP S b)) h
  have hgap : u * (ta - csiStart hn hP S a) < ta - csiStart hn hP S a := by
    have := sub_pos.mpr hsta
    nlinarith
  have hvb : 0 ≤ v * (tb - csiStart hn hP S b) := mul_nonneg hv0 (sub_pos.mpr hstb).le
  refine csi_no_mark_in_gap hn hP S a (selectedMarkPerm S b) ta hdata he.symm hs ?_
  change csiStart hn hP S b < ta
  linarith

/-- Two distinct marks with the same parent edge trace disjoint half-open pieces of that edge
("distinct traversal subsegments of one original edge have disjoint interiors"). -/
theorem csi_same_edge_disjoint (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) {a b : Mark P} (hab : a ≠ b)
    (he : csiEdge hn hP S a = csiEdge hn hP S b) {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    smoothingSegment hn hP S a u ≠ smoothingSegment hn hP S b v := by
  have hs : csiStart hn hP S a ≠ csiStart hn hP S b := by
    intro hs
    apply hab
    have hpos : markPosition hn hP.1 (selectedMarkPerm S a) =
        markPosition hn hP.1 (selectedMarkPerm S b) :=
      Prod.ext he (Subtype.ext hs)
    have h1 := markPosition_injective hn hP hpos
    have h2 := congrArg (selectedMarkPerm S) h1
    rwa [selectedMarkPerm_involutive, selectedMarkPerm_involutive] at h2
  rcases lt_or_gt_of_ne hs with hlt | hgt
  · exact csi_same_edge_disjoint_of_lt hn hP S a b he hlt hu0 hu1 hv0 hv1
  · exact fun h => csi_same_edge_disjoint_of_lt hn hP S b a he.symm hgt hv0 hv1 hu0 hu1 h.symm

/-! ## 4. Meetings of two distinct original edges -/

/-- A common point of two distinct closed edges is an original vertex (adjacent edges, G1) or
the crossing point of the crossing `{i, j}` (remote edges). -/
theorem csi_edgeSegment_meet (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    {i j : ZMod n} (hij : i ≠ j) {x : Plane}
    (hxi : x ∈ edgeSegment P i) (hxj : x ∈ edgeSegment P j) :
    (∃ k : ZMod n, x = P k) ∨ ∃ c : Crossing P, c.val = {i, j} ∧ x = crossingPoint c := by
  have : Fact (1 < n) := ⟨by omega⟩
  by_cases hadj : adjacent i j
  · left
    rcases g1_adjacent_intersection hn hP hij hadj with ⟨_, hint⟩ | ⟨_, hint⟩
    · have hx : x ∈ edgeSegment P i ∩ edgeSegment P j := ⟨hxi, hxj⟩
      rw [hint] at hx
      exact ⟨j, hx⟩
    · have hx : x ∈ edgeSegment P i ∩ edgeSegment P j := ⟨hxi, hxj⟩
      rw [hint] at hx
      exact ⟨i, hx⟩
  · right
    have hc : IsCrossing P {i, j} := ⟨i, j, rfl, hadj, ⟨x, hxi, hxj⟩⟩
    refine ⟨⟨{i, j}, hc⟩, rfl, ?_⟩
    apply crossingPoint_unique hP ⟨{i, j}, hc⟩ x
    intro k hk
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hxi
    · exact hxj

/-- A crossing point lies on a closed edge only if that edge is one of its two edges (G2 via
`generic_crossingPoint_injective`, and vertices are excluded). -/
theorem csi_edge_mem_of_crossingPoint_mem (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (c : Crossing P) {e : ZMod n} (hx : crossingPoint c ∈ edgeSegment P e) : e ∈ c.val := by
  obtain ⟨i, j, hs, _, _⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  by_contra he
  have hei : e ≠ i := fun h => he (h ▸ hi)
  rcases csi_edgeSegment_meet hn hP.1 hei hx (crossingPoint_mem c i hi) with ⟨k, hk⟩ | ⟨c', hc', hx'⟩
  · exact csi_crossingPoint_ne_vertex hn hP.1 c k hk
  · have hcc := generic_crossingPoint_injective hn hP hx'
    apply he
    rw [hcc, hc']
    simp

/-! ## 5. Parameters of a vertex and of a crossing point on a segment -/

/-- An original vertex `P k` is the point `σ_a(u)`, `0 ≤ u < 1`, only for `a = k` and `u = 0`. -/
theorem csi_trace_eq_vertex (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (k : ZMod n) (h : smoothingSegment hn hP S a u = P k) : a = Sum.inl k ∧ u = 0 := by
  have : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨t, hst, ht1, hf, _⟩ := csi_segment_data hn hP S a
  set e := csiEdge hn hP S a with he
  set s := csiStart hn hP S a with hs
  have hs0 : 0 ≤ s := csiStart_nonneg hn hP S a
  rw [hf u] at h
  have hne : edge P e ≠ 0 := g1_edge_ne_zero hn hP.1 e
  have hr0 : 0 ≤ s + u * (t - s) := add_nonneg hs0 (mul_nonneg hu0 (sub_pos.mpr hst).le)
  have hrt : s + u * (t - s) < t := by
    have := sub_pos.mpr hst
    nlinarith
  by_cases hk0 : k = e
  · rw [hk0] at h
    have h0 : edgePoint P e (s + u * (t - s)) = edgePoint P e 0 := by rw [edgePoint_zero]; exact h
    have hr := edgePoint_injective hne h0
    have hsz : s = 0 := by nlinarith [mul_nonneg hu0 (sub_pos.mpr hst).le]
    have huz : u = 0 := by
      have hm : u * (t - s) = 0 := by linarith
      exact (mul_eq_zero.mp hm).resolve_right (sub_pos.mpr hst).ne'
    refine ⟨?_, huz⟩
    rw [hk0]
    have hpos : markPosition hn hP.1 (selectedMarkPerm S a) = markPosition hn hP.1 (Sum.inl e) := by
      rw [markPosition_vertex]
      exact Prod.ext rfl (Subtype.ext hsz)
    have h1 := markPosition_injective hn hP hpos
    have h2 := congrArg (selectedMarkPerm S) h1
    rwa [selectedMarkPerm_involutive, selectedMarkPerm_vertex] at h2
  · by_cases hk1 : k = e + 1
    · rw [hk1] at h
      have h1 : edgePoint P e (s + u * (t - s)) = edgePoint P e 1 := by rw [edgePoint_one]; exact h
      have hr := edgePoint_injective hne h1
      linarith
    · exfalso
      exact g1_vertex_not_mem_edge hP.1 e k (next_ne_self e).symm hk0 hk1
        ⟨s + u * (t - s), hr0, hrt.le.trans ht1, h.symm⟩

/-- The crossing point of `c` is the point `σ_a(u)`, `0 ≤ u < 1`, only for `u = 0` and `a` a
visit of `c`: the visit of `c` on the parent edge is a mark, so it cannot lie in the gap of the
segment, hence it is the start mark. -/
theorem csi_trace_eq_crossingPoint (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (c : Crossing P) (h : smoothingSegment hn hP S a u = crossingPoint c) :
    u = 0 ∧ ∃ w : Visit P, w.1 = c ∧ a = Sum.inr w := by
  have : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨t, hst, ht1, hf, hdata⟩ := csi_segment_data hn hP S a
  set e := csiEdge hn hP S a with he
  set s := csiStart hn hP S a with hs
  have hs0 : 0 ≤ s := csiStart_nonneg hn hP S a
  rw [hf u] at h
  have hne : edge P e ≠ 0 := g1_edge_ne_zero hn hP.1 e
  have hr0 : 0 ≤ s + u * (t - s) := add_nonneg hs0 (mul_nonneg hu0 (sub_pos.mpr hst).le)
  have hrt : s + u * (t - s) < t := by
    have := sub_pos.mpr hst
    nlinarith
  have hmem : crossingPoint c ∈ edgeSegment P e :=
    ⟨s + u * (t - s), hr0, hrt.le.trans ht1, h.symm⟩
  have hec : e ∈ c.val := csi_edge_mem_of_crossingPoint_mem hn hP c hmem
  let w0 : Visit P := ⟨c, ⟨e, hec⟩⟩
  have hw0 : crossingPoint c = edgePoint P e (visitParameter w0) :=
    (crossingParameter_spec c e hec).2.2
  rw [hw0] at h
  have hr := edgePoint_injective hne h
  have hpos0 : markPosition hn hP.1 (Sum.inr w0) = (e, ⟨visitParameter w0,
      (visitPosition_interior hn hP.1 w0).1.le, (visitPosition_interior hn hP.1 w0).2⟩) := rfl
  have hnlt : ¬ s < visitParameter w0 := by
    intro hlt
    refine csi_no_mark_in_gap hn hP S a (Sum.inr w0) t hdata rfl hlt ?_
    change visitParameter w0 < t
    rw [← hr]
    exact hrt
  have hsr : s = visitParameter w0 := by
    have hsle : s ≤ visitParameter w0 := by
      rw [← hr]
      exact le_add_of_nonneg_right (mul_nonneg hu0 (sub_pos.mpr hst).le)
    exact le_antisymm hsle (not_lt.mp hnlt)
  have huz : u = 0 := by
    have hm : u * (t - s) = 0 := by linarith
    exact (mul_eq_zero.mp hm).resolve_right (sub_pos.mpr hst).ne'
  refine ⟨huz, selectedVisitTwin S w0, selectedVisitTwin_crossing S w0, ?_⟩
  have hpos : markPosition hn hP.1 (selectedMarkPerm S a) = markPosition hn hP.1 (Sum.inr w0) := by
    rw [hpos0]
    exact Prod.ext rfl (Subtype.ext hsr)
  have h1 := markPosition_injective hn hP hpos
  have h2 := congrArg (selectedMarkPerm S) h1
  rwa [selectedMarkPerm_involutive, selectedMarkPerm_visit] at h2

/-! ## 6. The core meeting theorem -/

/-- **Two distinct half-open segments meet only at a crossing point, at their start marks,
which are the two visits of that crossing.** For marks `a ≠ b` and parameters `u, v ∈ [0,1)`
with `σ_a(u) = σ_b(v)`: `u = v = 0`, the point is `crossingPoint c` for a crossing `c`, and
`a`, `b` are visits of `c`. (No ownership or independence hypothesis is needed.) -/
theorem csi_trace_meet (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) {a b : Mark P} (hab : a ≠ b) {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (h : smoothingSegment hn hP S a u = smoothingSegment hn hP S b v) :
    u = 0 ∧ v = 0 ∧ ∃ c : Crossing P, smoothingSegment hn hP S a u = crossingPoint c ∧
      (∃ w : Visit P, w.1 = c ∧ a = Sum.inr w) ∧ (∃ w' : Visit P, w'.1 = c ∧ b = Sum.inr w') := by
  by_cases he : csiEdge hn hP S a = csiEdge hn hP S b
  · exact (csi_same_edge_disjoint hn hP S hab he hu0 hu1 hv0 hv1 h).elim
  · have hxa : smoothingSegment hn hP S a u ∈ edgeSegment P (csiEdge hn hP S a) :=
      smoothingSegment_mem_edgeSegment hn hP S a hu0 hu1.le
    have hxb : smoothingSegment hn hP S a u ∈ edgeSegment P (csiEdge hn hP S b) := by
      rw [h]
      exact smoothingSegment_mem_edgeSegment hn hP S b hv0 hv1.le
    rcases csi_edgeSegment_meet hn hP.1 he hxa hxb with ⟨k, hk⟩ | ⟨c, _, hc⟩
    · exfalso
      have ha := (csi_trace_eq_vertex hn hP S a hu0 hu1 k hk).1
      have hb := (csi_trace_eq_vertex hn hP S b hv0 hv1 k (h ▸ hk)).1
      exact hab (ha.trans hb.symm)
    · obtain ⟨hu, w, hw, ha⟩ := csi_trace_eq_crossingPoint hn hP S a hu0 hu1 c hc
      obtain ⟨hv, w', hw', hb⟩ := csi_trace_eq_crossingPoint hn hP S b hv0 hv1 c (h ▸ hc)
      exact ⟨hu, hv, c, hc, ⟨w, hw, ha⟩, ⟨w', hw', hb⟩⟩

/-! ## 7. The traced closed curve of a carrier and its self-intersections -/

/-- A parameter of the traced closed curve of the carrier `q`: a mark `a` owned by `q` together
with a parameter `u ∈ [0,1)` of the segment of `a` (from `a` to `ρ_S a`). The half-open pieces
parametrize the concatenation of the segments of `q` bijectively: the joint
`σ_a(1) = σ_{ρ_S a}(0)` is represented once, by `(ρ_S a, 0)`. -/
def IsCarrierParameter (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (p : Mark P × ℝ) : Prop :=
  owner hn hP S p.1 = q ∧ 0 ≤ p.2 ∧ p.2 < 1

/-- The point of the plane traced at the parameter `p = (a, u)`: `σ_a(u)`. -/
def carrierTrace (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (p : Mark P × ℝ) : Plane :=
  smoothingSegment hn hP S p.1 p.2

/-- `x` is a self-intersection of the carrier `q`: the traced closed curve of `q` passes through
`x` at (at least) two distinct parameters. -/
def IsSelfIntersection (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (x : Plane) : Prop :=
  ∃ p p' : Mark P × ℝ, IsCarrierParameter hn hP S q p ∧ IsCarrierParameter hn hP S q p' ∧
    p ≠ p' ∧ carrierTrace hn hP S p = x ∧ carrierTrace hn hP S p' = x

/-- `x` is a triple point of the carrier `q`: three distinct parameters trace `x`. -/
def IsTriplePoint (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (x : Plane) : Prop :=
  ∃ p p' p'' : Mark P × ℝ, IsCarrierParameter hn hP S q p ∧ IsCarrierParameter hn hP S q p' ∧
    IsCarrierParameter hn hP S q p'' ∧ p ≠ p' ∧ p ≠ p'' ∧ p' ≠ p'' ∧
    carrierTrace hn hP S p = x ∧ carrierTrace hn hP S p' = x ∧ carrierTrace hn hP S p'' = x

/-- Distinct parameters tracing the same point have distinct marks (each segment is injective). -/
theorem csi_mark_ne_of_param_ne (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) {p p' : Mark P × ℝ} (hne : p ≠ p')
    (h : carrierTrace hn hP S p = carrierTrace hn hP S p') : p.1 ≠ p'.1 := by
  intro hm
  apply hne
  have h' : smoothingSegment hn hP S p.1 p.2 = smoothingSegment hn hP S p.1 p'.2 := by
    unfold carrierTrace at h
    rw [h, hm]
  exact Prod.ext hm (smoothingSegment_injective hn hP S p.1 h')

/-- The parameters of `q` tracing the crossing point of `c` are exactly `(w, 0)` for the visits
`w` of `c` owned by `q`: a carrier passes through a crossing point once for each visit of the
crossing assigned to it. -/
theorem carrier_crossingPoint_parameters (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (c : Crossing P) (p : Mark P × ℝ) :
    (IsCarrierParameter hn hP S q p ∧ carrierTrace hn hP S p = crossingPoint c) ↔
      ∃ w : Visit P, w.1 = c ∧ owner hn hP S (Sum.inr w) = q ∧ p = (Sum.inr w, 0) := by
  constructor
  · rintro ⟨⟨hq, hu0, hu1⟩, hx⟩
    obtain ⟨hu, w, hw, ha⟩ := csi_trace_eq_crossingPoint hn hP S p.1 hu0 hu1 c hx
    refine ⟨w, hw, ?_, Prod.ext ha hu⟩
    rw [← ha]
    exact hq
  · rintro ⟨w, hw, hq, rfl⟩
    refine ⟨⟨hq, le_rfl, zero_lt_one⟩, ?_⟩
    change smoothingSegment hn hP S (Sum.inr w) 0 = crossingPoint c
    rw [smoothingSegment_zero, markPosition_evaluation_visit, hw]

/-- The parameters of `q` tracing the original vertex `P k` are exactly `(k, 0)` when `q` owns
the vertex mark `k`: a carrier passes through an original vertex at most once. -/
theorem carrier_vertex_parameters (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (k : ZMod n) (p : Mark P × ℝ) :
    (IsCarrierParameter hn hP S q p ∧ carrierTrace hn hP S p = P k) ↔
      owner hn hP S (Sum.inl k) = q ∧ p = (Sum.inl k, 0) := by
  constructor
  · rintro ⟨⟨hq, hu0, hu1⟩, hx⟩
    obtain ⟨ha, hu⟩ := csi_trace_eq_vertex hn hP S p.1 hu0 hu1 k hx
    refine ⟨?_, Prod.ext ha hu⟩
    rw [← ha]
    exact hq
  · rintro ⟨hq, rfl⟩
    refine ⟨⟨hq, le_rfl, zero_lt_one⟩, ?_⟩
    change smoothingSegment hn hP S (Sum.inl k) 0 = P k
    rw [smoothingSegment_zero, markPosition_evaluation_vertex]

/-- Two distinct marks owned by `q` whose half-open segments meet do so at the crossing point
of a crossing of `q` (an unselected crossing both of whose visits are owned by `q`); the selected
case is excluded because the two visits of a selected crossing have different owners. -/
theorem csi_owned_marks_meet (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) (q : Component hn hP S)
    {a b : Mark P} (ha : owner hn hP S a = q) (hb : owner hn hP S b = q) (hab : a ≠ b)
    {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (h : smoothingSegment hn hP S a u = smoothingSegment hn hP S b v) :
    ∃ c ∈ carrierCrossings hn hP S q, smoothingSegment hn hP S a u = crossingPoint c := by
  obtain ⟨_, _, c, hc, ⟨w, hw, rfl⟩, ⟨w', hw', rfl⟩⟩ :=
    csi_trace_meet hn hP S hab hu0 hu1 hv0 hv1 h
  have hww' : w' ≠ w := fun he => hab (congrArg Sum.inr he).symm
  have htw : w' = visitTwin w := visitTwin_unique w w' (hw'.trans hw.symm) hww'
  have hcS : c ∉ S := by
    intro hcS
    apply independent_selected_pair_owners_ne hn hP hS w (hw ▸ hcS)
    rw [ha, ← htw, hb]
  refine ⟨c, ?_, hc⟩
  rw [mem_carrierCrossings]
  refine ⟨hcS, ?_⟩
  intro v hv
  rcases visit_eq_or_twin w v (hv.trans hw.symm) with rfl | rfl
  · exact ha
  · rw [← htw]
    exact hb

/-- **lem:carriers (iii), first sentence.** For an independent `S`, the self-intersections of
the carrier `q` are exactly the crossing points of the crossings of `q`
(`carrierCrossings hn hP S q`: the unselected crossings both of whose visits are assigned to `q`). -/
theorem carrier_selfIntersection_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) (q : Component hn hP S)
    (x : Plane) :
    IsSelfIntersection hn hP S q x ↔ ∃ c ∈ carrierCrossings hn hP S q, x = crossingPoint c := by
  constructor
  · rintro ⟨p, p', ⟨hq, hu0, hu1⟩, ⟨hq', hv0, hv1⟩, hne, hx, hx'⟩
    have hab : p.1 ≠ p'.1 := csi_mark_ne_of_param_ne hn hP S hne (hx.trans hx'.symm)
    obtain ⟨c, hc, he⟩ := csi_owned_marks_meet hn hP hS q hq hq' hab hu0 hu1 hv0 hv1
      (hx.trans hx'.symm)
    exact ⟨c, hc, hx.symm.trans he⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨i, _, _⟩ := crossing_visits_exist c
    let w : Visit P := ⟨c, i⟩
    have hmem := (mem_carrierCrossings hn hP S q c).mp hc
    have hw : owner hn hP S (Sum.inr w) = q := hmem.2 w rfl
    have hw' : owner hn hP S (Sum.inr (visitTwin w)) = q := hmem.2 (visitTwin w) rfl
    refine ⟨(Sum.inr w, 0), (Sum.inr (visitTwin w), 0), ⟨hw, le_rfl, zero_lt_one⟩,
      ⟨hw', le_rfl, zero_lt_one⟩, ?_, ?_, ?_⟩
    · intro he
      exact visitTwin_ne w (Sum.inr.inj (congrArg Prod.fst he)).symm
    · change smoothingSegment hn hP S (Sum.inr w) 0 = crossingPoint c
      rw [smoothingSegment_zero, markPosition_evaluation_visit]
    · change smoothingSegment hn hP S (Sum.inr (visitTwin w)) 0 = crossingPoint c
      rw [smoothingSegment_zero, markPosition_evaluation_visit, visitTwin_crossing]

/-- A selected crossing point is a self-intersection of no carrier: "a single carrier passes
through that smoothing point only once". -/
theorem carrier_selected_not_selfIntersection (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) {c : Crossing P} (hc : c ∈ S) :
    ¬ IsSelfIntersection hn hP S q (crossingPoint c) := by
  intro h
  obtain ⟨c', hc', he⟩ := (carrier_selfIntersection_iff hn hP hS q _).mp h
  have hcc := generic_crossingPoint_injective hn hP he
  exact selected_not_mem_carrierCrossings hn hP S q hc (hcc ▸ hc')

/-- An original vertex is a self-intersection of no carrier. -/
theorem carrier_vertex_not_selfIntersection (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (q : Component hn hP S) (k : ZMod n) :
    ¬ IsSelfIntersection hn hP S q (P k) := by
  rintro ⟨p, p', hp, hp', hne, hx, hx'⟩
  have h1 := ((carrier_vertex_parameters hn hP S q k p).mp ⟨hp, hx⟩).2
  have h2 := ((carrier_vertex_parameters hn hP S q k p').mp ⟨hp', hx'⟩).2
  exact hne (h1.trans h2.symm)

/-- **lem:carriers (iii): "no carrier has a triple point."** Three distinct parameters cannot
trace one point: any two of them are the two visits of one crossing, and a crossing has only
two visits. (No independence hypothesis is needed.) -/
theorem carrier_no_triple_point (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (x : Plane) :
    ¬ IsTriplePoint hn hP S q x := by
  rintro ⟨p, p', p'', ⟨_, hu0, hu1⟩, ⟨_, hv0, hv1⟩, ⟨_, hw0, hw1⟩, h01, h02, h12, hx, hx', hx''⟩
  have hab : p.1 ≠ p'.1 := csi_mark_ne_of_param_ne hn hP S h01 (hx.trans hx'.symm)
  have had : p.1 ≠ p''.1 := csi_mark_ne_of_param_ne hn hP S h02 (hx.trans hx''.symm)
  have hbd : p'.1 ≠ p''.1 := csi_mark_ne_of_param_ne hn hP S h12 (hx'.trans hx''.symm)
  obtain ⟨_, _, c, _, ⟨wa, hwa, ha⟩, ⟨wb, hwb, hb⟩⟩ :=
    csi_trace_meet hn hP S hab hu0 hu1 hv0 hv1 (hx.trans hx'.symm)
  obtain ⟨_, _, c', _, ⟨wa', hwa', ha'⟩, ⟨wd, hwd, hd⟩⟩ :=
    csi_trace_meet hn hP S had hu0 hu1 hw0 hw1 (hx.trans hx''.symm)
  have hwaa : wa' = wa := Sum.inr.inj (ha'.symm.trans ha)
  have hcc : c' = c := by rw [← hwa', hwaa, hwa]
  have hwb' : wb = visitTwin wa :=
    visitTwin_unique wa wb (hwb.trans hwa.symm) (fun he => hab (by rw [ha, hb, he]))
  have hwd' : wd = visitTwin wa :=
    visitTwin_unique wa wd (by rw [hwd, hcc, hwa]) (fun he => had (by rw [ha, hd, he]))
  exact hbd (by rw [hb, hd, hwb', hwd'])

/-- A crossing `c` of `q` is passed exactly twice by `q`: its parameters are precisely
`(w, 0)` and `(visitTwin w, 0)` for the two visits of `c`. -/
theorem carrier_crossing_two_passes (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) {c : Crossing P}
    (hc : c ∈ carrierCrossings hn hP S q) (w : Visit P) (hw : w.1 = c) (p : Mark P × ℝ) :
    (IsCarrierParameter hn hP S q p ∧ carrierTrace hn hP S p = crossingPoint c) ↔
      (p = (Sum.inr w, 0) ∨ p = (Sum.inr (visitTwin w), 0)) := by
  have hmem := (mem_carrierCrossings hn hP S q c).mp hc
  rw [carrier_crossingPoint_parameters]
  constructor
  · rintro ⟨w', hw', _, rfl⟩
    rcases visit_eq_or_twin w w' (hw'.trans hw.symm) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨w, hw, hmem.2 w hw, rfl⟩
    · exact ⟨visitTwin w, (visitTwin_crossing w).trans hw, hmem.2 _ ((visitTwin_crossing w).trans hw), rfl⟩

/-! ## 8. Transversality and non-corner status of the self-intersections -/

omit [NeZero n] in
theorem csi_det_smul_smul (u v : Plane) (c₁ c₂ : ℝ) :
    det (c₁ • u) (c₂ • v) = c₁ * c₂ * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

omit [NeZero n] in
/-- The two edges of a crossing have transverse directions (G1). -/
theorem csi_crossing_edges_det_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (c : Crossing P) {i j : ZMod n} (hi : i ∈ c.val) (hj : j ∈ c.val) (hij : i ≠ j) :
    det (edge P i) (edge P j) ≠ 0 := by
  have : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨i0, j0, hs, hr, _⟩ := c.property
  have hi0 : i0 ∈ c.val := by rw [hs]; simp
  have hj0 : j0 ∈ c.val := by rw [hs]; simp
  have hd := (g1_remote_meeting hP hr (crossingPoint_mem c i0 hi0) (crossingPoint_mem c j0 hj0)).2.2.1
  rw [hs, Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · exact hd
  · rw [det_swap]
    exact neg_ne_zero.mpr hd
  · exact (hij rfl).elim

/-- **lem:carriers (iii): the self-intersections are transverse, with the parent's unchanged
straight germs.** At a crossing `c` of `q` with visits `w`, `visitTwin w` (on the edges
`i = w.2`, `j = (visitTwin w).2` of `c`), the incoming and outgoing segments of `q` at `w` are
positive multiples of `ℓ_i`, those at `visitTwin w` positive multiples of `ℓ_j`, `det(ℓ_i, ℓ_j) ≠ 0`,
and the determinant of the two outgoing germs of `q` at the point is nonzero. -/
theorem carrier_selfIntersection_transverse (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (q : Component hn hP S) {c : Crossing P}
    (hc : c ∈ carrierCrossings hn hP S q) (w : Visit P) (hw : w.1 = c) :
    det (edge P w.2.val) (edge P (visitTwin w).2.val) ≠ 0 ∧
    (∃ c₁ : ℝ, 0 < c₁ ∧ smoothingSegment hn hP S (Sum.inr w) 1 -
        smoothingSegment hn hP S (Sum.inr w) 0 = c₁ • edge P w.2.val) ∧
    (∃ c₁' : ℝ, 0 < c₁' ∧ smoothingSegment hn hP S (Sum.inr w) 0 -
        smoothingSegment hn hP S ((smoothingSuccessor hn hP S).symm (Sum.inr w)) 0 =
          c₁' • edge P w.2.val) ∧
    (∃ c₂ : ℝ, 0 < c₂ ∧ smoothingSegment hn hP S (Sum.inr (visitTwin w)) 1 -
        smoothingSegment hn hP S (Sum.inr (visitTwin w)) 0 = c₂ • edge P (visitTwin w).2.val) ∧
    (∃ c₂' : ℝ, 0 < c₂' ∧ smoothingSegment hn hP S (Sum.inr (visitTwin w)) 0 -
        smoothingSegment hn hP S ((smoothingSuccessor hn hP S).symm (Sum.inr (visitTwin w))) 0 =
          c₂' • edge P (visitTwin w).2.val) ∧
    det (smoothingSegment hn hP S (Sum.inr w) 1 - smoothingSegment hn hP S (Sum.inr w) 0)
      (smoothingSegment hn hP S (Sum.inr (visitTwin w)) 1 -
        smoothingSegment hn hP S (Sum.inr (visitTwin w)) 0) ≠ 0 := by
  subst hw
  have hcS : w.1 ∉ S := ((mem_carrierCrossings hn hP S q w.1).mp hc).1
  have htS : (visitTwin w).1 ∉ S := by rw [visitTwin_crossing]; exact hcS
  have hdet : det (edge P w.2.val) (edge P (visitTwin w).2.val) ≠ 0 :=
    csi_crossing_edges_det_ne_zero hn hP.1 w.1 w.2.property
      (by rw [← visitTwin_crossing w]; exact (visitTwin w).2.property) (visitTwin_edge_ne w).symm
  obtain ⟨c₁, hc₁, he₁⟩ := unselected_visit_outgoing_direction hn hP S w hcS
  obtain ⟨c₂, hc₂, he₂⟩ := unselected_visit_outgoing_direction hn hP S (visitTwin w) htS
  have hout₁ : smoothingSegment hn hP S (Sum.inr w) 1 - smoothingSegment hn hP S (Sum.inr w) 0 =
      c₁ • edge P w.2.val := by
    rw [smoothingSegment_one, smoothingSegment_zero]; exact he₁
  have hout₂ : smoothingSegment hn hP S (Sum.inr (visitTwin w)) 1 -
      smoothingSegment hn hP S (Sum.inr (visitTwin w)) 0 = c₂ • edge P (visitTwin w).2.val := by
    rw [smoothingSegment_one, smoothingSegment_zero]; exact he₂
  refine ⟨hdet, ⟨c₁, hc₁, hout₁⟩, ?_, ⟨c₂, hc₂, hout₂⟩, ?_, ?_⟩
  · obtain ⟨d, hd, he⟩ := visit_incoming_direction hn hP S w
    refine ⟨d, hd, ?_⟩
    rw [smoothingSegment_zero, smoothingSegment_zero]; exact he
  · obtain ⟨d, hd, he⟩ := visit_incoming_direction hn hP S (visitTwin w)
    refine ⟨d, hd, ?_⟩
    rw [smoothingSegment_zero, smoothingSegment_zero]; exact he
  · rw [hout₁, hout₂, csi_det_smul_smul]
    exact mul_ne_zero (mul_ne_zero hc₁.ne' hc₂.ne') hdet

/-- **lem:carriers (iii): "none is a corner."** The crossing point of a crossing of `q` differs
from every original vertex and from every selected crossing point; hence it is the plane point
of no true corner (original vertex mark or selected visit) of any carrier. -/
theorem carrier_selfIntersection_not_corner (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (q : Component hn hP S) {c : Crossing P}
    (hc : c ∈ carrierCrossings hn hP S q) :
    (∀ k : ZMod n, crossingPoint c ≠ P k) ∧
    (∀ c' ∈ S, crossingPoint c ≠ crossingPoint c') ∧
    (∀ w : Visit P, w.1 = c → ¬ IsTrueCorner S (Sum.inr w)) ∧
    ∀ m : Mark P, IsTrueCorner S m →
      traversalEvaluation P (markPosition hn hP.1 m) ≠ crossingPoint c := by
  have hcS : c ∉ S := ((mem_carrierCrossings hn hP S q c).mp hc).1
  have hv : ∀ k : ZMod n, crossingPoint c ≠ P k := csi_crossingPoint_ne_vertex hn hP.1 c
  have hs : ∀ c' ∈ S, crossingPoint c ≠ crossingPoint c' := by
    intro c' hc' he
    exact hcS ((generic_crossingPoint_injective hn hP he) ▸ hc')
  refine ⟨hv, hs, fun w hw hcorner => hcS (hw ▸ hcorner), ?_⟩
  intro m hm
  cases m with
  | inl k =>
    rw [markPosition_evaluation_vertex]
    exact (hv k).symm
  | inr v =>
    rw [markPosition_evaluation_visit]
    exact (hs v.1 hm).symm

/-! ## 9. Closed segments: non-consecutive segments meet only at crossings of the carrier -/

/-- Normalization of a closed-segment parameter `(a, u)`, `u ∈ [0,1]`, to a half-open one:
the point `σ_a(1)` is `σ_{ρ_S a}(0)`. -/
theorem csi_normalize (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∃ a' : Mark P, ∃ u' : ℝ, (a' = a ∨ a' = smoothingSuccessor hn hP S a) ∧ 0 ≤ u' ∧ u' < 1 ∧
      smoothingSegment hn hP S a u = smoothingSegment hn hP S a' u' ∧
      owner hn hP S a' = owner hn hP S a := by
  rcases lt_or_eq_of_le hu1 with hlt | heq
  · exact ⟨a, u, Or.inl rfl, hu0, hlt, rfl, rfl⟩
  · subst heq
    exact ⟨smoothingSuccessor hn hP S a, 0, Or.inr rfl, le_rfl, zero_lt_one,
      smoothingSegment_glue hn hP S a, owner_successor hn hP S a⟩

/-- **Two distinct non-consecutive closed segments of one carrier meet only at crossing points
of crossings of that carrier.** For `a ≠ b` owned by `q` with `b ≠ ρ_S a` and `a ≠ ρ_S b`, every
common point of the closed segments `σ_a([0,1])`, `σ_b([0,1])` is `crossingPoint c` for some
`c ∈ carrierCrossings hn hP S q`. -/
theorem carrier_nonconsecutive_segments_meet (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) {a b : Mark P} (ha : owner hn hP S a = q) (hb : owner hn hP S b = q)
    (hab : a ≠ b) (hba : b ≠ smoothingSuccessor hn hP S a) (hab' : a ≠ smoothingSuccessor hn hP S b)
    {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (h : smoothingSegment hn hP S a u = smoothingSegment hn hP S b v) :
    ∃ c ∈ carrierCrossings hn hP S q, smoothingSegment hn hP S a u = crossingPoint c := by
  obtain ⟨a', u', ha', hu0', hu1', hea, hoa⟩ := csi_normalize hn hP S a hu0 hu1
  obtain ⟨b', v', hb', hv0', hv1', heb, hob⟩ := csi_normalize hn hP S b hv0 hv1
  have hne : a' ≠ b' := by
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact hab
    · exact hab'
    · exact hba.symm
    · exact fun he => hab ((smoothingSuccessor hn hP S).injective he)
  obtain ⟨c, hc, he⟩ := csi_owned_marks_meet hn hP hS q (hoa.trans ha) (hob.trans hb) hne
    hu0' hu1' hv0' hv1' (hea.symm.trans (h.trans heb))
  exact ⟨c, hc, hea.trans he⟩

/-! ## 10. lem:carriers (iii), geometric part, assembled -/

/-- **lem:carriers (iii), geometric part** (sm-3-statesum.tex:84-86), for a generic polygon
`P`, `n ≥ 3`, and an independent `S`: for every carrier `q`,
(1) its self-intersections are exactly the crossing points of the unselected crossings both of
whose visits are assigned to it (`carrierCrossings hn hP S q`);
(2) each is transverse: at such a crossing with visits `w`, `visitTwin w`, the two germs of `q`
are positive multiples of the two (transverse) parent edge directions, and the determinant of
the two outgoing germs is nonzero;
(3) none is a corner: it differs from every original vertex and every selected crossing point,
hence from the plane point of every true corner;
(4) `q` has no triple point. -/
theorem carrier_selfIntersections (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) (q : Component hn hP S) :
    (∀ x : Plane, IsSelfIntersection hn hP S q x ↔
      ∃ c ∈ carrierCrossings hn hP S q, x = crossingPoint c) ∧
    (∀ c ∈ carrierCrossings hn hP S q, ∀ w : Visit P, w.1 = c →
      det (edge P w.2.val) (edge P (visitTwin w).2.val) ≠ 0 ∧
      (∃ c₁ : ℝ, 0 < c₁ ∧ smoothingSegment hn hP S (Sum.inr w) 1 -
          smoothingSegment hn hP S (Sum.inr w) 0 = c₁ • edge P w.2.val) ∧
      (∃ c₂ : ℝ, 0 < c₂ ∧ smoothingSegment hn hP S (Sum.inr (visitTwin w)) 1 -
          smoothingSegment hn hP S (Sum.inr (visitTwin w)) 0 = c₂ • edge P (visitTwin w).2.val) ∧
      det (smoothingSegment hn hP S (Sum.inr w) 1 - smoothingSegment hn hP S (Sum.inr w) 0)
        (smoothingSegment hn hP S (Sum.inr (visitTwin w)) 1 -
          smoothingSegment hn hP S (Sum.inr (visitTwin w)) 0) ≠ 0) ∧
    (∀ c ∈ carrierCrossings hn hP S q,
      (∀ k : ZMod n, crossingPoint c ≠ P k) ∧
      (∀ c' ∈ S, crossingPoint c ≠ crossingPoint c') ∧
      (∀ w : Visit P, w.1 = c → ¬ IsTrueCorner S (Sum.inr w)) ∧
      ∀ m : Mark P, IsTrueCorner S m →
        traversalEvaluation P (markPosition hn hP.1 m) ≠ crossingPoint c) ∧
    (∀ x : Plane, ¬ IsTriplePoint hn hP S q x) := by
  refine ⟨carrier_selfIntersection_iff hn hP hS q, ?_,
    fun c hc => carrier_selfIntersection_not_corner hn hP S q hc,
    carrier_no_triple_point hn hP S q⟩
  intro c hc w hw
  obtain ⟨hd, h₁, _, h₂, _, hdet⟩ := carrier_selfIntersection_transverse hn hP S q hc w hw
  exact ⟨hd, h₁, h₂, hdet⟩


end
end SM.Carrier
