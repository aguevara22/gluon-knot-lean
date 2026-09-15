import SM.GeoCarrierCrossings
import SM.GeoCarrierGeometry

/-! Ported 2026-09-14 from work/drafts/cvdom/U2c/GeoCarrierSelfIntersections.lean (CV-DOM unit U2c: self-intersections of the geo carriers = their retained crossings, transverse, not at corners, no triple point — tier 1 (CarrierGeometry), with the tier-2 corollary and the agreement lemmas with the accepted lane; REPORT.md in the same directory). Library module, no row. Only this header added. -/

/-! # SM/GeoCarrierSelfIntersections.lean — self-intersections of a geo carrier (CV-DOM unit U2c)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor, for the CV-DOM decision
(work/drafts/cvdom/DECISION_FINAL.md §0, §3 rulings R1–R5, §5 unit U2c). Draft home
work/drafts/cvdom/U2c/; intended home work/lean/SM/GeoCarrierSelfIntersections.lean. CV-free.

Port of work/lean/SM/CarrierSelfIntersections.lean (lem:carriers (iii), geometric part,
sm-3-statesum.tex:84-90: "A carrier's self-intersections are exactly the unselected crossings both
of whose visits are assigned to it. They are transverse, none is a corner, and no carrier has a
triple point.") onto the ACCEPTED geometric carrier layer `SM.GeoCarrier` of SM/FlatCarriersDefs.lean
(def:flat-carriers: `geoMarkPosition`, `geoSmoothingSuccessor`, `GeoComponent`, `geoOwner`,
`geoSmoothingSegment`, `geoCarrierCrossings`, `GeoIndependent`, all on `hP : CrossingGeometry P`).

Tiers (ruling R1). Tier 0 = `CrossingGeometry P`; tier 1 = `CarrierGeometry P` (U0,
SM/GeoCarrierGeometry.lean: tier 0 + "no vertex on a non-incident closed edge"); tier 2 =
`WeakGeneric P` — NOT needed anywhere in this file (ruling R4: the one tier-2 site of the analysts'
prototype, `turns_adjacent_intersection` in `csi_edgeSegment_meet`, is replaced by U0's fold-back
exclusion `CarrierGeometry.adjacent_edges_meet hn`). Every declaration below is tier 0 or tier 1.

Sections follow the source. §0 of the source is U0's `cg_vertex_not_mem_edgeInterior`,
`cg_crossingPoint_ne_vertex` (not re-declared). §1–§3 (parent edge, parameter gap, disjoint
half-open pieces on one edge) are tier 0 and word for word the analysts' prototype
work/drafts/cvdom/CarrierGeometry.lean. §4 (meetings of two distinct edges) is tier 1:
`cg_edgeSegment_meet`, `cg_edge_mem_of_crossingPoint_mem` re-bound from the dropped `CornerGeometry`
to `CarrierGeometry` (they now take `hn : 3 ≤ n`, needed by the fold-back lemma). §5–§6 (vertex /
crossing point on a segment; the core meeting theorem) tier 1. §7 the traced closed curve of a carrier:
`GeoIsCarrierParameter`, `geoCarrierTrace`, `GeoIsSelfIntersection`, `GeoIsTriplePoint` (tier 0
definitions) and the parameter lemmas (tier 1). §8 transversality (tier 0) and non-corner status
(tier 1). §9 closed segments. §10 the §5 target `geo_self_intersections (hn) (hG : CarrierGeometry P)
(hS) (q)`, with the exact shape of the accepted `CarriersLemmaData.self_intersections`
(SM/CarriersLemma.lean) under `owner ↦ geoOwner`, `carrierCrossings ↦ geoCarrierCrossings`,
`smoothingSegment ↦ geoSmoothingSegment`, `markPosition hn hP.1 ↦ geoMarkPosition hG.cg`,
`IsSelfIntersection ↦ GeoIsSelfIntersection`, `IsTriplePoint ↦ GeoIsTriplePoint`. §11 agreement of the
new definitions with the accepted lane on SM-generic polygons (through the accepted §4b lemmas of
FlatCarriersDefs).

Renaming (port_lane.py DEFMAP + the §5 extension `IsSelfIntersection ↦ GeoIsSelfIntersection`,
`IsTriplePoint ↦ GeoIsTriplePoint`, and `IsCarrierParameter ↦ GeoIsCarrierParameter`, `carrierTrace ↦
geoCarrierTrace`, `csiX ↦ geoCsiX`, `csi_X ↦ geoCsi_X`, `carrier_X ↦ geo_carrier_X`): `X hn hP → geoX hP`,
`markPosition hn hP.1 → geoMarkPosition hP`, `S ∈ independentSupports hn hP → GeoIndependent hP S`.
`hn : 3 ≤ n` is kept exactly where the accepted lemmas take it (`geoMarkSuccessor_position_cases hn`,
`geoSmoothingSegment_injective hn`, the direction lemmas of FlatCarriers §3) and on the §5 target.
The 13 G1/`Generic`-lemma sites of the source (ANALYSIS_A.md §2, row CarrierSelfIntersections):
`g1_edge_ne_zero → hP.1` (clause 1, ×4), `g1_vertex_off_edge_line` / `g1_vertex_not_mem_edge →
hG.vertex_not_mem_edge` (U0), `crossingPoint_interior → crossingPoint_interior_of_geometry` (in U0's
`cg_crossingPoint_ne_vertex`), `g1_adjacent_intersection → CarrierGeometry.adjacent_edges_meet hn` (U0,
tier 1), `crossingPoint_unique → crossingPoint_unique_of_geometry`, `generic_crossingPoint_injective →
crossingPoint_injective_of_geometry` (×3), `g1_remote_meeting → crossing_det_ne_zero_of_geometry`
(clause 2); and the `Generic`-typed lane lemmas `markPosition_injective → geoMarkPosition_injective`,
`visitPosition_interior → crossingParameter_interior_of_geometry`, `smoothingSegment_injective →
geoSmoothingSegment_injective hn` (U1b), `independent_selected_pair_owners_ne →
geo_selected_visits_separated` (U1a), `mem_carrierCrossings → mem_geoCarrierCrossings` (U2a).

Checked with `cd work/lean && lake env lean ../drafts/cvdom/U2c/GeoCarrierSelfIntersections.lean`. -/

namespace SM.GeoCarrier
open Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-! ## 0. Vertices are not interior points of edges

Source §0 (`csi_vertex_not_mem_edgeInterior`, `csi_crossingPoint_ne_vertex`) is U0's
`cg_vertex_not_mem_edgeInterior (hG) (k i)`, `cg_crossingPoint_ne_vertex (hG) (c) (k)`
(SM/GeoCarrierGeometry.lean §4, tier 1, no `hn`); not re-declared. -/

/-! ## 1. Parent edge and parameter interval of a carrier segment (tier 0) -/

/-- The parent original edge of the segment of `a`: the edge of the selected-slot image
`selectedMarkPerm S a` (the twin at a selected visit, `a` itself otherwise). -/
def geoCsiEdge {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (a : Mark P) : ZMod n :=
  (geoMarkPosition hP (selectedMarkPerm S a)).1

/-- The start parameter of the segment of `a` on its parent edge. -/
def geoCsiStart {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (a : Mark P) : ℝ :=
  (geoMarkPosition hP (selectedMarkPerm S a)).2.val

omit [NeZero n] in
theorem geoCsiStart_nonneg {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) : 0 ≤ geoCsiStart hP S a :=
  (geoMarkPosition hP (selectedMarkPerm S a)).2.property.1

omit [NeZero n] in
theorem geoCsiStart_lt_one {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) : geoCsiStart hP S a < 1 :=
  (geoMarkPosition hP (selectedMarkPerm S a)).2.property.2

-- [port] `csi_smoothingSuccessor_eq` -> accepted `geoSmoothingSuccessor_apply` (SM/FlatCarriersDefs.lean); not re-declared

theorem geoCsi_evaluation_start {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) :
    traversalEvaluation P (geoMarkPosition hP a) =
      edgePoint P (geoCsiEdge hP S a) (geoCsiStart hP S a) :=
  (geoSelectedMarkPerm_evaluation hP S a).symm

/-- The segment of `a` is the parent-edge parameter interval `[s, t]`, `s < t ≤ 1`, and its end
mark `ρ_S a` is either the mark at parameter `t` of the parent edge or the next original vertex
(`t = 1`). -/
theorem geoCsi_segment_data (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) :
    ∃ t : ℝ, geoCsiStart hP S a < t ∧ t ≤ 1 ∧
      (∀ u : ℝ, geoSmoothingSegment hP S a u =
        edgePoint P (geoCsiEdge hP S a) (geoCsiStart hP S a + u * (t - geoCsiStart hP S a))) ∧
      (((geoMarkPosition hP (geoSmoothingSuccessor hP S a)).1 = geoCsiEdge hP S a ∧
          (geoMarkPosition hP (geoSmoothingSuccessor hP S a)).2.val = t) ∨
        (geoSmoothingSuccessor hP S a = Sum.inl (geoCsiEdge hP S a + 1) ∧ t = 1)) := by
  have hstart := geoCsi_evaluation_start hP S a
  rcases geoMarkSuccessor_position_cases hn hP (selectedMarkPerm S a) with ⟨hi, ht⟩ | hv
  · refine ⟨(geoMarkPosition hP (geoSmoothingSuccessor hP S a)).2.val, ht,
      (geoMarkPosition hP (geoSmoothingSuccessor hP S a)).2.property.2.le, ?_, Or.inl ⟨hi, rfl⟩⟩
    intro u
    have hend : traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) =
        edgePoint P (geoCsiEdge hP S a)
          (geoMarkPosition hP (geoSmoothingSuccessor hP S a)).2.val := by
      unfold traversalEvaluation
      rw [geoSmoothingSuccessor_apply, hi]
      rfl
    unfold geoSmoothingSegment
    rw [hstart, hend, edgePoint_affine]
  · refine ⟨1, geoCsiStart_lt_one hP S a, le_rfl, ?_, Or.inr ⟨hv, rfl⟩⟩
    intro u
    have hend : traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) =
        edgePoint P (geoCsiEdge hP S a) 1 := by
      rw [geoSmoothingSuccessor_apply, hv, geoMarkPosition_evaluation_vertex, edgePoint_one]
      rfl
    unfold geoSmoothingSegment
    rw [hstart, hend, edgePoint_affine]

/-! ## 2. No mark in the parameter gap of a segment (tier 0) -/

/-- No mark lies on the parent edge of the segment of `a` strictly between its start parameter
and its end parameter (the segment is a *consecutive* piece of the marked circle). The end
datum is either form of `geoCsi_segment_data`. -/
theorem geoCsi_no_mark_in_gap (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a m : Mark P) (t : ℝ)
    (hdata : ((geoMarkPosition hP (geoSmoothingSuccessor hP S a)).1 = geoCsiEdge hP S a ∧
          (geoMarkPosition hP (geoSmoothingSuccessor hP S a)).2.val = t) ∨
        (geoSmoothingSuccessor hP S a = Sum.inl (geoCsiEdge hP S a + 1) ∧ t = 1))
    (hme : (geoMarkPosition hP m).1 = geoCsiEdge hP S a)
    (hlo : geoCsiStart hP S a < (geoMarkPosition hP m).2.val)
    (hhi : (geoMarkPosition hP m).2.val < t) : False := by
  have : Fact (1 < n) := ⟨by omega⟩
  set a' := selectedMarkPerm S a with ha'
  set i := geoCsiEdge hP S a with hi
  have hnb := geoMarkSuccessor_no_mark_between hP a' m
  rw [← geoSmoothingSuccessor_apply] at hnb
  apply hnb
  rw [← traversalBetween_shift i]
  have hp : traversalShift i (geoMarkPosition hP a') = ((0 : ZMod n), (geoMarkPosition hP a').2) := by
    simp [traversalShift, i, geoCsiEdge, a']
  have hq : traversalShift i (geoMarkPosition hP m) = ((0 : ZMod n), (geoMarkPosition hP m).2) := by
    apply Prod.ext
    · change (geoMarkPosition hP m).1 - i = 0
      rw [hme]
      exact sub_self _
    · rfl
  have hk0 : ∀ s : Set.Ico (0 : ℝ) 1, traversalKey ((0 : ZMod n), s) = s.val := by
    intro s
    simp [traversalKey]
  rw [hp, hq]
  rcases hdata with ⟨hre, hrt⟩ | ⟨hv, ht1⟩
  · have hr : traversalShift i (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) =
        ((0 : ZMod n), (geoMarkPosition hP (geoSmoothingSuccessor hP S a)).2) := by
      apply Prod.ext
      · change (geoMarkPosition hP (geoSmoothingSuccessor hP S a)).1 - i = 0
        rw [hre]
        exact sub_self _
      · rfl
    rw [hr]
    left
    rw [hk0, hk0, hk0]
    exact ⟨hlo, hrt ▸ hhi⟩
  · let z : Set.Ico (0 : ℝ) 1 := ⟨0, le_rfl, zero_lt_one⟩
    have hr : traversalShift i (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) =
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

/-! ## 3. Distinct segments on one parent edge have disjoint half-open parameter intervals (tier 0) -/

/-- Auxiliary: with `geoCsiStart a < geoCsiStart b` on a common parent edge, the half-open pieces
`σ_a([0,1))` and `σ_b([0,1))` are disjoint, since the start mark of `b` would otherwise lie in
the gap of `a`. -/
theorem geoCsi_same_edge_disjoint_of_lt (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a b : Mark P)
    (he : geoCsiEdge hP S a = geoCsiEdge hP S b)
    (hs : geoCsiStart hP S a < geoCsiStart hP S b) {u v : ℝ}
    (_hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (_hv1 : v < 1) :
    geoSmoothingSegment hP S a u ≠ geoSmoothingSegment hP S b v := by
  intro h
  obtain ⟨ta, hsta, hta1, hfa, hdata⟩ := geoCsi_segment_data hn hP S a
  obtain ⟨tb, hstb, htb1, hfb, _⟩ := geoCsi_segment_data hn hP S b
  rw [hfa u, hfb v, he] at h
  have hr := edgePoint_injective (hP.1 (geoCsiEdge hP S b)) h
  have hgap : u * (ta - geoCsiStart hP S a) < ta - geoCsiStart hP S a := by
    have := sub_pos.mpr hsta
    nlinarith
  have hvb : 0 ≤ v * (tb - geoCsiStart hP S b) := mul_nonneg hv0 (sub_pos.mpr hstb).le
  refine geoCsi_no_mark_in_gap hn hP S a (selectedMarkPerm S b) ta hdata he.symm hs ?_
  change geoCsiStart hP S b < ta
  linarith

/-- Two distinct marks with the same parent edge trace disjoint half-open pieces of that edge
("distinct traversal subsegments of one original edge have disjoint interiors"). -/
theorem geoCsi_same_edge_disjoint (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) {a b : Mark P} (hab : a ≠ b)
    (he : geoCsiEdge hP S a = geoCsiEdge hP S b) {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    geoSmoothingSegment hP S a u ≠ geoSmoothingSegment hP S b v := by
  have hs : geoCsiStart hP S a ≠ geoCsiStart hP S b := by
    intro hs
    apply hab
    have hpos : geoMarkPosition hP (selectedMarkPerm S a) =
        geoMarkPosition hP (selectedMarkPerm S b) :=
      Prod.ext he (Subtype.ext hs)
    have h1 := geoMarkPosition_injective hP hpos
    have h2 := congrArg (selectedMarkPerm S) h1
    rwa [selectedMarkPerm_involutive, selectedMarkPerm_involutive] at h2
  rcases lt_or_gt_of_ne hs with hlt | hgt
  · exact geoCsi_same_edge_disjoint_of_lt hn hP S a b he hlt hu0 hu1 hv0 hv1
  · exact fun h => geoCsi_same_edge_disjoint_of_lt hn hP S b a he.symm hgt hv0 hv1 hu0 hu1 h.symm

/-! ## 4. Meetings of two distinct original edges (tier 1)

The prototype (work/drafts/cvdom/CarrierGeometry.lean §4) stated these on the dropped
`CornerGeometry` (tier 2) because the source consumes `g1_adjacent_intersection` /
`turns_adjacent_intersection`. Ruling R4: at tier 1 the adjacent case is U0's fold-back exclusion
`CarrierGeometry.adjacent_edges_meet hn`, so both lemmas hold for `hG : CarrierGeometry P` (and
now take `hn : 3 ≤ n`). -/

omit [NeZero n] in
/-- A common point of two distinct closed edges is an original vertex (adjacent edges, fold-back
exclusion) or the crossing point of the crossing `{i, j}` (remote edges). Tier-1 form of
`csi_edgeSegment_meet` (CarrierSelfIntersections.lean:238). -/
theorem cg_edgeSegment_meet (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {i j : ZMod n} (hij : i ≠ j) {x : Plane}
    (hxi : x ∈ edgeSegment P i) (hxj : x ∈ edgeSegment P j) :
    (∃ k : ZMod n, x = P k) ∨ ∃ c : Crossing P, c.val = {i, j} ∧ x = crossingPoint c := by
  by_cases hadj : adjacent i j
  · left
    rcases hG.adjacent_edges_meet hn hij hadj with ⟨_, hint⟩ | ⟨_, hint⟩
    · have hx : x ∈ edgeSegment P i ∩ edgeSegment P j := ⟨hxi, hxj⟩
      rw [hint] at hx
      exact ⟨j, hx⟩
    · have hx : x ∈ edgeSegment P i ∩ edgeSegment P j := ⟨hxi, hxj⟩
      rw [hint] at hx
      exact ⟨i, hx⟩
  · right
    have hc : IsCrossing P {i, j} := ⟨i, j, rfl, hadj, ⟨x, hxi, hxj⟩⟩
    refine ⟨⟨{i, j}, hc⟩, rfl, ?_⟩
    apply crossingPoint_unique_of_geometry hG.cg ⟨{i, j}, hc⟩ x
    intro k hk
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hxi
    · exact hxj

omit [NeZero n] in
/-- A crossing point lies on a closed edge only if that edge is one of its two edges
(`crossingPoint_injective_of_geometry`, and vertices are excluded). Tier-1 form of
`csi_edge_mem_of_crossingPoint_mem` (CarrierSelfIntersections.lean:264). -/
theorem cg_edge_mem_of_crossingPoint_mem (hn : 3 ≤ n) {P : LabelledTuple n}
    (hG : CarrierGeometry P) (c : Crossing P) {e : ZMod n}
    (hx : crossingPoint c ∈ edgeSegment P e) : e ∈ c.val := by
  obtain ⟨i, j, hs, _, _⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  by_contra he
  have hei : e ≠ i := fun h => he (h ▸ hi)
  rcases cg_edgeSegment_meet hn hG hei hx (crossingPoint_mem c i hi) with ⟨k, hk⟩ | ⟨c', hc', hx'⟩
  · exact cg_crossingPoint_ne_vertex hG c k hk
  · have hcc := crossingPoint_injective_of_geometry hG.cg hx'
    apply he
    rw [hcc, hc']
    simp

/-! ## 5. Parameters of a vertex and of a crossing point on a segment (tier 1) -/

/-- An original vertex `P k` is the point `σ_a(u)`, `0 ≤ u < 1`, only for `a = k` and `u = 0`. -/
theorem geoCsi_trace_eq_vertex (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (k : ZMod n) (h : geoSmoothingSegment hG.cg S a u = P k) : a = Sum.inl k ∧ u = 0 := by
  obtain ⟨t, hst, ht1, hf, _⟩ := geoCsi_segment_data hn hG.cg S a
  set e := geoCsiEdge hG.cg S a with he
  set s := geoCsiStart hG.cg S a with hs
  have hs0 : 0 ≤ s := geoCsiStart_nonneg hG.cg S a
  rw [hf u] at h
  have hne : edge P e ≠ 0 := hG.cg.1 e
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
    have hpos : geoMarkPosition hG.cg (selectedMarkPerm S a) =
        geoMarkPosition hG.cg (Sum.inl e) := by
      rw [geoMarkPosition_vertex]
      exact Prod.ext rfl (Subtype.ext hsz)
    have h1 := geoMarkPosition_injective hG.cg hpos
    have h2 := congrArg (selectedMarkPerm S) h1
    rwa [selectedMarkPerm_involutive, selectedMarkPerm_vertex] at h2
  · by_cases hk1 : k = e + 1
    · rw [hk1] at h
      have h1 : edgePoint P e (s + u * (t - s)) = edgePoint P e 1 := by rw [edgePoint_one]; exact h
      have hr := edgePoint_injective hne h1
      linarith
    · exfalso
      exact hG.vertex_not_mem_edge hk0 hk1 ⟨s + u * (t - s), hr0, hrt.le.trans ht1, h.symm⟩

/-- The crossing point of `c` is the point `σ_a(u)`, `0 ≤ u < 1`, only for `u = 0` and `a` a
visit of `c`: the visit of `c` on the parent edge is a mark, so it cannot lie in the gap of the
segment, hence it is the start mark. -/
theorem geoCsi_trace_eq_crossingPoint (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (c : Crossing P) (h : geoSmoothingSegment hG.cg S a u = crossingPoint c) :
    u = 0 ∧ ∃ w : Visit P, w.1 = c ∧ a = Sum.inr w := by
  obtain ⟨t, hst, ht1, hf, hdata⟩ := geoCsi_segment_data hn hG.cg S a
  set e := geoCsiEdge hG.cg S a with he
  set s := geoCsiStart hG.cg S a with hs
  have hs0 : 0 ≤ s := geoCsiStart_nonneg hG.cg S a
  rw [hf u] at h
  have hne : edge P e ≠ 0 := hG.cg.1 e
  have hr0 : 0 ≤ s + u * (t - s) := add_nonneg hs0 (mul_nonneg hu0 (sub_pos.mpr hst).le)
  have hrt : s + u * (t - s) < t := by
    have := sub_pos.mpr hst
    nlinarith
  have hmem : crossingPoint c ∈ edgeSegment P e :=
    ⟨s + u * (t - s), hr0, hrt.le.trans ht1, h.symm⟩
  have hec : e ∈ c.val := cg_edge_mem_of_crossingPoint_mem hn hG c hmem
  let w0 : Visit P := ⟨c, ⟨e, hec⟩⟩
  have hw0 : crossingPoint c = edgePoint P e (visitParameter w0) :=
    (crossingParameter_spec c e hec).2.2
  rw [hw0] at h
  have hr := edgePoint_injective hne h
  have hpos0 : geoMarkPosition hG.cg (Sum.inr w0) = (e, ⟨visitParameter w0,
      (crossingParameter_interior_of_geometry hG.cg c e hec).1.le,
      (crossingParameter_interior_of_geometry hG.cg c e hec).2⟩) := rfl
  have hnlt : ¬ s < visitParameter w0 := by
    intro hlt
    refine geoCsi_no_mark_in_gap hn hG.cg S a (Sum.inr w0) t hdata rfl hlt ?_
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
  have hpos : geoMarkPosition hG.cg (selectedMarkPerm S a) = geoMarkPosition hG.cg (Sum.inr w0) := by
    rw [hpos0]
    exact Prod.ext rfl (Subtype.ext hsr)
  have h1 := geoMarkPosition_injective hG.cg hpos
  have h2 := congrArg (selectedMarkPerm S) h1
  rwa [selectedMarkPerm_involutive, selectedMarkPerm_visit] at h2

/-! ## 6. The core meeting theorem (tier 1) -/

/-- **Two distinct half-open segments meet only at a crossing point, at their start marks,
which are the two visits of that crossing.** For marks `a ≠ b` and parameters `u, v ∈ [0,1)`
with `σ_a(u) = σ_b(v)`: `u = v = 0`, the point is `crossingPoint c` for a crossing `c`, and
`a`, `b` are visits of `c`. (No ownership or independence hypothesis is needed.) -/
theorem geoCsi_trace_meet (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    (S : Finset (Crossing P)) {a b : Mark P} (hab : a ≠ b) {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (h : geoSmoothingSegment hG.cg S a u = geoSmoothingSegment hG.cg S b v) :
    u = 0 ∧ v = 0 ∧ ∃ c : Crossing P, geoSmoothingSegment hG.cg S a u = crossingPoint c ∧
      (∃ w : Visit P, w.1 = c ∧ a = Sum.inr w) ∧ (∃ w' : Visit P, w'.1 = c ∧ b = Sum.inr w') := by
  by_cases he : geoCsiEdge hG.cg S a = geoCsiEdge hG.cg S b
  · exact (geoCsi_same_edge_disjoint hn hG.cg S hab he hu0 hu1 hv0 hv1 h).elim
  · have hxa : geoSmoothingSegment hG.cg S a u ∈ edgeSegment P (geoCsiEdge hG.cg S a) :=
      geoSmoothingSegment_mem_edgeSegment hG.cg S a u hu0 hu1.le
    have hxb : geoSmoothingSegment hG.cg S a u ∈ edgeSegment P (geoCsiEdge hG.cg S b) := by
      rw [h]
      exact geoSmoothingSegment_mem_edgeSegment hG.cg S b v hv0 hv1.le
    rcases cg_edgeSegment_meet hn hG he hxa hxb with ⟨k, hk⟩ | ⟨c, _, hc⟩
    · exfalso
      have ha := (geoCsi_trace_eq_vertex hn hG S a hu0 hu1 k hk).1
      have hb := (geoCsi_trace_eq_vertex hn hG S b hv0 hv1 k (h ▸ hk)).1
      exact hab (ha.trans hb.symm)
    · obtain ⟨hu, w, hw, ha⟩ := geoCsi_trace_eq_crossingPoint hn hG S a hu0 hu1 c hc
      obtain ⟨hv, w', hw', hb⟩ := geoCsi_trace_eq_crossingPoint hn hG S b hv0 hv1 c (h ▸ hc)
      exact ⟨hu, hv, c, hc, ⟨w, hw, ha⟩, ⟨w', hw', hb⟩⟩

/-! ## 7. The traced closed curve of a carrier and its self-intersections -/

/-- A parameter of the traced closed curve of the carrier `q`: a mark `a` owned by `q` together
with a parameter `u ∈ [0,1)` of the segment of `a` (from `a` to `ρ_S a`). The half-open pieces
parametrize the concatenation of the segments of `q` bijectively: the joint
`σ_a(1) = σ_{ρ_S a}(0)` is represented once, by `(ρ_S a, 0)`. (Port of `IsCarrierParameter`.) -/
def GeoIsCarrierParameter {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (p : Mark P × ℝ) : Prop :=
  geoOwner hP S p.1 = q ∧ 0 ≤ p.2 ∧ p.2 < 1

/-- The point of the plane traced at the parameter `p = (a, u)`: `σ_a(u)`. (Port of `carrierTrace`.) -/
def geoCarrierTrace {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (p : Mark P × ℝ) : Plane :=
  geoSmoothingSegment hP S p.1 p.2

/-- `x` is a self-intersection of the carrier `q`: the traced closed curve of `q` passes through
`x` at (at least) two distinct parameters. (Port of `IsSelfIntersection`.) -/
def GeoIsSelfIntersection {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (x : Plane) : Prop :=
  ∃ p p' : Mark P × ℝ, GeoIsCarrierParameter hP S q p ∧ GeoIsCarrierParameter hP S q p' ∧
    p ≠ p' ∧ geoCarrierTrace hP S p = x ∧ geoCarrierTrace hP S p' = x

/-- `x` is a triple point of the carrier `q`: three distinct parameters trace `x`.
(Port of `IsTriplePoint`.) -/
def GeoIsTriplePoint {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (x : Plane) : Prop :=
  ∃ p p' p'' : Mark P × ℝ, GeoIsCarrierParameter hP S q p ∧ GeoIsCarrierParameter hP S q p' ∧
    GeoIsCarrierParameter hP S q p'' ∧ p ≠ p' ∧ p ≠ p'' ∧ p' ≠ p'' ∧
    geoCarrierTrace hP S p = x ∧ geoCarrierTrace hP S p' = x ∧ geoCarrierTrace hP S p'' = x

/-- Distinct parameters tracing the same point have distinct marks (each segment is injective). -/
theorem geoCsi_mark_ne_of_param_ne (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) {p p' : Mark P × ℝ} (hne : p ≠ p')
    (h : geoCarrierTrace hP S p = geoCarrierTrace hP S p') : p.1 ≠ p'.1 := by
  intro hm
  apply hne
  have h' : geoSmoothingSegment hP S p.1 p.2 = geoSmoothingSegment hP S p.1 p'.2 := by
    unfold geoCarrierTrace at h
    rw [h, hm]
  exact Prod.ext hm (geoSmoothingSegment_injective hn hP S p.1 h')

/-- The parameters of `q` tracing the crossing point of `c` are exactly `(w, 0)` for the visits
`w` of `c` owned by `q`: a carrier passes through a crossing point once for each visit of the
crossing assigned to it. -/
theorem geo_carrier_crossingPoint_parameters (hn : 3 ≤ n) {P : LabelledTuple n}
    (hG : CarrierGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hG.cg S)
    (c : Crossing P) (p : Mark P × ℝ) :
    (GeoIsCarrierParameter hG.cg S q p ∧ geoCarrierTrace hG.cg S p = crossingPoint c) ↔
      ∃ w : Visit P, w.1 = c ∧ geoOwner hG.cg S (Sum.inr w) = q ∧ p = (Sum.inr w, 0) := by
  constructor
  · rintro ⟨⟨hq, hu0, hu1⟩, hx⟩
    obtain ⟨hu, w, hw, ha⟩ := geoCsi_trace_eq_crossingPoint hn hG S p.1 hu0 hu1 c hx
    refine ⟨w, hw, ?_, Prod.ext ha hu⟩
    rw [← ha]
    exact hq
  · rintro ⟨w, hw, hq, rfl⟩
    refine ⟨⟨hq, le_rfl, zero_lt_one⟩, ?_⟩
    change geoSmoothingSegment hG.cg S (Sum.inr w) 0 = crossingPoint c
    rw [geoSmoothingSegment_zero, geoMarkPosition_evaluation_visit, hw]

/-- The parameters of `q` tracing the original vertex `P k` are exactly `(k, 0)` when `q` owns
the vertex mark `k`: a carrier passes through an original vertex at most once. -/
theorem geo_carrier_vertex_parameters (hn : 3 ≤ n) {P : LabelledTuple n}
    (hG : CarrierGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hG.cg S)
    (k : ZMod n) (p : Mark P × ℝ) :
    (GeoIsCarrierParameter hG.cg S q p ∧ geoCarrierTrace hG.cg S p = P k) ↔
      geoOwner hG.cg S (Sum.inl k) = q ∧ p = (Sum.inl k, 0) := by
  constructor
  · rintro ⟨⟨hq, hu0, hu1⟩, hx⟩
    obtain ⟨ha, hu⟩ := geoCsi_trace_eq_vertex hn hG S p.1 hu0 hu1 k hx
    refine ⟨?_, Prod.ext ha hu⟩
    rw [← ha]
    exact hq
  · rintro ⟨hq, rfl⟩
    refine ⟨⟨hq, le_rfl, zero_lt_one⟩, ?_⟩
    change geoSmoothingSegment hG.cg S (Sum.inl k) 0 = P k
    rw [geoSmoothingSegment_zero, geoMarkPosition_evaluation_vertex]

/-- Two distinct marks owned by `q` whose half-open segments meet do so at the crossing point
of a crossing of `q` (an unselected crossing both of whose visits are owned by `q`); the selected
case is excluded because the two visits of a selected crossing have different owners
(`geo_selected_visits_separated`, U1a). -/
theorem geoCsi_owned_marks_meet (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)
    {a b : Mark P} (ha : geoOwner hG.cg S a = q) (hb : geoOwner hG.cg S b = q) (hab : a ≠ b)
    {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (h : geoSmoothingSegment hG.cg S a u = geoSmoothingSegment hG.cg S b v) :
    ∃ c ∈ geoCarrierCrossings hG.cg S q, geoSmoothingSegment hG.cg S a u = crossingPoint c := by
  obtain ⟨_, _, c, hc, ⟨w, hw, rfl⟩, ⟨w', hw', rfl⟩⟩ :=
    geoCsi_trace_meet hn hG S hab hu0 hu1 hv0 hv1 h
  have hww' : w' ≠ w := fun he => hab (congrArg Sum.inr he).symm
  have htw : w' = visitTwin w := visitTwin_unique w w' (hw'.trans hw.symm) hww'
  have hcS : c ∉ S := by
    intro hcS
    apply geo_selected_visits_separated hG.cg hS w (hw ▸ hcS)
    rw [ha, ← htw, hb]
  refine ⟨c, ?_, hc⟩
  rw [mem_geoCarrierCrossings]
  refine ⟨hcS, ?_⟩
  intro v hv
  rcases visit_eq_or_twin w v (hv.trans hw.symm) with rfl | rfl
  · exact ha
  · rw [← htw]
    exact hb

/-- **lem:carriers (iii), first sentence.** For an independent `S`, the self-intersections of
the carrier `q` are exactly the crossing points of the crossings of `q`
(`geoCarrierCrossings hP S q`: the unselected crossings both of whose visits are assigned to `q`). -/
theorem geo_carrier_selfIntersection_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)
    (x : Plane) :
    GeoIsSelfIntersection hG.cg S q x ↔
      ∃ c ∈ geoCarrierCrossings hG.cg S q, x = crossingPoint c := by
  constructor
  · rintro ⟨p, p', ⟨hq, hu0, hu1⟩, ⟨hq', hv0, hv1⟩, hne, hx, hx'⟩
    have hab : p.1 ≠ p'.1 := geoCsi_mark_ne_of_param_ne hn hG.cg S hne (hx.trans hx'.symm)
    obtain ⟨c, hc, he⟩ := geoCsi_owned_marks_meet hn hG hS q hq hq' hab hu0 hu1 hv0 hv1
      (hx.trans hx'.symm)
    exact ⟨c, hc, hx.symm.trans he⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨i, _, _⟩ := crossing_visits_exist c
    let w : Visit P := ⟨c, i⟩
    have hmem := (mem_geoCarrierCrossings hG.cg S q c).mp hc
    have hw : geoOwner hG.cg S (Sum.inr w) = q := hmem.2 w rfl
    have hw' : geoOwner hG.cg S (Sum.inr (visitTwin w)) = q := hmem.2 (visitTwin w) rfl
    refine ⟨(Sum.inr w, 0), (Sum.inr (visitTwin w), 0), ⟨hw, le_rfl, zero_lt_one⟩,
      ⟨hw', le_rfl, zero_lt_one⟩, ?_, ?_, ?_⟩
    · intro he
      exact visitTwin_ne w (Sum.inr.inj (congrArg Prod.fst he)).symm
    · change geoSmoothingSegment hG.cg S (Sum.inr w) 0 = crossingPoint c
      rw [geoSmoothingSegment_zero, geoMarkPosition_evaluation_visit]
    · change geoSmoothingSegment hG.cg S (Sum.inr (visitTwin w)) 0 = crossingPoint c
      rw [geoSmoothingSegment_zero, geoMarkPosition_evaluation_visit, visitTwin_crossing]

/-- A selected crossing point is a self-intersection of no carrier: "a single carrier passes
through that smoothing point only once". -/
theorem geo_carrier_selected_not_selfIntersection (hn : 3 ≤ n) {P : LabelledTuple n}
    (hG : CarrierGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S)
    (q : GeoComponent hG.cg S) {c : Crossing P} (hc : c ∈ S) :
    ¬ GeoIsSelfIntersection hG.cg S q (crossingPoint c) := by
  intro h
  obtain ⟨c', hc', he⟩ := (geo_carrier_selfIntersection_iff hn hG hS q _).mp h
  have hcc := crossingPoint_injective_of_geometry hG.cg he
  exact geo_selected_not_mem_carrierCrossings hG.cg S q hc (hcc ▸ hc')

/-- An original vertex is a self-intersection of no carrier. -/
theorem geo_carrier_vertex_not_selfIntersection (hn : 3 ≤ n) {P : LabelledTuple n}
    (hG : CarrierGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hG.cg S) (k : ZMod n) :
    ¬ GeoIsSelfIntersection hG.cg S q (P k) := by
  rintro ⟨p, p', hp, hp', hne, hx, hx'⟩
  have h1 := ((geo_carrier_vertex_parameters hn hG S q k p).mp ⟨hp, hx⟩).2
  have h2 := ((geo_carrier_vertex_parameters hn hG S q k p').mp ⟨hp', hx'⟩).2
  exact hne (h1.trans h2.symm)

/-- **lem:carriers (iii): "no carrier has a triple point."** Three distinct parameters cannot
trace one point: any two of them are the two visits of one crossing, and a crossing has only
two visits. (No independence hypothesis is needed.) -/
theorem geo_carrier_no_triple_point (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hG.cg S) (x : Plane) :
    ¬ GeoIsTriplePoint hG.cg S q x := by
  rintro ⟨p, p', p'', ⟨_, hu0, hu1⟩, ⟨_, hv0, hv1⟩, ⟨_, hw0, hw1⟩, h01, h02, h12, hx, hx', hx''⟩
  have hab : p.1 ≠ p'.1 := geoCsi_mark_ne_of_param_ne hn hG.cg S h01 (hx.trans hx'.symm)
  have had : p.1 ≠ p''.1 := geoCsi_mark_ne_of_param_ne hn hG.cg S h02 (hx.trans hx''.symm)
  have hbd : p'.1 ≠ p''.1 := geoCsi_mark_ne_of_param_ne hn hG.cg S h12 (hx'.trans hx''.symm)
  obtain ⟨_, _, c, _, ⟨wa, hwa, ha⟩, ⟨wb, hwb, hb⟩⟩ :=
    geoCsi_trace_meet hn hG S hab hu0 hu1 hv0 hv1 (hx.trans hx'.symm)
  obtain ⟨_, _, c', _, ⟨wa', hwa', ha'⟩, ⟨wd, hwd, hd⟩⟩ :=
    geoCsi_trace_meet hn hG S had hu0 hu1 hw0 hw1 (hx.trans hx''.symm)
  have hwaa : wa' = wa := Sum.inr.inj (ha'.symm.trans ha)
  have hcc : c' = c := by rw [← hwa', hwaa, hwa]
  have hwb' : wb = visitTwin wa :=
    visitTwin_unique wa wb (hwb.trans hwa.symm) (fun he => hab (by rw [ha, hb, he]))
  have hwd' : wd = visitTwin wa :=
    visitTwin_unique wa wd (by rw [hwd, hcc, hwa]) (fun he => had (by rw [ha, hd, he]))
  exact hbd (by rw [hb, hd, hwb', hwd'])

/-- A crossing `c` of `q` is passed exactly twice by `q`: its parameters are precisely
`(w, 0)` and `(visitTwin w, 0)` for the two visits of `c`. -/
theorem geo_carrier_crossing_two_passes (hn : 3 ≤ n) {P : LabelledTuple n}
    (hG : CarrierGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hG.cg S)
    {c : Crossing P} (hc : c ∈ geoCarrierCrossings hG.cg S q) (w : Visit P) (hw : w.1 = c)
    (p : Mark P × ℝ) :
    (GeoIsCarrierParameter hG.cg S q p ∧ geoCarrierTrace hG.cg S p = crossingPoint c) ↔
      (p = (Sum.inr w, 0) ∨ p = (Sum.inr (visitTwin w), 0)) := by
  have hmem := (mem_geoCarrierCrossings hG.cg S q c).mp hc
  rw [geo_carrier_crossingPoint_parameters hn hG]
  constructor
  · rintro ⟨w', hw', _, rfl⟩
    rcases visit_eq_or_twin w w' (hw'.trans hw.symm) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨w, hw, hmem.2 w hw, rfl⟩
    · exact ⟨visitTwin w, (visitTwin_crossing w).trans hw,
        hmem.2 _ ((visitTwin_crossing w).trans hw), rfl⟩

/-! ## 8. Transversality (tier 0) and non-corner status (tier 1) of the self-intersections -/

-- [shared] `csi_det_smul_smul` is hypothesis-free and already in scope (SM.Carrier); not re-declared

omit [NeZero n] in
/-- The two edges of a crossing have transverse directions (`CrossingGeometry` clause 2). Tier-0
form of `csi_crossing_edges_det_ne_zero` (CarrierSelfIntersections.lean:596; consumed
`g1_remote_meeting` → `crossing_det_ne_zero_of_geometry`). -/
theorem geoCsi_crossing_edges_det_ne_zero {P : LabelledTuple n} (hP : CrossingGeometry P)
    (c : Crossing P) {i j : ZMod n} (hi : i ∈ c.val) (hj : j ∈ c.val) (hij : i ≠ j) :
    det (edge P i) (edge P j) ≠ 0 := by
  obtain ⟨i0, j0, hs, _, _⟩ := c.property
  have hc0 : IsCrossing P {i0, j0} := by
    have := c.property
    rwa [hs] at this
  have hd := crossing_det_ne_zero_of_geometry hP hc0
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
and the determinant of the two outgoing germs of `q` at the point is nonzero. Tier 0. -/
theorem geo_carrier_selfIntersection_transverse (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S)
    {c : Crossing P} (hc : c ∈ geoCarrierCrossings hP S q) (w : Visit P) (hw : w.1 = c) :
    det (edge P w.2.val) (edge P (visitTwin w).2.val) ≠ 0 ∧
    (∃ c₁ : ℝ, 0 < c₁ ∧ geoSmoothingSegment hP S (Sum.inr w) 1 -
        geoSmoothingSegment hP S (Sum.inr w) 0 = c₁ • edge P w.2.val) ∧
    (∃ c₁' : ℝ, 0 < c₁' ∧ geoSmoothingSegment hP S (Sum.inr w) 0 -
        geoSmoothingSegment hP S ((geoSmoothingSuccessor hP S).symm (Sum.inr w)) 0 =
          c₁' • edge P w.2.val) ∧
    (∃ c₂ : ℝ, 0 < c₂ ∧ geoSmoothingSegment hP S (Sum.inr (visitTwin w)) 1 -
        geoSmoothingSegment hP S (Sum.inr (visitTwin w)) 0 = c₂ • edge P (visitTwin w).2.val) ∧
    (∃ c₂' : ℝ, 0 < c₂' ∧ geoSmoothingSegment hP S (Sum.inr (visitTwin w)) 0 -
        geoSmoothingSegment hP S ((geoSmoothingSuccessor hP S).symm (Sum.inr (visitTwin w))) 0 =
          c₂' • edge P (visitTwin w).2.val) ∧
    det (geoSmoothingSegment hP S (Sum.inr w) 1 - geoSmoothingSegment hP S (Sum.inr w) 0)
      (geoSmoothingSegment hP S (Sum.inr (visitTwin w)) 1 -
        geoSmoothingSegment hP S (Sum.inr (visitTwin w)) 0) ≠ 0 := by
  subst hw
  have hcS : w.1 ∉ S := ((mem_geoCarrierCrossings hP S q w.1).mp hc).1
  have htS : (visitTwin w).1 ∉ S := by rw [visitTwin_crossing]; exact hcS
  have hdet : det (edge P w.2.val) (edge P (visitTwin w).2.val) ≠ 0 :=
    geoCsi_crossing_edges_det_ne_zero hP w.1 w.2.property
      (by rw [← visitTwin_crossing w]; exact (visitTwin w).2.property) (visitTwin_edge_ne w).symm
  obtain ⟨c₁, hc₁, he₁⟩ := geo_unselected_visit_outgoing_direction hn hP S w hcS
  obtain ⟨c₂, hc₂, he₂⟩ := geo_unselected_visit_outgoing_direction hn hP S (visitTwin w) htS
  have hout₁ : geoSmoothingSegment hP S (Sum.inr w) 1 - geoSmoothingSegment hP S (Sum.inr w) 0 =
      c₁ • edge P w.2.val := by
    rw [geoSmoothingSegment_one, geoSmoothingSegment_zero]; exact he₁
  have hout₂ : geoSmoothingSegment hP S (Sum.inr (visitTwin w)) 1 -
      geoSmoothingSegment hP S (Sum.inr (visitTwin w)) 0 = c₂ • edge P (visitTwin w).2.val := by
    rw [geoSmoothingSegment_one, geoSmoothingSegment_zero]; exact he₂
  refine ⟨hdet, ⟨c₁, hc₁, hout₁⟩, ?_, ⟨c₂, hc₂, hout₂⟩, ?_, ?_⟩
  · obtain ⟨d, hd, he⟩ := geo_visit_incoming_direction hn hP S w
    refine ⟨d, hd, ?_⟩
    rw [geoSmoothingSegment_zero, geoSmoothingSegment_zero]; exact he
  · obtain ⟨d, hd, he⟩ := geo_visit_incoming_direction hn hP S (visitTwin w)
    refine ⟨d, hd, ?_⟩
    rw [geoSmoothingSegment_zero, geoSmoothingSegment_zero]; exact he
  · rw [hout₁, hout₂, csi_det_smul_smul]
    exact mul_ne_zero (mul_ne_zero hc₁.ne' hc₂.ne') hdet

/-- **lem:carriers (iii): "none is a corner."** The crossing point of a crossing of `q` differs
from every original vertex and from every selected crossing point; hence it is the plane point
of no true corner (original vertex mark or selected visit) of any carrier. Tier 1 (the vertex
clause is `cg_crossingPoint_ne_vertex`); no `hn`. -/
theorem geo_carrier_selfIntersection_not_corner {P : LabelledTuple n}
    (hG : CarrierGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hG.cg S)
    {c : Crossing P} (hc : c ∈ geoCarrierCrossings hG.cg S q) :
    (∀ k : ZMod n, crossingPoint c ≠ P k) ∧
    (∀ c' ∈ S, crossingPoint c ≠ crossingPoint c') ∧
    (∀ w : Visit P, w.1 = c → ¬ IsTrueCorner S (Sum.inr w)) ∧
    ∀ m : Mark P, IsTrueCorner S m →
      traversalEvaluation P (geoMarkPosition hG.cg m) ≠ crossingPoint c := by
  have hcS : c ∉ S := ((mem_geoCarrierCrossings hG.cg S q c).mp hc).1
  have hv : ∀ k : ZMod n, crossingPoint c ≠ P k := cg_crossingPoint_ne_vertex hG c
  have hs : ∀ c' ∈ S, crossingPoint c ≠ crossingPoint c' := by
    intro c' hc' he
    exact hcS ((crossingPoint_injective_of_geometry hG.cg he) ▸ hc')
  refine ⟨hv, hs, fun w hw hcorner => hcS (hw ▸ hcorner), ?_⟩
  intro m hm
  cases m with
  | inl k =>
    rw [geoMarkPosition_evaluation_vertex]
    exact (hv k).symm
  | inr v =>
    rw [geoMarkPosition_evaluation_visit]
    exact (hs v.1 hm).symm

/-! ## 9. Closed segments: non-consecutive segments meet only at crossings of the carrier -/

/-- Normalization of a closed-segment parameter `(a, u)`, `u ∈ [0,1]`, to a half-open one:
the point `σ_a(1)` is `σ_{ρ_S a}(0)`. Tier 0, no `hn`. -/
theorem geoCsi_normalize {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∃ a' : Mark P, ∃ u' : ℝ, (a' = a ∨ a' = geoSmoothingSuccessor hP S a) ∧ 0 ≤ u' ∧ u' < 1 ∧
      geoSmoothingSegment hP S a u = geoSmoothingSegment hP S a' u' ∧
      geoOwner hP S a' = geoOwner hP S a := by
  rcases lt_or_eq_of_le hu1 with hlt | heq
  · exact ⟨a, u, Or.inl rfl, hu0, hlt, rfl, rfl⟩
  · subst heq
    exact ⟨geoSmoothingSuccessor hP S a, 0, Or.inr rfl, le_rfl, zero_lt_one,
      geoSmoothingSegment_glue hP S a, geoOwner_successor hP S a⟩

/-- **Two distinct non-consecutive closed segments of one carrier meet only at crossing points
of crossings of that carrier.** For `a ≠ b` owned by `q` with `b ≠ ρ_S a` and `a ≠ ρ_S b`, every
common point of the closed segments `σ_a([0,1])`, `σ_b([0,1])` is `crossingPoint c` for some
`c ∈ geoCarrierCrossings hP S q`. -/
theorem geo_carrier_nonconsecutive_segments_meet (hn : 3 ≤ n) {P : LabelledTuple n}
    (hG : CarrierGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S)
    (q : GeoComponent hG.cg S) {a b : Mark P}
    (ha : geoOwner hG.cg S a = q) (hb : geoOwner hG.cg S b = q)
    (hab : a ≠ b) (hba : b ≠ geoSmoothingSuccessor hG.cg S a)
    (hab' : a ≠ geoSmoothingSuccessor hG.cg S b)
    {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (h : geoSmoothingSegment hG.cg S a u = geoSmoothingSegment hG.cg S b v) :
    ∃ c ∈ geoCarrierCrossings hG.cg S q, geoSmoothingSegment hG.cg S a u = crossingPoint c := by
  obtain ⟨a', u', ha', hu0', hu1', hea, hoa⟩ := geoCsi_normalize hG.cg S a hu0 hu1
  obtain ⟨b', v', hb', hv0', hv1', heb, hob⟩ := geoCsi_normalize hG.cg S b hv0 hv1
  have hne : a' ≠ b' := by
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact hab
    · exact hab'
    · exact hba.symm
    · exact fun he => hab ((geoSmoothingSuccessor hG.cg S).injective he)
  obtain ⟨c, hc, he⟩ := geoCsi_owned_marks_meet hn hG hS q (hoa.trans ha) (hob.trans hb) hne
    hu0' hu1' hv0' hv1' (hea.symm.trans (h.trans heb))
  exact ⟨c, hc, hea.trans he⟩

/-! ## 10. lem:carriers (iii), geometric part, assembled (the §5 U2c target) -/

/-- **lem:carriers (iii), geometric part** (sm-3-statesum.tex:84-86) on the geometric carrier
lane, tier 1: for a `CarrierGeometry` polygon `P`, `n ≥ 3`, and a geometrically independent `S`,
for every carrier `q`,
(1) its self-intersections are exactly the crossing points of the unselected crossings both of
whose visits are assigned to it (`geoCarrierCrossings hG.cg S q`);
(2) each is transverse: at such a crossing with visits `w`, `visitTwin w`, the two germs of `q`
are positive multiples of the two (transverse) parent edge directions, and the determinant of
the two outgoing germs is nonzero;
(3) none is a corner: it differs from every original vertex and every selected crossing point,
hence from the plane point of every true corner;
(4) `q` has no triple point.
Exact shape of the accepted `CarriersLemmaData.self_intersections` (SM/CarriersLemma.lean) under
`owner ↦ geoOwner`, `carrierCrossings ↦ geoCarrierCrossings`, `smoothingSegment ↦ geoSmoothingSegment`,
`markPosition hn hP.1 ↦ geoMarkPosition hG.cg`, `IsSelfIntersection ↦ GeoIsSelfIntersection`,
`IsTriplePoint ↦ GeoIsTriplePoint`; port of `carrier_selfIntersections`. -/
theorem geo_self_intersections (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S) :
    (∀ x : Plane, GeoIsSelfIntersection hG.cg S q x ↔
      ∃ c ∈ geoCarrierCrossings hG.cg S q, x = crossingPoint c) ∧
    (∀ c ∈ geoCarrierCrossings hG.cg S q, ∀ w : Visit P, w.1 = c →
      det (edge P w.2.val) (edge P (visitTwin w).2.val) ≠ 0 ∧
      (∃ c₁ : ℝ, 0 < c₁ ∧ geoSmoothingSegment hG.cg S (Sum.inr w) 1 -
          geoSmoothingSegment hG.cg S (Sum.inr w) 0 = c₁ • edge P w.2.val) ∧
      (∃ c₂ : ℝ, 0 < c₂ ∧ geoSmoothingSegment hG.cg S (Sum.inr (visitTwin w)) 1 -
          geoSmoothingSegment hG.cg S (Sum.inr (visitTwin w)) 0 = c₂ • edge P (visitTwin w).2.val) ∧
      det (geoSmoothingSegment hG.cg S (Sum.inr w) 1 - geoSmoothingSegment hG.cg S (Sum.inr w) 0)
        (geoSmoothingSegment hG.cg S (Sum.inr (visitTwin w)) 1 -
          geoSmoothingSegment hG.cg S (Sum.inr (visitTwin w)) 0) ≠ 0) ∧
    (∀ c ∈ geoCarrierCrossings hG.cg S q,
      (∀ k : ZMod n, crossingPoint c ≠ P k) ∧
      (∀ c' ∈ S, crossingPoint c ≠ crossingPoint c') ∧
      (∀ w : Visit P, w.1 = c → ¬ IsTrueCorner S (Sum.inr w)) ∧
      ∀ m : Mark P, IsTrueCorner S m →
        traversalEvaluation P (geoMarkPosition hG.cg m) ≠ crossingPoint c) ∧
    (∀ x : Plane, ¬ GeoIsTriplePoint hG.cg S q x) := by
  refine ⟨geo_carrier_selfIntersection_iff hn hG hS q, ?_,
    fun c hc => geo_carrier_selfIntersection_not_corner hG S q hc,
    geo_carrier_no_triple_point hn hG S q⟩
  intro c hc w hw
  obtain ⟨hd, h₁, _, h₂, _, hdet⟩ := geo_carrier_selfIntersection_transverse hn hG.cg S q hc w hw
  exact ⟨hd, h₁, h₂, hdet⟩

/-- The same at tier 2 (`hW : WeakGeneric P`), for consumers holding the printed def:wind binder;
proof irrelevance identifies `(hW.carrierGeometry).cg` with `weak_crossingGeometry hW`. -/
theorem geo_self_intersections_of_weak (hn : 3 ≤ n) {P : LabelledTuple n} (hW : WeakGeneric P)
    {S : Finset (Crossing P)} (hS : GeoIndependent (weak_crossingGeometry hW) S)
    (q : GeoComponent (weak_crossingGeometry hW) S) :
    (∀ x : Plane, GeoIsSelfIntersection (weak_crossingGeometry hW) S q x ↔
      ∃ c ∈ geoCarrierCrossings (weak_crossingGeometry hW) S q, x = crossingPoint c) ∧
    (∀ c ∈ geoCarrierCrossings (weak_crossingGeometry hW) S q, ∀ w : Visit P, w.1 = c →
      det (edge P w.2.val) (edge P (visitTwin w).2.val) ≠ 0 ∧
      (∃ c₁ : ℝ, 0 < c₁ ∧ geoSmoothingSegment (weak_crossingGeometry hW) S (Sum.inr w) 1 -
          geoSmoothingSegment (weak_crossingGeometry hW) S (Sum.inr w) 0 = c₁ • edge P w.2.val) ∧
      (∃ c₂ : ℝ, 0 < c₂ ∧
          geoSmoothingSegment (weak_crossingGeometry hW) S (Sum.inr (visitTwin w)) 1 -
          geoSmoothingSegment (weak_crossingGeometry hW) S (Sum.inr (visitTwin w)) 0 =
            c₂ • edge P (visitTwin w).2.val) ∧
      det (geoSmoothingSegment (weak_crossingGeometry hW) S (Sum.inr w) 1 -
          geoSmoothingSegment (weak_crossingGeometry hW) S (Sum.inr w) 0)
        (geoSmoothingSegment (weak_crossingGeometry hW) S (Sum.inr (visitTwin w)) 1 -
          geoSmoothingSegment (weak_crossingGeometry hW) S (Sum.inr (visitTwin w)) 0) ≠ 0) ∧
    (∀ c ∈ geoCarrierCrossings (weak_crossingGeometry hW) S q,
      (∀ k : ZMod n, crossingPoint c ≠ P k) ∧
      (∀ c' ∈ S, crossingPoint c ≠ crossingPoint c') ∧
      (∀ w : Visit P, w.1 = c → ¬ IsTrueCorner S (Sum.inr w)) ∧
      ∀ m : Mark P, IsTrueCorner S m →
        traversalEvaluation P (geoMarkPosition (weak_crossingGeometry hW) m) ≠ crossingPoint c) ∧
    (∀ x : Plane, ¬ GeoIsTriplePoint (weak_crossingGeometry hW) S q x) :=
  geo_self_intersections hn hW.carrierGeometry hS q

/-! ## 11. Agreement with the accepted lane on SM-generic polygons

Through the accepted §4b agreement lemmas of SM/FlatCarriersDefs.lean / FlatCarriers.lean
(`geoMarkPosition_eq_generic`, `geoSmoothingSegment_eq_generic`, `geoComponentEquivGeneric_owner`);
no new content. Write `hc := generic_crossingGeometry hn hP`, `e := geoComponentEquivGeneric hn hP S`. -/

omit [NeZero n] in
theorem geoCsiEdge_eq_generic (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) :
    geoCsiEdge (generic_crossingGeometry hn hP) S a = csiEdge hn hP S a := by
  unfold geoCsiEdge csiEdge
  rw [geoMarkPosition_eq_generic hn hP]

omit [NeZero n] in
theorem geoCsiStart_eq_generic (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) :
    geoCsiStart (generic_crossingGeometry hn hP) S a = csiStart hn hP S a := by
  unfold geoCsiStart csiStart
  rw [geoMarkPosition_eq_generic hn hP]

theorem geoCarrierTrace_eq_generic (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (p : Mark P × ℝ) :
    geoCarrierTrace (generic_crossingGeometry hn hP) S p = carrierTrace hn hP S p :=
  geoSmoothingSegment_eq_generic hn hP S p.1 p.2

theorem geoIsCarrierParameter_iff_generic (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : GeoComponent (generic_crossingGeometry hn hP) S)
    (p : Mark P × ℝ) :
    GeoIsCarrierParameter (generic_crossingGeometry hn hP) S q p ↔
      IsCarrierParameter hn hP S (geoComponentEquivGeneric hn hP S q) p := by
  unfold GeoIsCarrierParameter IsCarrierParameter
  rw [← geoComponentEquivGeneric_owner hn hP S, (geoComponentEquivGeneric hn hP S).apply_eq_iff_eq]

theorem geoIsSelfIntersection_iff_generic (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : GeoComponent (generic_crossingGeometry hn hP) S) (x : Plane) :
    GeoIsSelfIntersection (generic_crossingGeometry hn hP) S q x ↔
      IsSelfIntersection hn hP S (geoComponentEquivGeneric hn hP S q) x := by
  unfold GeoIsSelfIntersection IsSelfIntersection
  refine exists_congr fun p => exists_congr fun p' => ?_
  rw [geoIsCarrierParameter_iff_generic, geoIsCarrierParameter_iff_generic,
    geoCarrierTrace_eq_generic, geoCarrierTrace_eq_generic]

theorem geoIsTriplePoint_iff_generic (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : GeoComponent (generic_crossingGeometry hn hP) S) (x : Plane) :
    GeoIsTriplePoint (generic_crossingGeometry hn hP) S q x ↔
      IsTriplePoint hn hP S (geoComponentEquivGeneric hn hP S q) x := by
  unfold GeoIsTriplePoint IsTriplePoint
  refine exists_congr fun p => exists_congr fun p' => exists_congr fun p'' => ?_
  rw [geoIsCarrierParameter_iff_generic, geoIsCarrierParameter_iff_generic,
    geoIsCarrierParameter_iff_generic, geoCarrierTrace_eq_generic, geoCarrierTrace_eq_generic,
    geoCarrierTrace_eq_generic]

end
end SM.GeoCarrier
