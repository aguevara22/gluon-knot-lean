import SM.FlatCarriers
import CV.Setup

/-! # CV-DOM prototype (analyst A, 2026-09-14): `CarrierGeometry` and a literal port

Purpose: measure what the Carrier lane really needs beyond `CrossingGeometry`, and check that the
Generic-consuming lemmas of the lane re-prove over a weaker hypothesis on the accepted geometric
carrier layer `SM.GeoCarrier.*` (SM/FlatCarriersDefs.lean, SM/FlatCarriers.lean).

Two tiers:
* `CarrierGeometry P` = `CrossingGeometry P` + "no vertex on a non-incident closed edge" — exactly
  what CV:lem:carriers (i)–(iv) and lem:piececurve read ("Let P be diagrammatic"): CV.Diagrammatic
  ⇒ CarrierGeometry (`CarrierGeometry.ofDiagrammatic`).
* `CornerGeometry P` = `CarrierGeometry P` + nonzero turns — what def:wind / the corner polygons
  read ("Let P be generic"): CV.Generic ⇒ CornerGeometry (`CornerGeometry.ofCV`), SM.Generic ⇒
  CornerGeometry (`CornerGeometry.ofGeneric`), WeakGeneric ⇔ CornerGeometry.

Ported below (word for word from SM/CarrierSelfIntersections.lean §0–§5, the file that consumes
the most Generic lemmas of the whole lane): `csi_vertex_not_mem_edgeInterior`,
`csi_crossingPoint_ne_vertex`, `csiEdge`, `csiStart`, `csi_segment_data`, `csi_no_mark_in_gap`,
`csi_same_edge_disjoint_of_lt`, `csi_same_edge_disjoint`, `csi_edgeSegment_meet`,
`csi_edge_mem_of_crossingPoint_mem`, `csi_trace_eq_vertex`. Checked with
`cd work/lean && lake env lean ../drafts/cvdom/CarrierGeometry.lean`. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-- Tier 1 (CV "diagrammatic"-level): the geometric record domain plus "no vertex lies on a
non-incident closed edge". -/
structure CarrierGeometry (P : LabelledTuple n) : Prop where
  cg : CrossingGeometry P
  vertex_off : ∀ k e : ZMod n, ¬ incident k e → P k ∉ edgeSegment P e

/-- Tier 2 (CV "generic"-level for the corner polygons): nonzero turns as well. -/
structure CornerGeometry (P : LabelledTuple n) : Prop extends CarrierGeometry P where
  turn_ne : ∀ i : ZMod n, turn P i ≠ 0

omit [NeZero n] in
theorem CarrierGeometry.ofDiagrammatic (hD : CV.Diagrammatic P) : CarrierGeometry P :=
  ⟨hD.crossingGeometry, hD.2.2.2.2⟩

omit [NeZero n] in
theorem CornerGeometry.ofWeak (hW : WeakGeneric P) : CornerGeometry P :=
  ⟨⟨weak_crossingGeometry hW, hW.2.2.1⟩, hW.2.1⟩

omit [NeZero n] in
theorem CornerGeometry.ofGeneric (hn : 3 ≤ n) (hP : Generic P) : CornerGeometry P :=
  .ofWeak (generic_implies_weak hn hP)

theorem CornerGeometry.ofCV (hP : CV.Generic P) : CornerGeometry P :=
  .ofWeak hP.weakGeneric

theorem CarrierGeometry.ofCV (hP : CV.Generic P) : CarrierGeometry P :=
  (CornerGeometry.ofCV hP).toCarrierGeometry

omit [NeZero n] in
/-- The converse: tier 2 is SM's `WeakGeneric` (so nothing new is being introduced). -/
theorem CornerGeometry.weakGeneric (h : CornerGeometry P) : WeakGeneric P := by
  refine ⟨h.cg.1, h.turn_ne, h.vertex_off, ?_, h.cg.2.2⟩
  intro i j hr
  refine ⟨fun x hxi hxj => (h.cg.2.1 i j hr x hxi hxj).2.2, ?_⟩
  intro x y hxi hxj hyi hyj
  exact transverse_segments_unique (h.cg.2.1 i j hr x hxi hxj).2.2 hxi hxj hyi hyj

omit [NeZero n] in
theorem cornerGeometry_iff_weakGeneric : CornerGeometry P ↔ WeakGeneric P :=
  ⟨CornerGeometry.weakGeneric, CornerGeometry.ofWeak⟩

namespace GeoCarrier

open Carrier

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## §0. Vertices are not interior points of edges (port of `csi_vertex_not_mem_edgeInterior`,
`csi_crossingPoint_ne_vertex`; consumed `g1_edge_ne_zero`, `g1_vertex_off_edge_line`,
`crossingPoint_interior` — replaced by `hG.cg.1`, `hG.vertex_off`,
`crossingPoint_interior_of_geometry`). -/

omit [NeZero n] in
theorem cg_vertex_not_mem_edgeInterior (hG : CarrierGeometry P) (k i : ZMod n) :
    P k ∉ edgeInterior P i := by
  rintro ⟨r, hr0, hr1, hr⟩
  have hne : edge P i ≠ 0 := hG.cg.1 i
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
    · exact hG.vertex_off k i ((nonincident_iff k i).mpr ⟨hk0, hk1⟩) ⟨r, hr0.le, hr1.le, hr⟩

omit [NeZero n] in
theorem cg_crossingPoint_ne_vertex (hG : CarrierGeometry P) (c : Crossing P) (k : ZMod n) :
    crossingPoint c ≠ P k := by
  intro he
  obtain ⟨i, j, hs, _, _⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hint := crossingPoint_interior_of_geometry hG.cg c i hi
  rw [he] at hint
  exact cg_vertex_not_mem_edgeInterior hG k i hint

/-! ## §1. Parent edge and parameter interval of a carrier segment (port of `csiEdge`, `csiStart`,
`csi_segment_data`; only `hn hP.1` plumbing changes, no Generic content). -/

def geoCsiEdge (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P) : ZMod n :=
  (geoMarkPosition hP (selectedMarkPerm S a)).1

def geoCsiStart (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P) : ℝ :=
  (geoMarkPosition hP (selectedMarkPerm S a)).2.val

omit [NeZero n] in
theorem geoCsiStart_nonneg (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P) :
    0 ≤ geoCsiStart hP S a :=
  (geoMarkPosition hP (selectedMarkPerm S a)).2.property.1

omit [NeZero n] in
theorem geoCsiStart_lt_one (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P) :
    geoCsiStart hP S a < 1 :=
  (geoMarkPosition hP (selectedMarkPerm S a)).2.property.2

theorem geoCsi_evaluation_start (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P) :
    traversalEvaluation P (geoMarkPosition hP a) =
      edgePoint P (geoCsiEdge hP S a) (geoCsiStart hP S a) :=
  (geoSelectedMarkPerm_evaluation hP S a).symm

theorem geoCsi_segment_data (hn : 3 ≤ n) (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (a : Mark P) :
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

/-! ## §2. No mark in the parameter gap of a segment (port of `csi_no_mark_in_gap`; consumed
`markSuccessor_no_mark_between` → `geoMarkSuccessor_no_mark_between`, accepted in
SM/FlatCarriers.lean). -/

theorem geoCsi_no_mark_in_gap (hn : 3 ≤ n) (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (a m : Mark P) (t : ℝ)
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

/-! ## §3. Distinct segments on one parent edge (port of `csi_same_edge_disjoint_of_lt`,
`csi_same_edge_disjoint`; consumed `g1_edge_ne_zero` → `hP.1`, `markPosition_injective` →
`geoMarkPosition_injective`). -/

theorem geoCsi_same_edge_disjoint_of_lt (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a b : Mark P) (he : geoCsiEdge hP S a = geoCsiEdge hP S b)
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

theorem geoCsi_same_edge_disjoint (hn : 3 ≤ n) (hP : CrossingGeometry P)
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

/-! ## §4. Meetings of two distinct original edges (port of `csi_edgeSegment_meet` — the ONE lane
lemma that needs nonzero turns, tier 2: `g1_adjacent_intersection` → `turns_adjacent_intersection`;
`crossingPoint_unique` → `crossingPoint_unique_of_geometry`; and of `csi_edge_mem_of_crossingPoint_mem`:
`generic_crossingPoint_injective` → `crossingPoint_injective_of_geometry`). -/

omit [NeZero n] in
theorem cg_edgeSegment_meet (hG : CornerGeometry P) {i j : ZMod n} (hij : i ≠ j) {x : Plane}
    (hxi : x ∈ edgeSegment P i) (hxj : x ∈ edgeSegment P j) :
    (∃ k : ZMod n, x = P k) ∨ ∃ c : Crossing P, c.val = {i, j} ∧ x = crossingPoint c := by
  by_cases hadj : adjacent i j
  · left
    rcases turns_adjacent_intersection hG.turn_ne hij hadj with ⟨_, hint⟩ | ⟨_, hint⟩
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
theorem cg_edge_mem_of_crossingPoint_mem (hG : CornerGeometry P) (c : Crossing P) {e : ZMod n}
    (hx : crossingPoint c ∈ edgeSegment P e) : e ∈ c.val := by
  obtain ⟨i, j, hs, _, _⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  by_contra he
  have hei : e ≠ i := fun h => he (h ▸ hi)
  rcases cg_edgeSegment_meet hG hei hx (crossingPoint_mem c i hi) with ⟨k, hk⟩ | ⟨c', hc', hx'⟩
  · exact cg_crossingPoint_ne_vertex hG.toCarrierGeometry c k hk
  · have hcc := crossingPoint_injective_of_geometry hG.cg hx'
    apply he
    rw [hcc, hc']
    simp

/-! ## §5. A vertex on a segment (port of `csi_trace_eq_vertex`; tier 1 suffices). -/

theorem geoCsi_trace_eq_vertex (hn : 3 ≤ n) (hG : CarrierGeometry P) (S : Finset (Crossing P))
    (a : Mark P) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
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
    have hpos : geoMarkPosition hG.cg (selectedMarkPerm S a) = geoMarkPosition hG.cg (Sum.inl e) := by
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
      exact hG.vertex_off k e ((nonincident_iff k e).mpr ⟨hk0, hk1⟩)
        ⟨s + u * (t - s), hr0, hrt.le.trans ht1, h.symm⟩

/-! ## Agreement with the accepted lane on SM-generic polygons (all by the accepted
`SM.FlatCarriersDefs` §4b lemmas; no new content). -/

omit [NeZero n] in
theorem geoCsiEdge_eq_generic (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) :
    geoCsiEdge (generic_crossingGeometry hn hP) S a = csiEdge hn hP S a := by
  unfold geoCsiEdge csiEdge
  rw [geoMarkPosition_eq_generic hn hP]

omit [NeZero n] in
theorem geoCsiStart_eq_generic (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) :
    geoCsiStart (generic_crossingGeometry hn hP) S a = csiStart hn hP S a := by
  unfold geoCsiStart csiStart
  rw [geoMarkPosition_eq_generic hn hP]

/-- On an SM-generic polygon the two hypotheses tiers are the accepted `Generic` read through
`CornerGeometry.ofGeneric`; the accepted definitions are reached by the §4b agreement lemmas
(`geoSmoothingSuccessor_eq_generic`, `geoComponentEquivGeneric`, `geoSmoothingSegment_eq_generic`). -/
example (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P)) :
    geoSmoothingSuccessor (CornerGeometry.ofGeneric hn hP).cg S = smoothingSuccessor hn hP S :=
  geoSmoothingSuccessor_eq_generic hn hP S

end
end GeoCarrier
end SM
