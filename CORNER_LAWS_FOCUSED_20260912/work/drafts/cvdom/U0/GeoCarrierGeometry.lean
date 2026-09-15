import SM.FlatCarriersDefs
import SM.RegularLocus

/-! # SM/GeoCarrierGeometry.lean — hypothesis tiers of the geometric carrier lane (CV-DOM unit U0)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor, for the CV-DOM decision
(work/drafts/cvdom/DECISION_FINAL.md §0, §3 rulings R1/R3/R4, §5 unit U0). Draft home
work/drafts/cvdom/U0/; intended home work/lean/SM/GeoCarrierGeometry.lean. CV-free (no `CV.*`
import): the CV-side bridges (`CarrierGeometry.ofDiagrammatic`, `.ofCV`,
`carrierGeometry_iff_diagrammatic`, `CV.mem_Ind_iff_geoIndependent`) live in CV/Carriers.lean
(draft work/drafts/cvdom/U0/CVCarrierBridges.lean). No accepted declaration is redefined or
shadowed; everything here is additive.

The Carrier lane's theorems are ported (units U1–U6) onto the ACCEPTED geometric carrier
definitions of SM/FlatCarriersDefs.lean (`SM.GeoCarrier.geo*`, on `hP : CrossingGeometry P`) in
three hypothesis tiers (ruling R1):
* tier 0 — the accepted `CrossingGeometry P` (SM/CrossingGeometry.lean:11): marks, successor,
  carriers, counts, inherited order, noncrossing, pieces, trace;
* tier 1 — NEW `CarrierGeometry P` := `CrossingGeometry P` ∧ "no vertex on a non-incident closed
  edge" (= CV "diagrammatic", `CV.diagrammatic_iff`, n ≥ 3): self-intersections of a carrier,
  regularity of the corner polygon, the positive lift;
* tier 2 — the accepted `WeakGeneric P` (SM/WeakGeneric.lean:11): nonzero turns (def:wind,
  selector_A).

`Generic →(hn) WeakGeneric → CarrierGeometry → CrossingGeometry`. Tier-2 lemmas take
`hW : WeakGeneric P` and use `hW.carrierGeometry` / `weak_crossingGeometry hW`; since the `geo*`
objects are parametrised by a `Prop`, `geoOwner hG.cg S` and `geoOwner (weak_crossingGeometry hW) S`
are definitionally equal (proof irrelevance), so the tiers mix freely.

Contents. §1 the structure and its constructors (`ofWeak`, `ofGeneric hn`,
`WeakGeneric.carrierGeometry`). §2 the tier-1 replacements of the G1 vertex lemmas
(`g1_vertex_not_mem_edge`, `g1_vertex_off_edge_line` in its segment form — the only form the lane
consumes). §3 the fold-back exclusion: two consecutive closed edges meet only at their common corner
(a CV-free copy of the accepted `CV.meet_next_eq_corner`, CV/Setup.lean, stated on the bare vertex
clause), hence `CarrierGeometry.adjacent_edges_meet` — the tier-1 replacement of
`g1_adjacent_intersection` (G1Consequences.lean:47) / `turns_adjacent_intersection`
(WeakGeometry.lean:44) in the exact shape consumed at SM/CarrierSelfIntersections.lean:245 — and,
for ruling R4, `regularPair_succ` / `regular`: a `CarrierGeometry` polygon is `Regular` (n ≥ 3),
the tier-1 fact behind `geoCornerPolygon_regular` at vertex corners. §4 the two §0 lemmas of the
CarrierSelfIntersections port (`cg_vertex_not_mem_edgeInterior`, `cg_crossingPoint_ne_vertex`,
replacing `csi_vertex_not_mem_edgeInterior` / `csi_crossingPoint_ne_vertex`).

Checked with `cd work/lean && lake env lean ../drafts/cvdom/U0/GeoCarrierGeometry.lean`. -/

namespace SM

variable {n : ℕ} {P : LabelledTuple n}

/-! ## 1. Tier 1: `CarrierGeometry` and its constructors -/

/-- Tier 1 of the geometric carrier lane (CV "diagrammatic"): the accepted geometric record domain
`CrossingGeometry P` together with "no vertex of `P` lies on a closed edge not incident to it"
(the third clause of `WeakGeneric`, the last clause of `CV.Diagrammatic`). -/
structure CarrierGeometry (P : LabelledTuple n) : Prop where
  /-- tier 0: the accepted geometric record domain -/
  cg : CrossingGeometry P
  /-- no vertex lies on a closed edge not incident to it -/
  vertex_off : ∀ k e : ZMod n, ¬ incident k e → P k ∉ edgeSegment P e

/-- Tier 2 ⇒ tier 1: weakly generic polygons (SM def:weak) have `CarrierGeometry`. -/
theorem CarrierGeometry.ofWeak (hW : WeakGeneric P) : CarrierGeometry P :=
  ⟨weak_crossingGeometry hW, hW.2.2.1⟩

/-- Dot-notation form of `CarrierGeometry.ofWeak`: `hW.carrierGeometry`. -/
theorem WeakGeneric.carrierGeometry (hW : WeakGeneric P) : CarrierGeometry P :=
  CarrierGeometry.ofWeak hW

/-- SM-generic polygons (def:generic, n ≥ 3) have `CarrierGeometry`. -/
theorem CarrierGeometry.ofGeneric (hn : 3 ≤ n) (hP : Generic P) : CarrierGeometry P :=
  CarrierGeometry.ofWeak (generic_implies_weak hn hP)

/-- Tier 1 ⇒ tier 0 (the field `cg`, named for symmetry with the other constructors). -/
theorem CarrierGeometry.crossingGeometry (hG : CarrierGeometry P) : CrossingGeometry P := hG.cg

/-! ## 2. Tier-1 replacements of the G1 vertex lemmas -/

/-- Tier-1 replacement of `g1_edge_ne_zero` (clause 1 of `CrossingGeometry`). -/
theorem CarrierGeometry.edge_ne_zero (hG : CarrierGeometry P) (i : ZMod n) : edge P i ≠ 0 :=
  hG.cg.1 i

/-- Tier-1 replacement of `g1_vertex_not_mem_edge` (Generic.lean:112): a vertex other than the two
endpoints of an edge is not on that closed edge. -/
theorem CarrierGeometry.vertex_not_mem_edge (hG : CarrierGeometry P) {i k : ZMod n}
    (hk0 : k ≠ i) (hk1 : k ≠ i + 1) : P k ∉ edgeSegment P i :=
  hG.vertex_off k i ((nonincident_iff k i).mpr ⟨hk0, hk1⟩)

/-- Tier-1 replacement of `g1_vertex_off_edge_line` (Generic.lean:103) in its segment form
(`0 ≤ t ≤ 1`); the lane consumes only this form (CarrierSelfIntersections.lean:51 is inside an
`edgeInterior` membership). At tier 1 a vertex MAY lie on the line of a non-incident edge outside
the closed segment, so the full-line statement is not available (nor needed). -/
theorem CarrierGeometry.vertex_ne_edgePoint (hG : CarrierGeometry P) {i k : ZMod n}
    (hk0 : k ≠ i) (hk1 : k ≠ i + 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P k ≠ edgePoint P i t :=
  fun h => hG.vertex_not_mem_edge hk0 hk1 ⟨t, ht0, ht1, h⟩

/-! ## 3. Fold-back exclusion: consecutive edges meet only at their corner (ruling R4) -/

/-- Two closed consecutive edges of a polygon with no vertex on a non-incident closed edge meet only
at their common corner (`n ≥ 3`): a second common point would make the second edge double back, and
then either `P i` lies on `e_{i+1}` or `P (i+2)` lies on `e_i`. CV-free copy of the accepted
`CV.meet_next_eq_corner` (CV/Setup.lean), word for word. -/
theorem meet_next_eq_corner_of_vertex_off (hn : 3 ≤ n)
    (hvert : ∀ k e, ¬ incident k e → P k ∉ edgeSegment P e) (i : ZMod n) {x : Plane}
    (hx : x ∈ edgeSegment P i) (hx' : x ∈ edgeSegment P (i + 1)) : x = P (i + 1) := by
  have : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨s, hs0, hs1, hs⟩ := hx
  obtain ⟨u, hu0, hu1, hu⟩ := hx'
  by_cases hs1' : s = 1
  · rw [hs, hs1', edgePoint_one]
  by_cases hu0' : u = 0
  · rw [hu, hu0', edgePoint_zero]
  have hs1lt : s < 1 := lt_of_le_of_ne hs1 hs1'
  have hu0lt : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu0')
  have hnext : P (i + 1) = P i + edge P i := by simp [edge]
  have hrel : u • edge P (i + 1) = (s - 1) • edge P i := by
    have h1 : P i + s • edge P i = P (i + 1) + u • edge P (i + 1) := hs.symm.trans hu
    rw [hnext] at h1
    rw [sub_smul, one_smul]
    calc u • edge P (i + 1) = (P i + edge P i + u • edge P (i + 1)) - (P i + edge P i) := by abel
      _ = (P i + s • edge P i) - (P i + edge P i) := by rw [h1]
      _ = s • edge P i - edge P i := by abel
  have hdir : edge P (i + 1) = (u⁻¹ * (s - 1)) • edge P i := by
    rw [mul_smul, ← hrel, smul_smul, inv_mul_cancel₀ hu0lt.ne', one_smul]
  have hnot_inc1 : ¬ incident i (i + 1) := by
    rintro (h | h)
    · exact prev_ne_next hn i h.symm
    · exact next_ne_self i h
  have hnot_inc2 : ¬ incident (i + 1 + 1) i := by
    rintro (h | h)
    · rw [add_sub_cancel_right] at h
      exact next_ne_self i h.symm
    · have h2 := prev_ne_next hn (i + 1)
      rw [add_sub_cancel_right] at h2
      exact h2 h
  exfalso
  have hs1ne : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1')
  rcases le_or_gt u (1 - s) with hle | hlt
  · apply hvert i (i + 1) hnot_inc1
    refine ⟨u / (1 - s), div_nonneg hu0 (by linarith), (div_le_one (by linarith)).mpr hle, ?_⟩
    rw [edgePoint, hdir, smul_smul, hnext]
    have hc : u / (1 - s) * (u⁻¹ * (s - 1)) = -1 := by
      field_simp
      ring
    rw [hc, neg_one_smul]
    abel
  · apply hvert (i + 1 + 1) i hnot_inc2
    refine ⟨1 + u⁻¹ * (s - 1), ?_, ?_, ?_⟩
    · have h1 : u⁻¹ * (s - 1) = -((1 - s) / u) := by ring
      have h2 := (div_lt_one hu0lt).mpr hlt
      rw [h1]
      linarith
    · have h1 : u⁻¹ * (s - 1) < 0 := mul_neg_of_pos_of_neg (inv_pos.mpr hu0lt) (by linarith)
      linarith
    · have h2 : P (i + 1 + 1) = P (i + 1) + edge P (i + 1) := by simp [edge]
      rw [edgePoint, h2, hdir, hnext, add_smul, one_smul]
      abel

/-- Tier-1 form of the fold-back exclusion (mirror of the accepted `regular_adjacent_meet`,
SM/CS3.lean:84, with `CarrierGeometry` in place of `Regular`). -/
theorem CarrierGeometry.meet_next_eq_corner (hn : 3 ≤ n) (hG : CarrierGeometry P) (i : ZMod n)
    {x : Plane} (hx : x ∈ edgeSegment P i) (hx' : x ∈ edgeSegment P (i + 1)) : x = P (i + 1) :=
  meet_next_eq_corner_of_vertex_off hn hG.vertex_off i hx hx'

/-- Tier-1 replacement of `g1_successive_intersection` (G1Consequences.lean:20) /
`turns_successive_intersection` (WeakGeometry.lean:22): the closed edges `e_i`, `e_{i+1}` meet
exactly in `P (i+1)`. -/
theorem CarrierGeometry.successive_edges_meet (hn : 3 ≤ n) (hG : CarrierGeometry P)
    (i : ZMod n) : edgeSegment P i ∩ edgeSegment P (i + 1) = {P (i + 1)} := by
  ext x
  constructor
  · rintro ⟨hx, hx'⟩
    exact hG.meet_next_eq_corner hn i hx hx'
  · intro hx
    have hx' : x = P (i + 1) := hx
    subst hx'
    exact ⟨⟨1, by norm_num, le_rfl, (edgePoint_one P i).symm⟩,
      ⟨0, le_rfl, by norm_num, (edgePoint_zero P (i + 1)).symm⟩⟩

/-- Tier-1 replacement of `g1_adjacent_intersection` (G1Consequences.lean:47) and of
`turns_adjacent_intersection` (WeakGeometry.lean:44), in the exact shape consumed at
SM/CarrierSelfIntersections.lean:245 (`csi_edgeSegment_meet`): two distinct adjacent closed edges
meet only in their shared vertex. -/
theorem CarrierGeometry.adjacent_edges_meet (hn : 3 ≤ n) (hG : CarrierGeometry P) {i j : ZMod n}
    (hij : i ≠ j) (hadj : adjacent i j) :
    (j = i + 1 ∧ edgeSegment P i ∩ edgeSegment P j = {P j}) ∨
    (i = j + 1 ∧ edgeSegment P i ∩ edgeSegment P j = {P i}) := by
  rcases adjacent_distinct_cases hij hadj with he | he
  · left
    refine ⟨he, ?_⟩
    subst he
    exact hG.successive_edges_meet hn i
  · right
    refine ⟨he, ?_⟩
    subst he
    rw [Set.inter_comm]
    exact hG.successive_edges_meet hn j

/-- Ruling R4: consecutive edges of a `CarrierGeometry` polygon are a `RegularPair` (`n ≥ 3`) — both
nonzero (clause 1 of `CrossingGeometry`) and never antiparallel: if `e_{i+1} = r • e_i` with
`r < 0`, the point at parameter `1/(1-r)` on both edges is a second common point, against
`meet_next_eq_corner`. -/
theorem CarrierGeometry.regularPair_succ (hn : 3 ≤ n) (hG : CarrierGeometry P) (i : ZMod n) :
    RegularPair (edge P i) (edge P (i + 1)) := by
  refine ⟨hG.cg.1 i, hG.cg.1 (i + 1), ?_⟩
  rintro ⟨r, hr, hre⟩
  have hpos : 0 < 1 - r := by linarith
  have hne : (1 - r) ≠ 0 := hpos.ne'
  have ht0 : 0 < 1 / (1 - r) := one_div_pos.mpr hpos
  have ht1 : 1 / (1 - r) < 1 := by
    rw [div_lt_one hpos]
    linarith
  have hnext : P (i + 1) = P i + edge P i := by simp [edge]
  have hc : (1 : ℝ) + 1 / (1 - r) * r = 1 / (1 - r) := by
    field_simp
    ring
  have hkey : edgePoint P (i + 1) (1 / (1 - r)) = edgePoint P i (1 / (1 - r)) := by
    have h1 : edgePoint P (i + 1) (1 / (1 - r)) = P i + (1 + 1 / (1 - r) * r) • edge P i := by
      rw [edgePoint, hre, hnext, smul_smul, add_smul, one_smul, add_assoc]
    rw [h1, hc, edgePoint]
  have hx : edgePoint P (i + 1) (1 / (1 - r)) = P (i + 1) :=
    hG.meet_next_eq_corner hn i ⟨1 / (1 - r), ht0.le, ht1.le, hkey⟩
      ⟨1 / (1 - r), ht0.le, ht1.le, rfl⟩
  have h0 : edgePoint P (i + 1) (1 / (1 - r)) = edgePoint P (i + 1) 0 := by
    rw [edgePoint_zero]
    exact hx
  exact ht0.ne' (edgePoint_injective (hG.cg.1 (i + 1)) h0)

/-- Ruling R4: a `CarrierGeometry` polygon is `Regular` (`n ≥ 3`) — no zero edge, no fold-back at
a vertex (`Regular` forbids only zero/antiparallel consecutive edges, RegularLocus.lean:12). This is
the tier-1 fact behind `geoCornerPolygon_regular` at vertex corners; at smoothing corners
`det ≠ 0` is clause 2 of `CrossingGeometry`. Compare the accepted `g1_regular` (tier `G1`) and
`CV.Generic.regular_sm`. -/
theorem CarrierGeometry.regular (hn : 3 ≤ n) (hG : CarrierGeometry P) : Regular P := by
  intro i
  have h := hG.regularPair_succ hn (i - 1)
  rwa [sub_add_cancel] at h

/-! ## 4. Vertices are not interior points of edges (CarrierSelfIntersections §0 at tier 1) -/

namespace GeoCarrier

/-- Tier-1 replacement of `csi_vertex_not_mem_edgeInterior` (CarrierSelfIntersections.lean:40;
consumed `g1_edge_ne_zero`, `g1_vertex_off_edge_line` → `hG.cg.1`, `hG.vertex_not_mem_edge`): no
original vertex is an interior point of any edge. -/
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
    · exact hG.vertex_not_mem_edge hk0 hk1 ⟨r, hr0.le, hr1.le, hr⟩

/-- Tier-1 replacement of `csi_crossingPoint_ne_vertex` (CarrierSelfIntersections.lean:60; consumed
`crossingPoint_interior` → `crossingPoint_interior_of_geometry`): a crossing point is never an
original vertex. -/
theorem cg_crossingPoint_ne_vertex (hG : CarrierGeometry P) (c : Crossing P) (k : ZMod n) :
    crossingPoint c ≠ P k := by
  intro he
  obtain ⟨i, j, hs, _, _⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hint := crossingPoint_interior_of_geometry hG.cg c i hi
  rw [he] at hint
  exact cg_vertex_not_mem_edgeInterior hG k i hint

end GeoCarrier

end SM
