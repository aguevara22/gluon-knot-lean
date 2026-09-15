import SM.GeoCornerPolygon
import SM.GeoCarrierSelfIntersections
import SM.LinkPositiveLift
import SM.LinkDiagramRecord

/-! Ported 2026-09-14 from work/drafts/cvdom/U4/GeoPositiveLift.lean (CV-DOM unit U4: the geo carrier shadow and positive lift at tier 1 (CarrierGeometry) — geoCarrierPolyComp, geoCarrierShadow (generic), geoPositiveLift with its crossing correspondence and writhe — and the literal agreement geoPositiveLift_eq_generic with the accepted positiveLift on SM-generic polygons; REPORT.md in the same directory). Library module, no row. Only this header added. -/

/-! # GeoPositiveLift — the positive lift of a geometric carrier (CV-DOM unit U4, tier 1)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor for the CV-DOM decision
(work/drafts/cvdom/DECISION_FINAL.md §0, §3 rulings R1-R5 (R4: the positive lift is tier 1,
`CarrierGeometry`), §5 row **U4**). Intended home `work/lean/SM/GeoPositiveLift.lean`. Checked with
`cd work/lean && lake env lean ../drafts/cvdom/U4/GeoPositiveLift.lean` (clean, standard axioms).

Re-binding of the accepted positive lift of a carrier, SM/LinkPositiveLift.lean:202-840
(`carrierPolyComp`, `carrierShadow`, the block parametrisation `BlockInterior` … `nonadjacent_meet`,
the four label-level genericity facts, `carrierShadow_generic`, `positiveLift`, its basic lemmas and
the crossing correspondence `carrierCrossingEquiv`), from `hP : SM.Generic P` /
`hS : IsDecomposition hn hP S` / `q : Component hn hP S` onto the ACCEPTED geometric carrier layer of
SM/FlatCarriersDefs.lean (`geoCornerCount`, `geoCornerMark`, `geoCornerPolygon`, `geoCarrierCrossings`,
`geoSmoothingSegment`, `geoSmoothingSuccessor`, `geoOwner`, `GeoIndependent`) at tier 1
`hG : CarrierGeometry P` (SM/GeoCarrierGeometry.lean, U0), on `hS : GeoIndependent hG.cg S`,
`q : GeoComponent hG.cg S`. Inputs: U2b (SM/GeoCornerPolygon.lean: `geoCornerPolygon_block`,
`geoCornerPolygon_edge_smul`, `geoCornerPolygon_regular`, `three_le_geoCornerCount`,
`geoCornerPolygon_edgeSegment`, `geo_pow_owner`, `geo_previous_corner`, `geoCornerMark_exists_of_owner`)
and U2c (SM/GeoCarrierSelfIntersections.lean: `GeoIsCarrierParameter`, `geoCarrierTrace`,
`GeoIsSelfIntersection`, `geoCsi_mark_ne_of_param_ne`, `geoCsi_trace_meet`,
`geo_carrier_selfIntersection_iff`, `geo_carrier_selfIntersection_not_corner`,
`geo_carrier_no_triple_point`, `geoCsi_crossing_edges_det_ne_zero`).

Tiers (ruling R1/R4). The block parametrisation (§2) is tier 0 (`hP : CrossingGeometry P`); the corner
uniqueness lemmas, the meeting lemma, the four genericity facts `geoCornerPolygon_tail_off`,
`geoCornerPolygon_transverse`, `geoCornerPolygon_no_triple` (with U2b's `geoCornerPolygon_regular`),
`geoCarrierShadow_generic`, `geoPositiveLift` and the crossing correspondence (§3-§5) are tier 1.
The one tier-2 site of the source, `consecutive_meet` via `ccpCornerPolygon_det_ne_zero` (nonzero
turns), is replaced by U0's fold-back exclusion `meet_next_eq_corner_of_vertex_off` applied to the
corner polygon itself, whose `vertex_off` clause is `geoCornerPolygon_tail_off` (tier 1) and whose
`3 ≤ k` is `three_le_geoCornerCount` (tier 1) — no tier-2 need arose (risk 3 of §7 discharged).
The `_of_weak` shapes of SM/CSilent.lean (row module, not imported) are recovered by passing
`hW.carrierGeometry`.

§6 is the agreement with the accepted lane on SM-generic polygons, in the strongest form: for
`hP : SM.Generic P`, ANY tier-1 witness `hG : CarrierGeometry P`, `hS' : GeoIndependent hG.cg S`,
`hS : IsDecomposition hn hP S` and `e := geoComponentEquivGeneric hn hP S`,
`geoPositiveLift hn hG hS' q = positiveLift hn hP S (e q) hS` (literal equality of `Diagram`s, via
`geoCarrierPolyComp hn hG hS' q = carrierPolyComp hn hP S (e q) hS` — the corner counts are
propositionally equal by `geoComponentCornerList_eq_generic`, the two polygons are `polyOfList` of
equal lists under equal position maps, so the `PolyComp`s are equal by `subst` — then
`eq_positiveLift_of_isPositive`). Hence the records are equal and `RecordIso` (`RecordIso.refl`),
the shadows and crossing sets agree (`geoCarrierCrossings_eq_generic`), and `SM.presentations`
gives `P (geoPositiveLift …) = P (positiveLift …)` downstream (not stated here: SM/PolynomialBlock.lean
is a row module). No `recastTuple` (SM/CChamber.lean is a row module); the recast-free form of the
polygon agreement is `geoCornerPolygon_apply_eq_generic` (equal corner values at equal `ZMod` values).

No accepted or ported `geo*` name is re-declared (ruling R3; the CS3/CSilent row modules' lemmas
`geoCornerCount_eq_generic`, `geoCornerPolygon_eq_generic`, `geoCornerPolygon_*_of_weak` are neither
imported nor shadowed: the agreement lemmas here carry distinct names). -/

namespace SM.GeoCarrier

open Carrier Link

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## 0. Hypothesis-free congruences (list indices; one-component shadow data of a list polygon) -/

/-- Entries of equal lists at equal indices agree (the two length proofs may differ). -/
theorem getElem_congr_of_eq {α : Type*} {L L' : List α} (h : L = L') {i i' : ℕ} (hii : i = i')
    (hi : i < L.length) (hi' : i' < L'.length) : L[i]'hi = L'[i']'hi' := by
  subst h; subst hii; rfl

/-- The one-component shadow data `⟨L.length, _, polyOfList L pos⟩` depends only on the list and the
position map: equal lists under equal maps give equal `PolyComp`s (the sizes are identified by
`subst`, so no recast is needed). -/
theorem polyComp_polyOfList_congr {α : Type*} {L L' : List α} (h : L = L')
    (hNZ : NeZero L.length) (hNZ' : NeZero L'.length) {pos pos' : α → Plane} (hpos : pos = pos')
    (h3 : 3 ≤ L.length) (h3' : 3 ≤ L'.length) :
    PolyComp.mk L.length h3 (@polyOfList α L hNZ pos) =
      PolyComp.mk L'.length h3' (@polyOfList α L' hNZ' pos') := by
  subst h; subst hpos; rfl

variable {n : ℕ} [NeZero n]

/-! ## 1. The carrier as a one-component shadow (tier 1) -/

/-- **§5 U4 target `geoCarrierPolyComp`.** The subpolygon `Q` of def:positive-lift ("whose curve is
Q", sm-3:332) as one component: the corner polygon `geoCornerPolygon hG.cg S q` of the carrier `q` of
the independent set `S`, with its `k = geoCornerCount` corners; `3 ≤ k` is U2b's
`three_le_geoCornerCount` (tier 1). Port of `carrierPolyComp`. -/
abbrev geoCarrierPolyComp (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S) : PolyComp :=
  ⟨geoCornerCount hG.cg S q, three_le_geoCornerCount hn hG hS q, geoCornerPolygon hG.cg S q⟩

/-- **§5 U4 target `geoCarrierShadow`.** The shadow of the positive lift of `Q`: the one-component
shadow of the corner polygon of the carrier `q`. Port of `carrierShadow`. -/
abbrev geoCarrierShadow (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S) : Shadow :=
  Shadow.single (geoCarrierPolyComp hn hG hS q)

theorem geoCarrierPolyComp_k (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S) :
    (geoCarrierPolyComp hn hG hS q).k = geoCornerCount hG.cg S q := rfl

theorem geoCarrierPolyComp_P (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S) :
    (geoCarrierPolyComp hn hG hS q).P = geoCornerPolygon hG.cg S q := rfl

theorem geoCarrierShadow_c (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S) :
    (geoCarrierShadow hn hG hS q).c = 1 := rfl

theorem geoCarrierShadow_comp (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S) (i : Fin 1) :
    (geoCarrierShadow hn hG hS q).comp i = geoCarrierPolyComp hn hG hS q := rfl

/-! ## 2. The block parametrisation of the corner polygon (tier 0)

`geoCornerPolygon_block` (U2b): from the corner `c_k = geoCornerMark k` the next corner `c_{k+1}` is
reached in `m ≥ 1` steps of `ρ_S`, the intermediate marks being unselected visits on the one original
edge of the outgoing slot of `c_k`, and the closed edge segment `[Q k, Q (k+1)]` is the union of the
`m` inherited straight subsegments. Points of the edge segments are read as half-open carrier
parameters (`GeoIsCarrierParameter`, `geoCarrierTrace`, U2c) to apply lem:carriers (iii) as ported in
SM/GeoCarrierSelfIntersections.lean. Port of LinkPositiveLift.lean:237-370. -/

/-- The interior marks of the block of the edge `k` of the corner polygon: the marks `ρ_S^i c_k`,
`1 ≤ i ≤ r`, are unselected visits on the original edge of the outgoing slot of `c_k`. Port of
`BlockInterior`. -/
def GeoBlockInterior {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) (r : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ r → ∃ v : Visit P,
    (geoSmoothingSuccessor hP S ^ i) (geoCornerMark hP S q k) = Sum.inr v ∧ v.1 ∉ S ∧
      v.2.val = (geoOutSlot hP S (geoCornerMark hP S q k)).1

theorem GeoBlockInterior.mono {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) {k : ZMod (geoCornerCount hP S q)} {r r' : ℕ}
    (h : r' ≤ r) (hb : GeoBlockInterior hP S q k r) : GeoBlockInterior hP S q k r' :=
  fun i h1 hi => hb i h1 (hi.trans h)

/-- The interior marks of a block are not true corners. -/
theorem GeoBlockInterior.not_trueCorner {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) {k : ZMod (geoCornerCount hP S q)} {r : ℕ}
    (hb : GeoBlockInterior hP S q k r) :
    ∀ i, 1 ≤ i → i ≤ r →
      ¬ IsTrueCorner S ((geoSmoothingSuccessor hP S ^ i) (geoCornerMark hP S q k)) := by
  intro i h1 hi hc
  obtain ⟨v, hv, hvS, -⟩ := hb i h1 hi
  rw [hv] at hc
  exact hvS ((isTrueCorner_visit S v).mp hc)

/-- A block mark that is a true corner is the starting corner (`r = 0`). -/
theorem GeoBlockInterior.eq_zero_of_trueCorner {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) {k : ZMod (geoCornerCount hP S q)} {r : ℕ}
    (hb : GeoBlockInterior hP S q k r)
    (hc : IsTrueCorner S ((geoSmoothingSuccessor hP S ^ r) (geoCornerMark hP S q k))) : r = 0 := by
  by_contra hr
  exact hb.not_trueCorner hP S q r (Nat.one_le_iff_ne_zero.mpr hr) le_rfl hc

/-- A block mark that is a crossing visit `w` with `1 ≤ r` lies on the block's original edge. -/
theorem GeoBlockInterior.visit_edge {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) {k : ZMod (geoCornerCount hP S q)} {r : ℕ}
    (hb : GeoBlockInterior hP S q k r) (hr : 1 ≤ r) {w : Visit P}
    (hw : (geoSmoothingSuccessor hP S ^ r) (geoCornerMark hP S q k) = Sum.inr w) :
    w.2.val = (geoOutSlot hP S (geoCornerMark hP S q k)).1 := by
  obtain ⟨v, hv, -, hve⟩ := hb r hr le_rfl
  rw [hw] at hv
  rw [Sum.inr.inj hv]
  exact hve

/-- A block parameter `(ρ_S^r c_k, u)`, `u ∈ [0,1)`, is a carrier parameter of `q`. Port of
`isCarrierParameter_block`. -/
theorem geoIsCarrierParameter_block {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) (r : ℕ)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    GeoIsCarrierParameter hP S q ((geoSmoothingSuccessor hP S ^ r) (geoCornerMark hP S q k), u) := by
  refine ⟨?_, hu0, hu1⟩
  show geoOwner hP S _ = q
  rw [geo_pow_owner]
  exact geoOwner_geoCornerMark hP S q k

/-- The corner `c_k` at parameter `0` is a carrier parameter tracing the corner point `Q k`. Port of
`corner_param`. -/
theorem geo_corner_param {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    GeoIsCarrierParameter hP S q (geoCornerMark hP S q k, 0) ∧
      geoCarrierTrace hP S (geoCornerMark hP S q k, 0) = geoCornerPolygon hP S q k :=
  ⟨⟨geoOwner_geoCornerMark hP S q k, le_rfl, zero_lt_one⟩,
    (geoSmoothingSegment_zero hP S _).trans (geoCornerPolygon_apply hP S q k).symm⟩

/-- **Unique previous corner.** Two true corners `c`, `c'` with `ρ_S^r c = ρ_S^{r'} c'` and no true
corner strictly after them within `r`, resp. `r'`, steps coincide, with `r = r'`. Port of
`prevCorner_unique_of_le`. -/
theorem geo_prevCorner_unique_of_le {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) {c c' : Mark P} (hc : IsTrueCorner S c) {r r' : ℕ} (hrr : r ≤ r')
    (hr' : ∀ i, 1 ≤ i → i ≤ r' → ¬ IsTrueCorner S ((geoSmoothingSuccessor hP S ^ i) c'))
    (h : (geoSmoothingSuccessor hP S ^ r) c = (geoSmoothingSuccessor hP S ^ r') c') :
    c = c' ∧ r = r' := by
  have hsplit : (geoSmoothingSuccessor hP S ^ r) ((geoSmoothingSuccessor hP S ^ (r' - r)) c') =
      (geoSmoothingSuccessor hP S ^ r') c' := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hrr]
  rw [← hsplit] at h
  have hc' : c = (geoSmoothingSuccessor hP S ^ (r' - r)) c' :=
    (geoSmoothingSuccessor hP S ^ r).injective h
  by_cases hz : r' - r = 0
  · have hrr' : r = r' := by omega
    subst hrr'
    rw [hz, pow_zero, Equiv.Perm.one_apply] at hc'
    exact ⟨hc', rfl⟩
  · exfalso
    apply hr' (r' - r) (by omega) (by omega)
    rw [← hc']
    exact hc

/-- Port of `prevCorner_unique`. -/
theorem geo_prevCorner_unique {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) {c c' : Mark P} (hc : IsTrueCorner S c) (hc' : IsTrueCorner S c')
    {r r' : ℕ}
    (hr : ∀ i, 1 ≤ i → i ≤ r → ¬ IsTrueCorner S ((geoSmoothingSuccessor hP S ^ i) c))
    (hr' : ∀ i, 1 ≤ i → i ≤ r' → ¬ IsTrueCorner S ((geoSmoothingSuccessor hP S ^ i) c'))
    (h : (geoSmoothingSuccessor hP S ^ r) c = (geoSmoothingSuccessor hP S ^ r') c') :
    c = c' ∧ r = r' := by
  rcases le_total r r' with hle | hle
  · exact geo_prevCorner_unique_of_le hP S hc hle hr' h
  · obtain ⟨h1, h2⟩ := geo_prevCorner_unique_of_le hP S hc' hle hr h.symm
    exact ⟨h1.symm, h2.symm⟩

/-- Two block marks (of the blocks of `a` and `b`) that coincide force `a = b` (and the same position
in the block). Port of `block_mark_eq`. -/
theorem geo_block_mark_eq {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) {a b : ZMod (geoCornerCount hP S q)} {r r' : ℕ}
    (hba : GeoBlockInterior hP S q a r) (hbb : GeoBlockInterior hP S q b r')
    (h : (geoSmoothingSuccessor hP S ^ r) (geoCornerMark hP S q a) =
      (geoSmoothingSuccessor hP S ^ r') (geoCornerMark hP S q b)) : a = b ∧ r = r' := by
  obtain ⟨hc, hr⟩ := geo_prevCorner_unique hP S (isTrueCorner_geoCornerMark hP S q a)
    (isTrueCorner_geoCornerMark hP S q b) (hba.not_trueCorner hP S q) (hbb.not_trueCorner hP S q) h
  exact ⟨geoCornerMark_injective hP S q hc, hr⟩

/-- **Block parametrisation of a closed edge segment.** A point of the `k`-th edge segment of the
corner polygon is traced at a half-open parameter `(ρ_S^r c_k, u)`, `u ∈ [0,1)`, by a mark of the
block of `k`, or it is the end corner `Q (k+1)`. Port of `edgeSegment_param`. -/
theorem geo_edgeSegment_param (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) {x : Plane}
    (hx : x ∈ edgeSegment (geoCornerPolygon hP S q) k) :
    (∃ (r : ℕ) (u : ℝ), 0 ≤ u ∧ u < 1 ∧ GeoBlockInterior hP S q k r ∧
      geoSmoothingSegment hP S ((geoSmoothingSuccessor hP S ^ r) (geoCornerMark hP S q k)) u = x) ∨
    x = geoCornerPolygon hP S q (k + 1) := by
  obtain ⟨m, hm, hchain, hmid, -, -, -, -, himage⟩ := geoCornerPolygon_block hn hP hS q k
  rw [geoCornerPolygon_edgeSegment, ← himage, Set.mem_iUnion₂] at hx
  obtain ⟨r, hr, u, ⟨hu0, hu1⟩, hux⟩ := hx
  have hint : ∀ r' < m, GeoBlockInterior hP S q k r' :=
    fun r' hr' i h1 hi => hmid i h1 (by omega)
  rcases lt_or_eq_of_le hu1 with hlt | heq
  · exact Or.inl ⟨r, u, hu0, hlt, hint r hr, hux⟩
  · subst heq
    rw [geoSmoothingSegment_glue, ← Equiv.Perm.mul_apply, ← pow_succ'] at hux
    rcases Nat.lt_or_ge (r + 1) m with hlt | hge
    · exact Or.inl ⟨r + 1, 0, le_rfl, zero_lt_one, hint (r + 1) hlt, hux⟩
    · right
      have heq : r + 1 = m := by omega
      rw [heq, hchain, geoSmoothingSegment_zero] at hux
      exact hux.symm

/-- **Block parametrisation of an open edge.** A point of the open `k`-th edge is traced at a
half-open block parameter of the block of `k`. Port of `edgeInterior_param`. -/
theorem geo_edgeInterior_param (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) {x : Plane}
    (hx : x ∈ edgeInterior (geoCornerPolygon hP S q) k) :
    ∃ (r : ℕ) (u : ℝ), 0 ≤ u ∧ u < 1 ∧ GeoBlockInterior hP S q k r ∧
      geoSmoothingSegment hP S ((geoSmoothingSuccessor hP S ^ r) (geoCornerMark hP S q k)) u = x := by
  rcases geo_edgeSegment_param hn hP hS q k (edgeInterior_subset_edgeSegment _ _ hx) with h | h
  · exact h
  · exfalso
    obtain ⟨t, -, ht1, hxt⟩ := hx
    have hne : edge (geoCornerPolygon hP S q) k ≠ 0 :=
      geoCornerPolygon_edge_ne_zero_of_independent hn hP hS q k
    have h1 : edgePoint (geoCornerPolygon hP S q) k t = edgePoint (geoCornerPolygon hP S q) k 1 := by
      rw [edgePoint_one, ← hxt, h]
    have := edgePoint_injective hne h1
    linarith

/-- Every mark owned by `q` is a block mark: `m = ρ_S^r c_k` for a corner `c_k` with the intermediate
marks interior to the block, and its plane point lies on the edge `k` of `Q`. Port of `mark_block`. -/
theorem geo_mark_block (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S) (m : Mark P)
    (hm : geoOwner hP S m = q) :
    ∃ (k : ZMod (geoCornerCount hP S q)) (r : ℕ),
      (geoSmoothingSuccessor hP S ^ r) (geoCornerMark hP S q k) = m ∧
      GeoBlockInterior hP S q k r ∧
      traversalEvaluation P (geoMarkPosition hP m) ∈ edgeSegment (geoCornerPolygon hP S q) k := by
  obtain ⟨a, r, ha, hac, hra, hmid⟩ := geo_previous_corner hP S q m hm
  obtain ⟨k, hk⟩ := geoCornerMark_exists_of_owner hP S q a ha hac
  subst hk
  obtain ⟨mk, hmk, hchain, hmidk, -, -, -, -, himage⟩ := geoCornerPolygon_block hn hP hS q k
  have hr : r < mk := by
    by_contra hle
    apply hmid mk hmk (not_lt.mp hle)
    rw [hchain]
    exact isTrueCorner_geoCornerMark hP S q (k + 1)
  refine ⟨k, r, hra, fun i h1 hi => hmidk i h1 (by omega), ?_⟩
  rw [geoCornerPolygon_edgeSegment, ← himage, Set.mem_iUnion₂]
  refine ⟨r, hr, 0, ⟨le_rfl, zero_le_one⟩, ?_⟩
  rw [hra, geoSmoothingSegment_zero]

/-! ## 3. Corner uniqueness and the meeting lemma for non-adjacent edges (tier 1) -/

/-- lem:carriers (iii) "none is a corner" in parameter form: two carrier parameters of `q` tracing
the plane point of a true corner coincide (otherwise that point would be a self-intersection, hence
the crossing point of an unselected crossing of `q`, which is the plane point of no true corner).
Port of `param_eq_of_corner`. -/
theorem geo_param_eq_of_corner (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)
    {p p' : Mark P × ℝ} (hp : GeoIsCarrierParameter hG.cg S q p)
    (hp' : GeoIsCarrierParameter hG.cg S q p') {m : Mark P} (hm : IsTrueCorner S m)
    (hx : geoCarrierTrace hG.cg S p = traversalEvaluation P (geoMarkPosition hG.cg m))
    (hx' : geoCarrierTrace hG.cg S p' = traversalEvaluation P (geoMarkPosition hG.cg m)) :
    p = p' := by
  by_contra hne
  have hsi : GeoIsSelfIntersection hG.cg S q (traversalEvaluation P (geoMarkPosition hG.cg m)) :=
    ⟨p, p', hp, hp', hne, hx, hx'⟩
  obtain ⟨c, hc, he⟩ := (geo_carrier_selfIntersection_iff hn hG hS q _).mp hsi
  exact (geo_carrier_selfIntersection_not_corner hG S q hc).2.2.2 m hm he

/-- The corner points of a carrier are pairwise distinct: the corner polygon is injective. Port of
`ccpCornerPolygon_injective`. -/
theorem geoCornerPolygon_injective (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S) :
    Function.Injective (geoCornerPolygon hG.cg S q) := by
  intro a b hab
  have h := geo_param_eq_of_corner hn hG hS q (geo_corner_param hG.cg S q a).1
    (geo_corner_param hG.cg S q b).1 (isTrueCorner_geoCornerMark hG.cg S q b)
    ((geo_corner_param hG.cg S q a).2.trans (hab.trans (geoCornerPolygon_apply hG.cg S q b)))
    ((geo_corner_param hG.cg S q b).2.trans (geoCornerPolygon_apply hG.cg S q b))
  exact geoCornerMark_injective hG.cg S q (congrArg Prod.fst h)

/-- A block parameter of the edge `b` tracing the corner point `Q a` is the corner parameter
`(c_a, 0)`; in particular `c_a = c_b`, i.e. `a = b`. Port of `block_param_corner`. -/
theorem geo_block_param_corner (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)
    {a b : ZMod (geoCornerCount hG.cg S q)} {r : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hb : GeoBlockInterior hG.cg S q b r)
    (h : geoSmoothingSegment hG.cg S ((geoSmoothingSuccessor hG.cg S ^ r) (geoCornerMark hG.cg S q b))
      u = geoCornerPolygon hG.cg S q a) : a = b := by
  have hp := geoIsCarrierParameter_block hG.cg S q b r hu0 hu1
  have heq := geo_param_eq_of_corner hn hG hS q hp (geo_corner_param hG.cg S q a).1
    (isTrueCorner_geoCornerMark hG.cg S q a) (h.trans (geoCornerPolygon_apply hG.cg S q a))
    ((geo_corner_param hG.cg S q a).2.trans (geoCornerPolygon_apply hG.cg S q a))
  have hmk : (geoSmoothingSuccessor hG.cg S ^ r) (geoCornerMark hG.cg S q b) =
      geoCornerMark hG.cg S q a :=
    congrArg Prod.fst heq
  have hr : r = 0 := hb.eq_zero_of_trueCorner hG.cg S q
    (by rw [hmk]; exact isTrueCorner_geoCornerMark hG.cg S q a)
  rw [hr, pow_zero, Equiv.Perm.one_apply] at hmk
  exact (geoCornerMark_injective hG.cg S q hmk).symm

/-- **Meeting of two non-adjacent edges of the corner polygon** (lem:carriers (iii), sm-3:84-86). A
common point `x` of the closed edge segments `a`, `b` of `Q`, `a`, `b` not adjacent, is the crossing
point of an unselected crossing `c` of `q` ("exactly the unselected crossings both of whose visits
are assigned to it"), whose two visits `w`, `visitTwin w` lie on the original edges carrying the two
edges of `Q`. Port of `nonadjacent_meet`. -/
theorem geo_nonadjacent_meet (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)
    {a b : ZMod (geoCornerCount hG.cg S q)} (hab : ¬ adjacent a b) {x : Plane}
    (hxa : x ∈ edgeSegment (geoCornerPolygon hG.cg S q) a)
    (hxb : x ∈ edgeSegment (geoCornerPolygon hG.cg S q) b) :
    ∃ (c : Crossing P) (w : Visit P), c ∈ geoCarrierCrossings hG.cg S q ∧
      x = crossingPoint c ∧ w.1 = c ∧
      w.2.val = (geoOutSlot hG.cg S (geoCornerMark hG.cg S q a)).1 ∧
      (visitTwin w).2.val = (geoOutSlot hG.cg S (geoCornerMark hG.cg S q b)).1 := by
  rcases geo_edgeSegment_param hn hG.cg hS q a hxa with ⟨r, u, hu0, hu1, hba, hux⟩ | hxa'
  · rcases geo_edgeSegment_param hn hG.cg hS q b hxb with ⟨r', v, hv0, hv1, hbb, hvx⟩ | hxb'
    · -- both points are half-open block parameters
      have hpa := geoIsCarrierParameter_block hG.cg S q a r hu0 hu1
      have hpb := geoIsCarrierParameter_block hG.cg S q b r' hv0 hv1
      have htr : geoCarrierTrace hG.cg S
            ((geoSmoothingSuccessor hG.cg S ^ r) (geoCornerMark hG.cg S q a), u) =
          geoCarrierTrace hG.cg S
            ((geoSmoothingSuccessor hG.cg S ^ r') (geoCornerMark hG.cg S q b), v) := by
        show geoSmoothingSegment hG.cg S _ u = geoSmoothingSegment hG.cg S _ v
        rw [hux, hvx]
      by_cases hpp : ((geoSmoothingSuccessor hG.cg S ^ r) (geoCornerMark hG.cg S q a), u) =
          ((geoSmoothingSuccessor hG.cg S ^ r') (geoCornerMark hG.cg S q b), v)
      · exfalso
        exact hab (adjacent_of_eq (geo_block_mark_eq hG.cg S q hba hbb (congrArg Prod.fst hpp)).1)
      · have hmk := geoCsi_mark_ne_of_param_ne hn hG.cg S hpp htr
        obtain ⟨-, -, c, hxc, ⟨w, hw, hwa₀⟩, ⟨w', hw', hwb₀⟩⟩ :=
          geoCsi_trace_meet hn hG S hmk hu0 hu1 hv0 hv1 (hux.trans hvx.symm)
        have hwa : (geoSmoothingSuccessor hG.cg S ^ r) (geoCornerMark hG.cg S q a) = Sum.inr w :=
          hwa₀
        have hwb : (geoSmoothingSuccessor hG.cg S ^ r') (geoCornerMark hG.cg S q b) = Sum.inr w' :=
          hwb₀
        have hww' : w' ≠ w := fun h => hmk (by
          show (geoSmoothingSuccessor hG.cg S ^ r) (geoCornerMark hG.cg S q a) =
            (geoSmoothingSuccessor hG.cg S ^ r') (geoCornerMark hG.cg S q b)
          rw [hwa, hwb, h])
        have htw : w' = visitTwin w := visitTwin_unique w w' (hw'.trans hw.symm) hww'
        have hoa : geoOwner hG.cg S (Sum.inr w) = q := by rw [← hwa]; exact hpa.1
        have hob : geoOwner hG.cg S (Sum.inr (visitTwin w)) = q := by
          rw [← htw, ← hwb]; exact hpb.1
        have hcS : c ∉ S := by
          intro hcS
          apply geo_selected_visits_separated hG.cg hS w (hw ▸ hcS)
          rw [hoa, hob]
        have hr : 1 ≤ r := by
          by_contra h
          have hr0 : r = 0 := by omega
          rw [hr0, pow_zero, Equiv.Perm.one_apply] at hwa
          have hcorner := isTrueCorner_geoCornerMark hG.cg S q a
          rw [hwa] at hcorner
          exact hcS (hw ▸ (isTrueCorner_visit S w).mp hcorner)
        have hr' : 1 ≤ r' := by
          by_contra h
          have hr0 : r' = 0 := by omega
          rw [hr0, pow_zero, Equiv.Perm.one_apply] at hwb
          have hcorner := isTrueCorner_geoCornerMark hG.cg S q b
          rw [hwb] at hcorner
          exact hcS (hw' ▸ (isTrueCorner_visit S w').mp hcorner)
        have hcmem : c ∈ geoCarrierCrossings hG.cg S q := by
          rw [mem_geoCarrierCrossings]
          refine ⟨hcS, fun v hv => ?_⟩
          rcases visit_eq_or_twin w v (hv.trans hw.symm) with rfl | rfl
          · exact hoa
          · exact hob
        refine ⟨c, w, hcmem, hux.symm.trans hxc, hw, hba.visit_edge hG.cg S q hr hwa, ?_⟩
        rw [← htw]
        exact hbb.visit_edge hG.cg S q hr' hwb
    · -- `x = Q (b+1)` is a corner point traced by a block parameter of `a`
      exfalso
      rw [hxb'] at hux
      exact hab (adjacent_of_eq_add_one (geo_block_param_corner hn hG hS q hu0 hu1 hba hux).symm)
  · rcases geo_edgeSegment_param hn hG.cg hS q b hxb with ⟨r', v, hv0, hv1, hbb, hvx⟩ | hxb'
    · exfalso
      rw [hxa'] at hvx
      exact hab (adjacent_of_add_one_eq (geo_block_param_corner hn hG hS q hv0 hv1 hbb hvx))
    · exfalso
      have h := geoCornerPolygon_injective hn hG hS q (hxa'.symm.trans hxb')
      exact hab (adjacent_of_eq (add_right_cancel h))

/-- The common point of two non-adjacent edges of `Q` is the crossing point of a crossing of `q`
(lem:carriers (iii), first sentence, on the corner polygon). Port of `nonadjacent_meet_crossing`. -/
theorem geo_nonadjacent_meet_crossing (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)
    {a b : ZMod (geoCornerCount hG.cg S q)} (hab : ¬ adjacent a b) {x : Plane}
    (hxa : x ∈ edgeSegment (geoCornerPolygon hG.cg S q) a)
    (hxb : x ∈ edgeSegment (geoCornerPolygon hG.cg S q) b) :
    ∃ c ∈ geoCarrierCrossings hG.cg S q, x = crossingPoint c := by
  obtain ⟨c, -, hc, hxc, -⟩ := geo_nonadjacent_meet hn hG hS q hab hxa hxb
  exact ⟨c, hc, hxc⟩

/-! ## 4. The four label-level genericity facts and the generic carrier shadow (tier 1) -/

/-- **§5 U4 target `geoCornerPolygon_tail_off`** (tier 1). No corner of `Q` lies on a non-incident
closed edge of `Q` (lem:carriers (iii): "none is a corner", with the distinctness of the corner
points). Port of `ccpCornerPolygon_tail_off`. -/
theorem geoCornerPolygon_tail_off (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)
    (a b : ZMod (geoCornerCount hG.cg S q)) (hab : ¬ incident a b) :
    geoCornerPolygon hG.cg S q a ∉ edgeSegment (geoCornerPolygon hG.cg S q) b := by
  intro hx
  rcases geo_edgeSegment_param hn hG.cg hS q b hx with ⟨r, u, hu0, hu1, hb, hux⟩ | h
  · exact hab (Or.inr (geo_block_param_corner hn hG hS q hu0 hu1 hb hux).symm)
  · have h' := geoCornerPolygon_injective hn hG hS q h
    exact hab (Or.inl (by rw [h']; ring))

/-- **§5 U4 target `geoCornerPolygon_transverse`** (tier 1). Meeting non-adjacent edges of `Q` are
transverse (lem:carriers (iii): "They are transverse"). Port of `ccpCornerPolygon_transverse`. -/
theorem geoCornerPolygon_transverse (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)
    (a b : ZMod (geoCornerCount hG.cg S q)) (hab : ¬ adjacent a b)
    (hmeet : (edgeSegment (geoCornerPolygon hG.cg S q) a ∩
      edgeSegment (geoCornerPolygon hG.cg S q) b).Nonempty) :
    det (edge (geoCornerPolygon hG.cg S q) a) (edge (geoCornerPolygon hG.cg S q) b) ≠ 0 := by
  obtain ⟨x, hxa, hxb⟩ := hmeet
  obtain ⟨c, w, -, -, hw, hwa, hwb⟩ := geo_nonadjacent_meet hn hG hS q hab hxa hxb
  obtain ⟨c₁, hc₁, he₁⟩ := geoCornerPolygon_edge_smul hn hG.cg hS q a
  obtain ⟨c₂, hc₂, he₂⟩ := geoCornerPolygon_edge_smul hn hG.cg hS q b
  rw [he₁, he₂, ccp_det_smul_smul, ← hwa, ← hwb]
  refine mul_ne_zero (mul_pos hc₁ hc₂).ne' ?_
  have hmem : w.2.val ∈ c.val := hw ▸ w.2.property
  have hmem' : (visitTwin w).2.val ∈ c.val := hw ▸ (visitTwin w).2.property
  exact geoCsi_crossing_edges_det_ne_zero hG.cg c hmem hmem' (visitTwin_edge_ne w).symm

/-- **§5 U4 target `geoCornerPolygon_no_triple`** (tier 1). `Q` has no triple point (lem:carriers
(iii): "no carrier has a triple point"). Port of `ccpCornerPolygon_no_triple`. -/
theorem geoCornerPolygon_no_triple (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S) :
    ¬ ∃ a b c : ZMod (geoCornerCount hG.cg S q), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      (edgeInterior (geoCornerPolygon hG.cg S q) a ∩ edgeInterior (geoCornerPolygon hG.cg S q) b ∩
        edgeInterior (geoCornerPolygon hG.cg S q) c).Nonempty := by
  rintro ⟨a, b, c, hab, hbc, hac, x, ⟨hxa, hxb⟩, hxc⟩
  obtain ⟨r, u, hu0, hu1, hba, hux⟩ := geo_edgeInterior_param hn hG.cg hS q a hxa
  obtain ⟨r', v, hv0, hv1, hbb, hvx⟩ := geo_edgeInterior_param hn hG.cg hS q b hxb
  obtain ⟨r'', t, ht0, ht1, hbc', htx⟩ := geo_edgeInterior_param hn hG.cg hS q c hxc
  apply geo_carrier_no_triple_point hn hG S q x
  refine ⟨_, _, _, geoIsCarrierParameter_block hG.cg S q a r hu0 hu1,
    geoIsCarrierParameter_block hG.cg S q b r' hv0 hv1,
    geoIsCarrierParameter_block hG.cg S q c r'' ht0 ht1, ?_, ?_, ?_, hux, hvx, htx⟩
  · intro h
    exact hab (geo_block_mark_eq hG.cg S q hba hbb (congrArg Prod.fst h)).1
  · intro h
    exact hac (geo_block_mark_eq hG.cg S q hba hbc' (congrArg Prod.fst h)).1
  · intro h
    exact hbc (geo_block_mark_eq hG.cg S q hbb hbc' (congrArg Prod.fst h)).1

/-- **§5 U4 target `geoCarrierShadow_generic`** ("CarrierGeneric" at tier 1). The shadow of a carrier
of an independent set on a `CarrierGeometry` polygon is generic in the sense of def:positive-lift
(sm-3:326-327: "finitely many transverse double points, no triple points"): regularity and `3 ≤ k`
are U2b's `geoCornerPolygon_regular` / `three_le_geoCornerCount`, and the immersion, transversality
and no-triple-point clauses are the three facts above. Port of `carrierShadow_generic`. -/
theorem geoCarrierShadow_generic (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S) :
    (geoCarrierShadow hn hG hS q).Generic :=
  Shadow.single_generic_of (geoCarrierPolyComp hn hG hS q) (geoCornerPolygon_regular hn hG hS q)
    (geoCornerPolygon_tail_off hn hG hS q) (geoCornerPolygon_transverse hn hG hS q)
    (geoCornerPolygon_no_triple hn hG hS q)

/-! ## 5. The positive lift (tier 1) -/

/-- **§5 U4 target `geoPositiveLift`.** def:positive-lift (sm-3:331-334) on the geometric carrier
layer: "The positive lift of a subpolygon Q is the oriented knot diagram whose curve is Q, whose
double points are the crossings of Q, and in which at every double point the over strand is chosen so
that the crossing is positive." The curve is the one-component shadow `geoCarrierShadow` of the
corner polygon of the carrier `q`; its double points are the crossings of that shadow (identified with
`geoCarrierCrossings hG.cg S q` in `geoCarrierCrossingEquiv`); the over strand at each crossing is the
strand `s` with `det(dir s, dir (other s)) > 0` (`Shadow.positiveDiagram`). Port of `positiveLift`. -/
def geoPositiveLift (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S) : Diagram :=
  (geoCarrierShadow hn hG hS q).positiveDiagram (geoCarrierShadow_generic hn hG hS q)

section PositiveLift

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P) {S : Finset (Crossing P)}
  (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)

@[simp] theorem geoPositiveLift_Γ : (geoPositiveLift hn hG hS q).Γ = geoCarrierShadow hn hG hS q :=
  rfl

/-- "the oriented knot diagram": one component (§5 shape `geoPositiveLift_componentCount = 1`). -/
theorem geoPositiveLift_componentCount : (geoPositiveLift hn hG hS q).componentCount = 1 := rfl

/-- The component of the lift is the corner polygon of the carrier ("whose curve is Q"). -/
theorem geoPositiveLift_comp (i : Fin 1) :
    ((geoPositiveLift hn hG hS q).Γ.comp i).P = geoCornerPolygon hG.cg S q := rfl

/-- **§5 U4 target `geoPositiveLift_isPositive`.** def:positive-lift (sm-3:333-334): "at every double
point the over strand is chosen so that the crossing is positive". -/
theorem geoPositiveLift_isPositive (x : (geoPositiveLift hn hG hS q).Γ.Crossing) :
    (geoPositiveLift hn hG hS q).IsPositive x :=
  Shadow.positiveDiagram_isPositive _ _ x

theorem geoPositiveLift_sign (x : (geoPositiveLift hn hG hS q).Γ.Crossing) :
    (geoPositiveLift hn hG hS q).sign x = 1 :=
  Shadow.positiveDiagram_sign _ _ x

/-- The writhe of the positive lift is its number of crossings (all signs are `+1`). -/
theorem geoPositiveLift_writhe_eq_card_crossing :
    (geoPositiveLift hn hG hS q).writhe = Fintype.card (geoCarrierShadow hn hG hS q).Crossing :=
  Shadow.positiveDiagram_writhe _ _

/-- **§5 U4 target `eq_geoPositiveLift_of_isPositive`.** The positive lift is the unique diagram on
the carrier shadow all of whose crossings are positive. -/
theorem eq_geoPositiveLift_of_isPositive (D : Diagram) (hD : D.Γ = geoCarrierShadow hn hG hS q)
    (hpos : ∀ x, D.IsPositive x) : D = geoPositiveLift hn hG hS q :=
  Shadow.eq_positiveDiagram_of_isPositive _ _ D hD hpos

/-! ### The double points of the lift are the crossings of `Q` -/

/-- Every crossing of the carrier shadow sits at the crossing point of a crossing of `q`
(def:positive-lift, sm-3:332-333: "whose double points are the crossings of Q"). Port of
`exists_carrierCrossing`. -/
theorem geo_exists_carrierCrossing (x : (geoCarrierShadow hn hG hS q).Crossing) :
    ∃ c : Crossing P, c ∈ geoCarrierCrossings hG.cg S q ∧
      (geoCarrierShadow hn hG hS q).crossingPoint x = crossingPoint c := by
  obtain ⟨s, t, hx, hna, -⟩ := x.2
  have hs : s ∈ x.val := by rw [hx]; simp
  have ht : t ∈ x.val := by rw [hx]; simp
  have hna' : ¬ adjacent (Shadow.singleStrandEquiv _ s) (Shadow.singleStrandEquiv _ t) :=
    fun h => hna ((Shadow.single_adjacent_iff _ s t).mpr h)
  have hps : (geoCarrierShadow hn hG hS q).crossingPoint x ∈
      edgeSegment (geoCornerPolygon hG.cg S q) (Shadow.singleStrandEquiv _ s) :=
    (geoCarrierShadow hn hG hS q).crossingPoint_mem x hs
  have hpt : (geoCarrierShadow hn hG hS q).crossingPoint x ∈
      edgeSegment (geoCornerPolygon hG.cg S q) (Shadow.singleStrandEquiv _ t) :=
    (geoCarrierShadow hn hG hS q).crossingPoint_mem x ht
  exact geo_nonadjacent_meet_crossing hn hG hS q hna' hps hpt

/-- The crossing of `q` at a crossing of the carrier shadow. Port of `toCarrierCrossing`. -/
def geoToCarrierCrossing (x : (geoCarrierShadow hn hG hS q).Crossing) :
    {c : Crossing P // c ∈ geoCarrierCrossings hG.cg S q} :=
  ⟨Classical.choose (geo_exists_carrierCrossing hn hG hS q x),
    (Classical.choose_spec (geo_exists_carrierCrossing hn hG hS q x)).1⟩

theorem crossingPoint_geoToCarrierCrossing (x : (geoCarrierShadow hn hG hS q).Crossing) :
    crossingPoint (geoToCarrierCrossing hn hG hS q x).val =
      (geoCarrierShadow hn hG hS q).crossingPoint x :=
  (Classical.choose_spec (geo_exists_carrierCrossing hn hG hS q x)).2.symm

theorem geoToCarrierCrossing_injective : Function.Injective (geoToCarrierCrossing hn hG hS q) := by
  intro x y h
  apply (geoCarrierShadow_generic hn hG hS q).crossingPoint_injective
  rw [← crossingPoint_geoToCarrierCrossing hn hG hS q x,
    ← crossingPoint_geoToCarrierCrossing hn hG hS q y, h]

include hn hS in
/-- Consecutive edges of `Q` meet only at their common corner. Tier 1 (ruling R4): the source
(`Link.consecutive_meet`) uses the nonzero turn `ccpCornerPolygon_det_ne_zero` (tier 2); here the
corner polygon has no corner on a non-incident closed edge (`geoCornerPolygon_tail_off`) and at least
three corners (`three_le_geoCornerCount`), so U0's fold-back exclusion
`meet_next_eq_corner_of_vertex_off` applies to `Q` itself. -/
theorem geo_consecutive_meet (k : ZMod (geoCornerCount hG.cg S q)) {x : Plane}
    (hx : x ∈ edgeSegment (geoCornerPolygon hG.cg S q) k)
    (hx' : x ∈ edgeSegment (geoCornerPolygon hG.cg S q) (k + 1)) :
    x = geoCornerPolygon hG.cg S q (k + 1) :=
  meet_next_eq_corner_of_vertex_off (three_le_geoCornerCount hn hG hS q)
    (geoCornerPolygon_tail_off hn hG hS q) k hx hx'

include hn hS in
/-- The two visits of a crossing of `q` lie on two non-adjacent edges of `Q`, and its crossing point
lies on both. Port of `carrierCrossing_edges`. -/
theorem geo_carrierCrossing_edges {c : Crossing P} (hc : c ∈ geoCarrierCrossings hG.cg S q) :
    ∃ j j' : ZMod (geoCornerCount hG.cg S q), ¬ adjacent j j' ∧
      crossingPoint c ∈ edgeSegment (geoCornerPolygon hG.cg S q) j ∧
      crossingPoint c ∈ edgeSegment (geoCornerPolygon hG.cg S q) j' := by
  obtain ⟨hcS, hown⟩ := (mem_geoCarrierCrossings hG.cg S q c).mp hc
  obtain ⟨i, -, -⟩ := crossing_visits_exist c
  let w : Visit P := ⟨c, i⟩
  have hw : w.1 = c := rfl
  have hw' : (visitTwin w).1 = c := rfl
  obtain ⟨j, r, hrj, hbj, hmemj⟩ := geo_mark_block hn hG.cg hS q (Sum.inr w) (hown w hw)
  obtain ⟨j', r', hrj', hbj', hmemj'⟩ :=
    geo_mark_block hn hG.cg hS q (Sum.inr (visitTwin w)) (hown _ hw')
  rw [geoMarkPosition_evaluation_visit] at hmemj hmemj'
  have hr : 1 ≤ r := by
    by_contra h
    have hr0 : r = 0 := by omega
    rw [hr0, pow_zero, Equiv.Perm.one_apply] at hrj
    have hcorner := isTrueCorner_geoCornerMark hG.cg S q j
    rw [hrj] at hcorner
    exact hcS ((isTrueCorner_visit S w).mp hcorner)
  have hr' : 1 ≤ r' := by
    by_contra h
    have hr0 : r' = 0 := by omega
    rw [hr0, pow_zero, Equiv.Perm.one_apply] at hrj'
    have hcorner := isTrueCorner_geoCornerMark hG.cg S q j'
    rw [hrj'] at hcorner
    exact hcS ((isTrueCorner_visit S (visitTwin w)).mp hcorner)
  have hwe := hbj.visit_edge hG.cg S q hr hrj
  have hwe' := hbj'.visit_edge hG.cg S q hr' hrj'
  have hnc : ∀ m : Mark P, IsTrueCorner S m →
      traversalEvaluation P (geoMarkPosition hG.cg m) ≠ crossingPoint c :=
    (geo_carrier_selfIntersection_not_corner hG S q hc).2.2.2
  refine ⟨j, j', ?_, hmemj, hmemj'⟩
  intro hadj
  rcases hadj with h | h | h
  · -- `j' - j = -1`: `j = j' + 1`
    have hj : j = j' + 1 := by linear_combination -h
    rw [hj] at hmemj
    exact hnc _ (isTrueCorner_geoCornerMark hG.cg S q (j' + 1))
      (geo_consecutive_meet hn hG hS q j' hmemj' hmemj).symm
  · -- `j' = j`: both visits on one original edge
    have hj : j' = j := by linear_combination h
    rw [hj] at hwe'
    exact visitTwin_edge_ne w (hwe'.trans hwe.symm)
  · -- `j' - j = 1`: `j' = j + 1`
    have hj : j' = j + 1 := by linear_combination h
    rw [hj] at hmemj'
    exact hnc _ (isTrueCorner_geoCornerMark hG.cg S q (j + 1))
      (geo_consecutive_meet hn hG hS q j hmemj hmemj').symm

theorem geoToCarrierCrossing_surjective : Function.Surjective (geoToCarrierCrossing hn hG hS q) := by
  rintro ⟨c, hc⟩
  obtain ⟨j, j', hna, hmemj, hmemj'⟩ := geo_carrierCrossing_edges hn hG hS q hc
  have hcr : (geoCarrierShadow hn hG hS q).IsCrossing
      {(⟨0, j⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, j'⟩} :=
    (geoCarrierShadow hn hG hS q).isCrossing_pair
      (fun h => hna ((Shadow.single_adjacent_iff _ _ _).mp h))
      ⟨crossingPoint c, hmemj, hmemj'⟩
  obtain ⟨y, hy⟩ : ∃ y : (geoCarrierShadow hn hG hS q).Crossing,
      y.val = {(⟨0, j⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, j'⟩} := ⟨⟨_, hcr⟩, rfl⟩
  refine ⟨y, Subtype.ext ?_⟩
  apply crossingPoint_injective_of_geometry hG.cg
  refine (crossingPoint_geoToCarrierCrossing hn hG hS q y).trans ?_
  symm
  apply (geoCarrierShadow_generic hn hG hS q).common_point_unique
  intro s hs
  rw [hy] at hs
  have hs' : s = ⟨0, j⟩ ∨ s = ⟨0, j'⟩ := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hs
  rcases hs' with rfl | rfl
  · exact hmemj
  · exact hmemj'

/-- **§5 U4 target `geoCarrierCrossingEquiv`.** def:positive-lift (sm-3:332-333), "whose double points
are the crossings of Q": the crossings of the positive lift correspond bijectively to the crossings
`geoCarrierCrossings hG.cg S q` of the carrier (def:smoothing; lem:carriers (iii)), each crossing of
the lift sitting at the crossing point of its image. Port of `carrierCrossingEquiv`. -/
def geoCarrierCrossingEquiv :
    (geoCarrierShadow hn hG hS q).Crossing ≃ {c : Crossing P // c ∈ geoCarrierCrossings hG.cg S q} :=
  Equiv.ofBijective (geoToCarrierCrossing hn hG hS q)
    ⟨geoToCarrierCrossing_injective hn hG hS q, geoToCarrierCrossing_surjective hn hG hS q⟩

theorem geoCarrierCrossingEquiv_apply (x : (geoCarrierShadow hn hG hS q).Crossing) :
    geoCarrierCrossingEquiv hn hG hS q x = geoToCarrierCrossing hn hG hS q x := rfl

/-- Sanity: the equivalence preserves the crossing point. -/
theorem crossingPoint_geoCarrierCrossingEquiv (x : (geoCarrierShadow hn hG hS q).Crossing) :
    crossingPoint (geoCarrierCrossingEquiv hn hG hS q x).val =
      (geoCarrierShadow hn hG hS q).crossingPoint x :=
  crossingPoint_geoToCarrierCrossing hn hG hS q x

/-- The number of crossings of the carrier shadow is `m_Q`. -/
theorem card_geoCarrierShadow_crossing :
    Fintype.card (geoCarrierShadow hn hG hS q).Crossing = (geoCarrierCrossings hG.cg S q).card := by
  rw [Fintype.card_congr (geoCarrierCrossingEquiv hn hG hS q)]
  exact Fintype.card_coe _

/-- **§5 U4 target `geoPositiveLift_writhe`.** def:positive-lift (sm-3:334-335): "Its writhe (the sum
of crossing signs) is m_Q", `m_Q = (geoCarrierCrossings hG.cg S q).card`. -/
theorem geoPositiveLift_writhe :
    (geoPositiveLift hn hG hS q).writhe = (geoCarrierCrossings hG.cg S q).card := by
  rw [geoPositiveLift_writhe_eq_card_crossing, card_geoCarrierShadow_crossing]

/-- The same with U2a's `geoCarrierCrossingCount`. -/
theorem geoPositiveLift_writhe_eq_geoCarrierCrossingCount :
    (geoPositiveLift hn hG hS q).writhe = geoCarrierCrossingCount hG.cg S q :=
  geoPositiveLift_writhe hn hG hS q

/-- Sanity: on the carrier shadow the multi-component crossing point is the accepted one-polygon
`crossingPoint` of the corner polygon (through `Shadow.singleCrossingEquiv`). -/
theorem geoCarrierShadow_crossingPoint (x : (geoCarrierShadow hn hG hS q).Crossing) :
    (geoCarrierShadow hn hG hS q).crossingPoint x =
      crossingPoint (Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hS q) x) :=
  Shadow.single_crossingPoint _ (geoCarrierShadow_generic hn hG hS q) x

/-- Sanity: the lift of a carrier without crossings is a crossing-free circle. -/
theorem geoPositiveLift_isCrossingFreeCircle (h : geoCarrierCrossings hG.cg S q = ∅) :
    (geoPositiveLift hn hG hS q).IsCrossingFreeCircle := by
  refine ⟨rfl, ⟨fun x => ?_⟩⟩
  obtain ⟨d, hd⟩ := geoToCarrierCrossing hn hG hS q x
  rw [h] at hd
  exact Finset.notMem_empty _ hd

end PositiveLift

/-! ## 6. Agreement with the accepted `positiveLift` on SM-generic polygons

Write `hc := generic_crossingGeometry hn hP`, `e := geoComponentEquivGeneric hn hP S`. The geo objects
are parametrised by a `Prop`, so for ANY `hG : CarrierGeometry P` the terms `geoCornerPolygon hG.cg S q`
and `geoCornerPolygon hc S q` are definitionally equal (proof irrelevance); the lemmas are stated with
an arbitrary tier-1 witness `hG` (e.g. `CarrierGeometry.ofGeneric hn hP`, or U0's
`CarrierGeometry.ofDiagrammatic hD` for a CV consumer). The one non-`rfl` point is the corner count:
`geoCornerCount hc S q = ccpCornerCount hn hP S (e q)` only propositionally
(`geoComponentCornerList_eq_generic`); both polygons are `polyOfList` of their corner lists under
their position maps, so the `PolyComp`s are equal by `polyComp_polyOfList_congr` (no recast). -/

section GenericAgreement

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (S : Finset (Crossing P))

/-- The geo corner count of a carrier of a generic polygon is the accepted one. -/
theorem geoCornerCount_eq_ccpCornerCount (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoCornerCount (generic_crossingGeometry hn hP) S q =
      ccpCornerCount hn hP S (geoComponentEquivGeneric hn hP S q) := by
  unfold geoCornerCount ccpCornerCount
  rw [geoComponentCornerList_eq_generic]

/-- The geo corner polygon of a carrier of a generic polygon is the accepted one, corner by corner
(recast-free form: equal corner values at equal `ZMod` values). -/
theorem geoCornerPolygon_apply_eq_generic (q : GeoComponent (generic_crossingGeometry hn hP) S)
    (k : ZMod (geoCornerCount (generic_crossingGeometry hn hP) S q))
    (k' : ZMod (ccpCornerCount hn hP S (geoComponentEquivGeneric hn hP S q))) (hk : k.val = k'.val) :
    geoCornerPolygon (generic_crossingGeometry hn hP) S q k =
      ccpCornerPolygon hn hP S (geoComponentEquivGeneric hn hP S q) k' := by
  rw [geoCornerPolygon_apply, ccpCornerPolygon_apply, geoMarkPosition_eq_generic hn hP]
  congr 2
  exact getElem_congr_of_eq (geoComponentCornerList_eq_generic hn hP S q) hk _ _

/-- The geo crossings of a carrier of a generic polygon are the accepted `carrierCrossings`. -/
theorem geoCarrierCrossings_eq_generic (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoCarrierCrossings (generic_crossingGeometry hn hP) S q =
      carrierCrossings hn hP S (geoComponentEquivGeneric hn hP S q) := by
  ext x
  rw [mem_geoCarrierCrossings, mem_carrierCrossings]
  refine and_congr Iff.rfl (forall_congr' fun v => forall_congr' fun _ => ?_)
  rw [← geoComponentEquivGeneric_owner]
  exact (geoComponentEquivGeneric hn hP S).injective.eq_iff.symm

theorem geoCarrierCrossingCount_eq_generic (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoCarrierCrossingCount (generic_crossingGeometry hn hP) S q =
      carrierCrossingCount hn hP S (geoComponentEquivGeneric hn hP S q) := by
  rw [geoCarrierCrossingCount_eq_card, carrierCrossingCount_eq_card, geoCarrierCrossings_eq_generic]

/-- **The one-component shadow data agree.** For any tier-1 witness `hG` and independence proof
`hS'`, the geo `PolyComp` of the carrier `q` is the accepted `carrierPolyComp` of `e q` (equal corner
lists `geoComponentCornerList_eq_generic`, equal position maps `geoMarkPosition_eq_generic`). -/
theorem geoCarrierPolyComp_eq_generic (hG : CarrierGeometry P) (hS' : GeoIndependent hG.cg S)
    (hS : IsDecomposition hn hP S) (q : GeoComponent hG.cg S) :
    geoCarrierPolyComp hn hG hS' q =
      carrierPolyComp hn hP S (geoComponentEquivGeneric hn hP S q) hS := by
  have hL := geoComponentCornerList_eq_generic hn hP S q
  have hpos : (fun m : Mark P => traversalEvaluation P (geoMarkPosition hG.cg m)) =
      fun m : Mark P => traversalEvaluation P (markPosition hn hP.1 m) := by
    funext m
    rw [geoMarkPosition_eq_generic hn hP]
  exact polyComp_polyOfList_congr hL (geoCornerCount_neZero hG.cg S q)
    (ccpCornerCount_neZero hn hP S _) hpos (three_le_geoCornerCount hn hG hS' q)
    (ccpCornerCount_ge_three hn hP hS _)

/-- The carrier shadows agree. -/
theorem geoCarrierShadow_eq_generic (hG : CarrierGeometry P) (hS' : GeoIndependent hG.cg S)
    (hS : IsDecomposition hn hP S) (q : GeoComponent hG.cg S) :
    geoCarrierShadow hn hG hS' q = carrierShadow hn hP S (geoComponentEquivGeneric hn hP S q) hS :=
  congrArg Shadow.single (geoCarrierPolyComp_eq_generic hn hP S hG hS' hS q)

/-- **§5 U6 target `geoPositiveLift_eq_generic`, proved here.** On an SM-generic polygon the
geometric positive lift IS the accepted `positiveLift` (def:positive-lift): literal equality of
diagrams, for any tier-1 witness `hG` and any independence proof `hS'` (the shadows are equal by
`geoCarrierShadow_eq_generic`, and both diagrams are all-positive, `eq_positiveLift_of_isPositive`). -/
theorem geoPositiveLift_eq_generic (hG : CarrierGeometry P) (hS' : GeoIndependent hG.cg S)
    (hS : IsDecomposition hn hP S) (q : GeoComponent hG.cg S) :
    geoPositiveLift hn hG hS' q = positiveLift hn hP S (geoComponentEquivGeneric hn hP S q) hS :=
  eq_positiveLift_of_isPositive hn hP S _ hS _ (geoCarrierShadow_eq_generic hn hP S hG hS' hS q)
    (geoPositiveLift_isPositive hn hG hS' q)

/-- The specialisation to the canonical tier-1 witness `CarrierGeometry.ofGeneric hn hP` and the
independence proof transported from `hS` by the accepted `geoIndependent_iff_isDecomposition`. -/
theorem geoPositiveLift_ofGeneric_eq (hS : IsDecomposition hn hP S)
    (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoPositiveLift hn (CarrierGeometry.ofGeneric hn hP)
        ((geoIndependent_iff_isDecomposition hn hP S).mpr hS) q =
      positiveLift hn hP S (geoComponentEquivGeneric hn hP S q) hS :=
  geoPositiveLift_eq_generic hn hP S _ _ hS q

/-- Consequently the crossing records agree. -/
theorem geoPositiveLift_record_eq_generic (hG : CarrierGeometry P) (hS' : GeoIndependent hG.cg S)
    (hS : IsDecomposition hn hP S) (q : GeoComponent hG.cg S) :
    (geoPositiveLift hn hG hS' q).record =
      (positiveLift hn hP S (geoComponentEquivGeneric hn hP S q) hS).record :=
  congrArg Diagram.record (geoPositiveLift_eq_generic hn hP S hG hS' hS q)

/-- … and are `RecordIso` (the form `SM.presentations` consumes: `P (geoPositiveLift …) =
P (positiveLift …)` follows downstream). -/
theorem geoPositiveLift_recordIso_generic (hG : CarrierGeometry P) (hS' : GeoIndependent hG.cg S)
    (hS : IsDecomposition hn hP S) (q : GeoComponent hG.cg S) :
    Nonempty (RecordIso (geoPositiveLift hn hG hS' q).record
      (positiveLift hn hP S (geoComponentEquivGeneric hn hP S q) hS).record) := by
  rw [geoPositiveLift_eq_generic hn hP S hG hS' hS q]
  exact ⟨RecordIso.refl _⟩

/-- The writhes agree (sanity: `m_Q` read on either side). -/
theorem geoPositiveLift_writhe_eq_generic (hG : CarrierGeometry P) (hS' : GeoIndependent hG.cg S)
    (hS : IsDecomposition hn hP S) (q : GeoComponent hG.cg S) :
    (geoPositiveLift hn hG hS' q).writhe =
      (positiveLift hn hP S (geoComponentEquivGeneric hn hP S q) hS).writhe :=
  congrArg Diagram.writhe (geoPositiveLift_eq_generic hn hP S hG hS' hS q)

end GenericAgreement

end
end SM.GeoCarrier
