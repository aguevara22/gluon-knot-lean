import SM.GeoCornerPolygon
import SM.GeoCarrierSelfIntersections
import SM.GeoCarrierNoncrossing
import SM.CX1

/-! Ported 2026-09-14 from work/drafts/cvdom/U3/GeoCarriersLemma.lean (CV-DOM unit U3: the geo mirrors of the accepted lem:carriers / def:smoothing / def:uniform / lem:C-X1 bundles — GeoCarriersLemmaData (tier 1) + GeoCornerTurnsData (tier 2), GeoSmoothingData, geoCarrierUniform / geoUniformSupport / geoCarrierRotation, geoCarrierWeight / geoWind and the agreement lemmas with the accepted lane; REPORT.md in the same directory). Library module, no row. Only this header added. -/

/-! # SM/GeoCarriersLemma.lean — lem:carriers, def:smoothing, def:uniform and def:wind's weights on
the geometric carrier layer (CV-DOM unit U3)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor, for the CV-DOM decision
(work/drafts/cvdom/DECISION_FINAL.md §0 option (C), §3 rulings R1–R5, §5 unit U3). Draft home
work/drafts/cvdom/U3/GeoCarriersLemma.lean; intended home work/lean/SM/GeoCarriersLemma.lean
(library module, namespace `SM.GeoCarrier`, `open Carrier`, CV-free, picked up by the lakefile glob
`SM.+`). Nothing under work/lean is modified; no accepted or ported name is re-declared.

## What this module is

The row-level mirrors of the accepted Carrier lane on the accepted geometric carrier layer
`SM.GeoCarrier` (def:flat-carriers, SM/FlatCarriersDefs.lean), proved from the ported units
U0–U2c (SM/GeoCarrierGeometry, GeoCarrierCount, GeoCarrierOrder, GeoCarrierCrossings,
GeoCarrierNoncrossing, GeoCornerPolygon, GeoCarrierSelfIntersections):

* §1 `GeoCarriersLemmaData` — the accepted `CarriersLemmaData` (SM/CarriersLemma.lean:42–122, lem:carriers
  (i)–(iv)) field by field on the geo objects, at tier 1 (`hG : CarrierGeometry P`, ruling R1). The one
  clause of (ii) that needs tier 2, "all corner turns nonzero", is split off into `GeoCornerTurnsData`
  (`hW : WeakGeneric P`), as ruling R4 prescribes; `geo_carriers_lemma` proves the tier-1 bundle,
  `geo_corner_turns` the tier-2 clause, `geo_carriers_lemma_of_weak` both under `hW`.
* §2 `GeoSmoothingData` — the accepted `SmoothingData` (SM/SmoothingDefinition.lean:39–150, def:smoothing)
  field by field on the geo objects, at tier 0 (`hP : CrossingGeometry P`): `geo_smoothing_data`, and the
  `∀`-closed `GeoSmoothingDefinitionData` / `geo_smoothing_definition` mirroring lines 182–187.
* §3 def:uniform on the geo carriers (mirror of SM/UniformDefinition.lean): `geoCarrierUniform`,
  `geoCarrierMixed`, `geoUniformSupport` (the accepted `UniformDecomposition`, renamed because
  "decomposition" is the `SM.Generic`-bound notion, ruling R2), `geoCarrierRotation`,
  `geoCarrierLeftTurns`, `GeoUniformDefinitionData` / `geo_uniform_definition`; and, mirroring
  SM/CornerStateSum.lean:61–77, `geoCarrierRotationInt` with `geoCarrierRotation_exists_int`,
  `geoCarrierRotationInt_cast` (tier 1, from `geoCornerPolygon_regular` and lem:rot's
  `rotationNumber_integer`).
* §4 the corner turns read off the corner marks: `turn_geoCornerPolygon_eq_markTurn`,
  `geoCornerTurn_eq_markTurn` (tier 0; mirror of SM/CX1.lean `turn_ccpCornerPolygon_eq_markTurn`), and
  "uniform" read on the corner marks (`forall_turn_geoCornerPolygon_iff`, `geoCarrierUniform_iff_corners`).
* §5 def:wind's weights, mirroring SM/CX1.lean (`carrierWeight`, `wind`): `geoCarrierWeight` (the accepted
  `geoCarrierSelector`, by definition), `geoWind`, the three weight clauses, `geoCarrierWeight_eq_of_uniform`,
  `geoCarrierSelector_ne_zero_iff_uniform`, `geoWind_ne_zero_iff` (tier 0).
* §6 agreement with the accepted lane on SM-generic polygons (`hP : Generic P`, `hn : 3 ≤ n`), through the
  accepted §4b lemmas of SM/FlatCarriersDefs.lean:638–724 (`geoComponentEquivGeneric`,
  `geoComponentEquivGeneric_owner`, `geoComponentCornerList_eq_generic`) and the accepted turn lemmas
  `generic_geoCornerTurn_vertex/_visit` (SM/FlatCarriers.lean:3414–3425): independence, `N(S)`, `U(S)`,
  ownership, "uniform"/"mixed"/"uniform support", the weight and `wind`. The agreements that need the
  corner polygon itself recast along the equal corner counts (`geoCarrierRotation`, `geoCarrierLeftTurns`,
  `geoCarrierRotationInt`) are NOT here: they need `recastTuple` (SM/CChamber.lean, the prop:C-chamber row
  module) and `geoCornerPolygon_eq_generic` (SM/CS3.lean §B, the thm:C-S3 row module), which a library
  module must not import; unit U6 (SM/GeoCarrierAgreement.lean) owns them.

## Binders and tiers (ruling R1, R4, R5)

Tier 0 `hP : CrossingGeometry P`, tier 1 `hG : CarrierGeometry P` (used as `hG.cg`), tier 2
`hW : WeakGeneric P` (used as `weak_crossingGeometry hW`; proof irrelevance identifies it with
`hW.carrierGeometry.cg`, so `hS : GeoIndependent (weak_crossingGeometry hW) S` is accepted where
`GeoIndependent hW.carrierGeometry.cg S` is expected). Independence is the accepted `GeoIndependent hP S`
(ruling R2). `hn : 3 ≤ n` is carried exactly where the ported lemmas take it (the corner-polygon and
direction lemmas of U2a/U2b/U2c, `geoComponent_card`); the definitions of §3 and §5 do not take it.

## Conventions

`turn = sign det(incoming, outgoing)` (`turn_det`), `+1` = left, `−1` = right (def:chirotope); `markTurn`
(SM/CX1.lean) is the turn contributed by a true corner as a function of its mark (`turn P i` at the vertex
`i`, `crossingSign P v.2 (visitTwin v).2` at the selected visit `v`). `N(S) = geoSupportNeighbors`,
`U(S) = geoSupportUnselected` (U2a; the accepted `CV.N`/`CV.U` word for word, CV-free);
`m_Q = geoCarrierCrossingCount` (U2a). The ownership of the two visits of a selected crossing follows
conv:selected-visits (`selectedMarkPerm`), as everywhere on the geo layer.

Checked with `cd work/lean && lake env lean ../drafts/cvdom/U3/GeoCarriersLemma.lean`. -/

namespace SM.GeoCarrier

open Carrier

variable {n : ℕ} [NeZero n]

/-! ## 1. lem:carriers (i)–(iv) on the geometric carrier layer -/

section CarriersLemma

attribute [local instance] Classical.propDecidable

/-- The four printed clauses of lem:carriers at one independent set `S` of a `CarrierGeometry` polygon
(tier 1): the accepted `CarriersLemmaData` (SM/CarriersLemma.lean:42–122) field by field on the geo
objects, with the one tier-2 clause of (ii) ("all corner turns nonzero") split off into
`GeoCornerTurnsData` (ruling R4). -/
structure GeoCarriersLemmaData (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    (S : Finset (Crossing P)) (hS : GeoIndependent hG.cg S) : Prop where
  /-- (i) exactly `|S| + 1` carriers -/
  count : Fintype.card (GeoComponent hG.cg S) = S.card + 1
  /-- (i) each carrier traverses the visits assigned to it in the cyclic order inherited from the
  original traversal circle -/
  component_cycle : ∀ q : GeoComponent hG.cg S,
    geoComponentCycle hG.cg S q =
      (geoMarkCycle hG.cg).filter (fun m => decide (geoOwner hG.cg S m = q))
  inherited_order : GeoInheritsMarkOrder hG.cg S
  /-- (i) the two visits of a selected crossing belong to different carriers -/
  selected_visits_separated : ∀ v : Visit P, v.1 ∈ S →
    geoOwner hG.cg S (Sum.inr v) ≠ geoOwner hG.cg S (Sum.inr (visitTwin v))
  /-- (ii) every carrier (as its corner polygon) traces the carrier, has nonzero edges that are positive
  multiples of original edge directions, at least three corners, no antiparallel consecutive
  directions (it is regular); at an original vertex `i` the turn sign is `τ_i`; at a selected crossing
  of `E_i, E_j` the two smoothing corners have signs `sgn det(d_i, d_j)` and `sgn det(d_j, d_i)`, one
  left and one right. (The clause "all corner turns nonzero" is `GeoCornerTurnsData.turn_ne_zero`.) -/
  corner_polygons :
    (∀ q : GeoComponent hG.cg S,
    (⋃ a ∈ {a : Mark P | geoOwner hG.cg S a = q}, geoSmoothingSegment hG.cg S a '' Set.Icc 0 1) =
    ⋃ k : ZMod (geoCornerCount hG.cg S q), edgeSegment (geoCornerPolygon hG.cg S q) k) ∧
    (∀ (q : GeoComponent hG.cg S) (k : ZMod (geoCornerCount hG.cg S q)),
    edge (geoCornerPolygon hG.cg S q) k ≠ 0 ∧
    ∃ (c : ℝ) (e : ZMod n), 0 < c ∧ edge (geoCornerPolygon hG.cg S q) k = c • edge P e) ∧
    (∀ q : GeoComponent hG.cg S, 3 ≤ geoCornerCount hG.cg S q) ∧
    (∀ (q : GeoComponent hG.cg S) (k : ZMod (geoCornerCount hG.cg S q)),
    ¬ ∃ r : ℝ, r < 0 ∧
    edge (geoCornerPolygon hG.cg S q) k = r • edge (geoCornerPolygon hG.cg S q) (k - 1)) ∧
    (∀ q : GeoComponent hG.cg S, Regular (geoCornerPolygon hG.cg S q)) ∧
    (∀ (q : GeoComponent hG.cg S) (k : ZMod (geoCornerCount hG.cg S q)) (i : ZMod n),
    geoCornerMark hG.cg S q k = Sum.inl i → turn (geoCornerPolygon hG.cg S q) k = turn P i) ∧
    (∀ (v : Visit P), v.1 ∈ S →
    geoOwner hG.cg S (Sum.inr v) ≠ geoOwner hG.cg S (Sum.inr (visitTwin v)) ∧
    ∃ (k : ZMod (geoCornerCount hG.cg S (geoOwner hG.cg S (Sum.inr v))))
    (k' : ZMod (geoCornerCount hG.cg S (geoOwner hG.cg S (Sum.inr (visitTwin v))))),
    geoCornerMark hG.cg S _ k = Sum.inr v ∧
    geoCornerMark hG.cg S _ k' = Sum.inr (visitTwin v) ∧
    turn (geoCornerPolygon hG.cg S _) k = crossingSign P v.2.val (visitTwin v).2.val ∧
    turn (geoCornerPolygon hG.cg S _) k' = crossingSign P (visitTwin v).2.val v.2.val ∧
    turn (geoCornerPolygon hG.cg S _) k' = - turn (geoCornerPolygon hG.cg S _) k ∧
    ((turn (geoCornerPolygon hG.cg S _) k = 1 ∧ turn (geoCornerPolygon hG.cg S _) k' = -1) ∨
    (turn (geoCornerPolygon hG.cg S _) k = -1 ∧ turn (geoCornerPolygon hG.cg S _) k' = 1)))
  /-- (iii) a carrier's self-intersections are exactly the unselected crossings both of whose
  visits are assigned to it; they are transverse, none is a corner, no carrier has a triple point -/
  self_intersections : ∀ q : GeoComponent hG.cg S,
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
    (∀ x : Plane, ¬ GeoIsTriplePoint hG.cg S q x)
  /-- (iii) an unselected crossing interlacing some element of `S` has its visits on different
  carriers; one interlacing no element of `S` has both visits on one carrier -/
  neighbor_visits_separated : ∀ x ∈ geoSupportNeighbors hG.cg S, ∀ v : Visit P, v.1 = x →
    geoOwner hG.cg S (Sum.inr v) ≠ geoOwner hG.cg S (Sum.inr (visitTwin v))
  nonneighbor_visits_together : ∀ x ∈ geoSupportUnselected hG.cg S, ∀ v w : Visit P,
    v.1 = x → w.1 = x → geoOwner hG.cg S (Sum.inr v) = geoOwner hG.cg S (Sum.inr w)
  /-- (iv) the assignment of all crossing visits (selected visits included) is noncrossing -/
  noncrossing :
    ¬ ∃ u₁ u₂ u₃ u₄ : Visit P,
    (u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₁ ≠ u₄ ∧ u₂ ≠ u₃ ∧ u₂ ≠ u₄ ∧ u₃ ≠ u₄) ∧
    traversalBetween (geometricVisitPosition hG.cg u₁) (geometricVisitPosition hG.cg u₂)
    (geometricVisitPosition hG.cg u₃) ∧
    traversalBetween (geometricVisitPosition hG.cg u₃) (geometricVisitPosition hG.cg u₄)
    (geometricVisitPosition hG.cg u₁) ∧
    geoOwner hG.cg S (Sum.inr u₁) = geoOwner hG.cg S (Sum.inr u₃) ∧
    geoOwner hG.cg S (Sum.inr u₂) = geoOwner hG.cg S (Sum.inr u₄) ∧
    geoOwner hG.cg S (Sum.inr u₁) ≠ geoOwner hG.cg S (Sum.inr u₂)

/-- The tier-2 clause of lem:carriers (ii) (ruling R4): on a weakly generic polygon all corner turns
of every carrier are nonzero — at a vertex corner because `τ_i ≠ 0` (`WeakGeneric` clause 2), at a
smoothing corner because the crossing is transverse. Stated on the polygon index and on the accepted
`geoCornerTurn`. -/
structure GeoCornerTurnsData (hn : 3 ≤ n) {P : LabelledTuple n} (hW : WeakGeneric P)
    (S : Finset (Crossing P)) (hS : GeoIndependent (weak_crossingGeometry hW) S) : Prop where
  /-- (ii) all corner turns of every carrier are nonzero -/
  turn_ne_zero : ∀ (q : GeoComponent (weak_crossingGeometry hW) S)
    (k : ZMod (geoCornerCount (weak_crossingGeometry hW) S q)),
    turn (geoCornerPolygon (weak_crossingGeometry hW) S q) k ≠ 0
  /-- the same at every mark, read through the accepted `geoCornerTurn` -/
  cornerTurn_ne_zero : ∀ a : Mark P, geoCornerTurn (weak_crossingGeometry hW) S a ≠ 0

/-- **lem:carriers (i)–(iv) on the geometric carrier layer**, tier 1: for every `CarrierGeometry`
polygon with `n ≥ 3` and every independent set `S` of crossings. Proofs: U1a (count, order,
separation), U2b (corner polygons), U2c (self-intersections), U2a (neighbour clauses, noncrossing). -/
theorem geo_carriers_lemma (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) : GeoCarriersLemmaData hn hG S hS where
  count := geoComponent_card hn hG.cg hS
  component_cycle := fun q => geoComponentCycle_eq_filter hG.cg S q
  inherited_order := geoInheritsMarkOrder_of_independent hG.cg hS
  selected_visits_separated := fun v hv => geo_selected_visits_separated hG.cg hS v hv
  corner_polygons := by
    refine ⟨fun q => (geoCornerPolygon_trace hn hG.cg hS q).symm,
      fun q k => ⟨geoCornerPolygon_edge_ne_zero_of_independent hn hG.cg hS q k, ?_⟩,
      fun q => three_le_geoCornerCount hn hG hS q,
      fun q k => geoCornerPolygon_not_antiparallel hn hG hS q k,
      fun q => geoCornerPolygon_regular hn hG hS q,
      fun q k i h => geoCornerPolygon_turn_vertex hn hG.cg hS q k i h,
      fun v hv => geoCornerPolygon_turn_visit_twin hn hG.cg hS v hv⟩
    obtain ⟨c, hc, he⟩ := geoCornerPolygon_edge_smul hn hG.cg hS q k
    exact ⟨c, _, hc, he⟩
  self_intersections := fun q => geo_self_intersections hn hG hS q
  neighbor_visits_separated := geo_neighbor_visits_separated hn hG.cg hS
  nonneighbor_visits_together := geo_nonneighbor_visits_together hn hG.cg hS
  noncrossing := geo_noncrossing hn hG.cg hS

/-- The tier-2 clause of lem:carriers (ii): all corner turns nonzero (U2b). -/
theorem geo_corner_turns (hn : 3 ≤ n) {P : LabelledTuple n} (hW : WeakGeneric P)
    {S : Finset (Crossing P)} (hS : GeoIndependent (weak_crossingGeometry hW) S) :
    GeoCornerTurnsData hn hW S hS where
  turn_ne_zero := fun q k => geoCornerPolygon_turn_ne_zero hn hW hS q k
  cornerTurn_ne_zero := fun a => geoCornerTurn_ne_zero hn hW hS a

/-- lem:carriers (i)–(iv) with every clause of (ii), on a weakly generic polygon (tier 2; the two
`CrossingGeometry` proofs are identified by proof irrelevance). -/
theorem geo_carriers_lemma_of_weak (hn : 3 ≤ n) {P : LabelledTuple n} (hW : WeakGeneric P)
    {S : Finset (Crossing P)} (hS : GeoIndependent (weak_crossingGeometry hW) S) :
    GeoCarriersLemmaData hn hW.carrierGeometry S hS ∧ GeoCornerTurnsData hn hW S hS :=
  ⟨geo_carriers_lemma hn hW.carrierGeometry hS, geo_corner_turns hn hW hS⟩

end CarriersLemma

/-! ## 2. def:smoothing on the geometric carrier layer -/

section Smoothing

attribute [local instance] Classical.propDecidable

/-- The printed description of the smoothing at one set `S` of crossings of a `CrossingGeometry`
polygon (tier 0): the accepted `SmoothingData` (SM/SmoothingDefinition.lean:39–150) field by field on
the geo objects. -/
structure GeoSmoothingData {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) : Prop where
  /-- the oriented reconnection: `ρ_S = ρ ∘ (swap of the two visits of each selected crossing)` -/
  reconnection : ∀ a : Mark P,
    geoSmoothingSuccessor hP S a = geoMarkSuccessor hP (selectedMarkPerm S a)
  /-- the carriers are the cycles of `ρ_S` -/
  carriers : ∀ a b : Mark P,
    geoOwner hP S a = geoOwner hP S b ↔ (geoSmoothingSuccessor hP S).SameCycle a b
  /-- the traced closed polygonal curve of a carrier: the plane points of its marks -/
  traced_curve : ∀ q : GeoComponent hP S,
    geoComponentPlaneCycle hP S q =
      ((geoComponentMarkList hP S q).map
        (fun m => traversalEvaluation P (geoMarkPosition hP m)) : Cycle Plane)
  /-- its corners are the vertices of `P` it passes through and the selected visits it turns at -/
  corners : ∀ q : GeoComponent hP S,
    geoComponentCornerCycle hP S q =
      (geoComponentCycle hP S q).filter (fun a => decide (IsTrueCorner S a))
  corner_vertex : ∀ i : ZMod n, IsTrueCorner S (Sum.inl i)
  corner_visit : ∀ v : Visit P, IsTrueCorner S (Sum.inr v) ↔ v.1 ∈ S
  /-- at an original vertex `i` the carrier arrives along `ℓ_{i-1}` and leaves along `ℓ_i` -/
  vertex_corner : ∀ (q : GeoComponent hP S) (i : ZMod n), geoOwner hP S (Sum.inl i) = q →
    (geoOwner hP S ((geoSmoothingSuccessor hP S).symm (Sum.inl i)) = q ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        geoSmoothingSegment hP S ((geoSmoothingSuccessor hP S).symm (Sum.inl i)) u ∈
          edgeSegment P (i - 1)) ∧
      ∃ c : ℝ, 0 < c ∧
        P i - traversalEvaluation P
            (geoMarkPosition hP ((geoSmoothingSuccessor hP S).symm (Sum.inl i))) =
          c • edge P (i - 1)) ∧
    (geoSmoothingSuccessor hP S (Sum.inl i) = geoMarkSuccessor hP (Sum.inl i) ∧
      geoOwner hP S (geoSmoothingSuccessor hP S (Sum.inl i)) = q ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        geoSmoothingSegment hP S (Sum.inl i) u ∈ edgeSegment P i) ∧
      ∃ c : ℝ, 0 < c ∧
        traversalEvaluation P
            (geoMarkPosition hP (geoSmoothingSuccessor hP S (Sum.inl i))) - P i =
          c • edge P i)
  /-- at a smoothing corner between `E_i` and `E_j` (the crossing of the selected visit `v`, with
  `i = v.2`, `j = (visitTwin v).2`) the carrier arrives along `ℓ_i` and leaves along `ℓ_j` -/
  smoothing_corner : ∀ (q : GeoComponent hP S) (v : Visit P), v.1 ∈ S →
    geoOwner hP S (Sum.inr v) = q →
    (v.1.val = {v.2.val, (visitTwin v).2.val} ∧ v.2.val ≠ (visitTwin v).2.val) ∧
    (geoOwner hP S ((geoSmoothingSuccessor hP S).symm (Sum.inr v)) = q ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        geoSmoothingSegment hP S ((geoSmoothingSuccessor hP S).symm (Sum.inr v)) u ∈
          edgeSegment P v.2.val) ∧
      ∃ c : ℝ, 0 < c ∧
        traversalEvaluation P (geoMarkPosition hP (Sum.inr v)) -
          traversalEvaluation P
            (geoMarkPosition hP ((geoSmoothingSuccessor hP S).symm (Sum.inr v))) =
          c • edge P v.2.val) ∧
    (geoSmoothingSuccessor hP S (Sum.inr v) = geoMarkSuccessor hP (Sum.inr (visitTwin v)) ∧
      geoOwner hP S (geoSmoothingSuccessor hP S (Sum.inr v)) = q ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        geoSmoothingSegment hP S (Sum.inr v) u ∈ edgeSegment P (visitTwin v).2.val) ∧
      ∃ c : ℝ, 0 < c ∧
        traversalEvaluation P
            (geoMarkPosition hP (geoSmoothingSuccessor hP S (Sum.inr v))) -
          traversalEvaluation P (geoMarkPosition hP (Sum.inr v)) =
          c • edge P (visitTwin v).2.val)
  /-- the traced curve is the closed polygonal curve of the cycle: the marks of `q` in inherited
  order, consecutive marks being `ρ_S`-successors (cyclically) -/
  traced_marks : ∀ q : GeoComponent hP S,
    (geoComponentMarkList hP S q).Nodup ∧ 0 < (geoComponentMarkList hP S q).length ∧
    (geoComponentMarkList hP S q : Cycle (Mark P)) = geoComponentCycle hP S q ∧
    ∀ m : Mark P, m ∈ geoComponentMarkList hP S q ↔ geoOwner hP S m = q
  traced_successor : ∀ (q : GeoComponent hP S) (i : Fin (geoComponentMarkList hP S q).length),
    geoSmoothingSuccessor hP S ((geoComponentMarkList hP S q)[i.val]'i.isLt) =
      (geoComponentMarkList hP S q)[(i.val + 1) % (geoComponentMarkList hP S q).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt))
  /-- its sides are the straight segments from each mark to its `ρ_S`-successor: nonzero,
  continuous, and closing up around the cycle -/
  traced_sides : ∀ (q : GeoComponent hP S) (i : Fin (geoComponentMarkList hP S q).length),
    (∀ u : ℝ, geoComponentTraceEdge hP S q i u =
      geoSmoothingSegment hP S ((geoComponentMarkList hP S q)[i.val]'i.isLt) u) ∧
    0 < euclideanLength (geoComponentTraceEdge hP S q i 1 - geoComponentTraceEdge hP S q i 0) ∧
    geoComponentTraceEdge hP S q i 1 =
      geoComponentTraceEdge hP S q
        ⟨(i.val + 1) % (geoComponentMarkList hP S q).length,
          Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩ 0 ∧
    Continuous (geoComponentTraceEdge hP S q i)
  /-- the carrier passes straight through an unselected visit it owns: the incoming piece lies on
  the visited edge `E_{v.2}`, and both the incoming and the outgoing displacement are positive
  multiples of `ℓ_{v.2}` (so such a point is not a corner) -/
  unselected_visit_straight : ∀ v : Visit P, v.1 ∉ S →
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      geoSmoothingSegment hP S ((geoSmoothingSuccessor hP S).symm (Sum.inr v)) u ∈
        edgeSegment P v.2.val) ∧
    (∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hP (Sum.inr v)) -
        traversalEvaluation P
          (geoMarkPosition hP ((geoSmoothingSuccessor hP S).symm (Sum.inr v))) =
        c • edge P v.2.val) ∧
    (∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S (Sum.inr v))) -
        traversalEvaluation P (geoMarkPosition hP (Sum.inr v)) = c • edge P v.2.val)
  /-- at a smoothing corner the two edges `E_i, E_j` of the selected crossing are transverse -/
  smoothing_corner_transverse : ∀ v : Visit P, v.1 ∈ S →
    det (edge P v.2.val) (edge P (visitTwin v).2.val) ≠ 0
  /-- the crossings of `Q`: `x ∈ X(P) ∖ S` both of whose visits lie on `Q`; their number `m_Q` -/
  crossings_of : ∀ (q : GeoComponent hP S) (x : Crossing P),
    x ∈ geoCarrierCrossings hP S q ↔
      x ∉ S ∧ ∀ v : Visit P, v.1 = x → geoOwner hP S (Sum.inr v) = q
  crossing_count : ∀ q : GeoComponent hP S,
    geoCarrierCrossingCount hP S q = (geoCarrierCrossings hP S q).card
  /-- a crossing in `N(S)` has its two visits on different subpolygons and is a crossing of no
  subpolygon -/
  neighbor_visits : ∀ x ∈ geoSupportNeighbors hP S, ∀ v : Visit P, v.1 = x →
    geoOwner hP S (Sum.inr v) ≠ geoOwner hP S (Sum.inr (visitTwin v))
  neighbor_no_carrier : ∀ x ∈ geoSupportNeighbors hP S, ∀ q : GeoComponent hP S,
    x ∉ geoCarrierCrossings hP S q

/-- **def:smoothing on the geometric carrier layer**, tier 0: for every `CrossingGeometry` polygon with
`n ≥ 3` and every independent set `S` (mirror of `smoothing_data`). Proofs: the accepted geo layer,
U1b (the traced marks, sides and successors), U2a (corner directions, crossings, neighbours);
transversality at a smoothing corner is `CrossingGeometry` clause 2. -/
theorem geo_smoothing_data (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) : GeoSmoothingData hP S where
  reconnection := fun a => geoSmoothingSuccessor_apply hP S a
  carriers := fun a b => geoOwner_eq_iff hP S a b
  traced_curve := fun _ => rfl
  corners := fun _ => rfl
  corner_vertex := fun i => isTrueCorner_vertex S i
  corner_visit := fun v => isTrueCorner_visit S v
  vertex_corner := fun q i hq => geo_vertex_corner_directions hn hP S q i hq
  smoothing_corner := fun q v hv hq => geo_smoothing_corner_directions hn hP S q v hv hq
  traced_marks := fun q => geoComponentMarkList_data hP S q
  traced_successor := fun q i => geoTracedSuccessor_of_independent hn hP hS q i
  traced_sides := fun q i => geoComponentTraceEdge_data hn hP hS q i
  unselected_visit_straight := fun v hv =>
    ⟨fun u hu0 hu1 => geo_visit_incoming_mem_edgeSegment hn hP S v hu0 hu1,
      geo_visit_incoming_direction hn hP S v, geo_unselected_visit_outgoing_direction hn hP S v hv⟩
  smoothing_corner_transverse := by
    intro v _
    have hc : IsCrossing P {v.2.val, (visitTwin v).2.val} := by
      have h := v.1.property
      rwa [visit_crossing_val_eq_pair v] at h
    exact crossing_det_ne_zero_of_geometry hP hc
  crossings_of := fun q x => mem_geoCarrierCrossings hP S q x
  crossing_count := fun q => geoCarrierCrossingCount_eq_card hP S q
  neighbor_visits := fun x hx v hv => geo_neighbor_visit_owners_ne hP hS hx v hv
  neighbor_no_carrier := fun x hx q => geo_neighbor_not_mem_geoCarrierCrossings hP hS hx q

/-- def:smoothing for every `CrossingGeometry` polygon with `n ≥ 3` and every independent set `S`
(mirror of `SmoothingDefinitionData`). -/
def GeoSmoothingDefinitionData : Prop :=
  ∀ k : ℕ, ∀ _ : NeZero k, ∀ _ : 3 ≤ k, ∀ P : LabelledTuple k, ∀ hP : CrossingGeometry P,
    ∀ S : Finset (Crossing P), GeoIndependent hP S → GeoSmoothingData hP S

theorem geo_smoothing_definition : GeoSmoothingDefinitionData :=
  fun _ _ hk _ hP _ hS => geo_smoothing_data hk hP hS

end Smoothing

/-! ## 3. def:uniform on the geometric carrier layer (mirror of SM/UniformDefinition.lean) -/

section Uniform

variable {P : LabelledTuple n}

/-- A carrier `Q` is *uniform* if all its turns have one (nonzero) sign (port of `CarrierUniform`). -/
def geoCarrierUniform (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : Prop :=
  ∃ τ : SignType, τ ≠ 0 ∧ ∀ k, turn (geoCornerPolygon hP S q) k = τ

/-- A carrier is *mixed* if it is not uniform (port of `CarrierMixed`). -/
def geoCarrierMixed (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : Prop :=
  ¬ geoCarrierUniform hP S q

/-- A set `S` of crossings is *uniform* if all its carriers are (port of `UniformDecomposition`; the
name says "support" because "decomposition" is the `SM.Generic`-bound notion, ruling R2). -/
def geoUniformSupport (hP : CrossingGeometry P) (S : Finset (Crossing P)) : Prop :=
  ∀ q : GeoComponent hP S, geoCarrierUniform hP S q

/-- `r_Q = rot(Q)`, the rotation number of the carrier `Q` (port of `carrierRotation`). -/
noncomputable def geoCarrierRotation (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : ℝ :=
  rotationNumber (geoCornerPolygon hP S q)

/-- `ℓ_Q`, the number of left turns of the carrier `Q` (port of `carrierLeftTurns`). -/
noncomputable def geoCarrierLeftTurns (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : ℕ :=
  leftTurns (geoCornerPolygon hP S q)

/-- `r_Q` read as an integer: `round` of the real rotation (port of `carrierRotationInt`,
SM/CornerStateSum.lean:61). On independent sets of a `CarrierGeometry` polygon the rotation is an
integer (lem:rot), so this is that integer (`geoCarrierRotationInt_cast`). -/
noncomputable def geoCarrierRotationInt (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : ℤ :=
  round (geoCarrierRotation hP S q)

/-- lem:rot on a carrier of an independent set: `r_Q` is an integer (the corner polygon is regular by
lem:carriers (ii) at tier 1, `geoCornerPolygon_regular`). -/
theorem geoCarrierRotation_exists_int (hn : 3 ≤ n) (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S) :
    ∃ k : ℤ, geoCarrierRotation hG.cg S q = (k : ℝ) :=
  rotationNumber_integer (geoCornerPolygon_regular hn hG hS q)

/-- On independent sets the integer rotation casts back to the real rotation. -/
theorem geoCarrierRotationInt_cast (hn : 3 ≤ n) (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S) :
    ((geoCarrierRotationInt hG.cg S q : ℤ) : ℝ) = geoCarrierRotation hG.cg S q := by
  obtain ⟨k, hk⟩ := geoCarrierRotation_exists_int hn hG hS q
  rw [geoCarrierRotationInt, hk, round_intCast]

end Uniform

/-- def:uniform as printed on SM15, read on the carriers of the geometric carrier layer (mirror of the
accepted `UniformDefinitionData`; the clause `regular_carrier` is at tier 1, ruling R4). -/
structure GeoUniformDefinitionData : Prop where
  /-- `Q` is uniform iff all its turns have one sign `τ ∈ {-1, +1}`. -/
  uniform : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S),
    geoCarrierUniform hP S q ↔
      ∃ τ : SignType, τ ≠ 0 ∧ ∀ k, turn (geoCornerPolygon hP S q) k = τ
  /-- `Q` is mixed iff it is not uniform. -/
  mixed : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S),
    geoCarrierMixed hP S q ↔ ¬ geoCarrierUniform hP S q
  /-- `S` is uniform iff all its carriers are. -/
  uniform_support : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)),
    geoUniformSupport hP S ↔ ∀ q : GeoComponent hP S, geoCarrierUniform hP S q
  /-- lem:rot is applicable to every carrier of an independent set (lem:carriers (ii)): the corner
  polygon has at least three vertices and is regular. -/
  regular_carrier : ∀ (n : ℕ) [NeZero n] (_hn : 3 ≤ n) (P : LabelledTuple n)
    (hG : CarrierGeometry P) (S : Finset (Crossing P)), GeoIndependent hG.cg S →
    ∀ q : GeoComponent hG.cg S, 3 ≤ geoCornerCount hG.cg S q ∧ Regular (geoCornerPolygon hG.cg S q)
  /-- `r_Q = rot(Q) = (1/2π) Σ_k ϑ_k(Q)` over the corners of `Q`. -/
  rotation : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S),
    geoCarrierRotation hP S q =
      (∑ k, principalTurn (geoCornerPolygon hP S q) k) / (2 * Real.pi)
  /-- `m_Q` is the number of crossings of `Q` (def:smoothing). -/
  crossings : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S),
    geoCarrierCrossingCount hP S q = (geoCarrierCrossings hP S q).card
  /-- `ℓ_Q` is the number of left turns `#{k : τ_k(Q) = 1}` of `Q`. -/
  left_turns : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S),
    geoCarrierLeftTurns hP S q =
      (Finset.univ.filter fun k => turn (geoCornerPolygon hP S q) k = 1).card

theorem geo_uniform_definition : GeoUniformDefinitionData where
  uniform := fun _ _ _ _ _ _ => Iff.rfl
  mixed := fun _ _ _ _ _ _ => Iff.rfl
  uniform_support := fun _ _ _ _ _ => Iff.rfl
  regular_carrier := fun _ _ hn _ hG _ hS q =>
    ⟨three_le_geoCornerCount hn hG hS q, geoCornerPolygon_regular hn hG hS q⟩
  rotation := fun _ _ _ _ _ _ => rfl
  crossings := fun _ _ _ _ _ _ => rfl
  left_turns := fun _ _ _ _ _ _ => rfl

/-! ## 4. The corner turns read off the corner marks (tier 0; mirror of SM/CX1.lean §Helpers) -/

section MarkTurns

variable {P : LabelledTuple n}

/-- The turn of a carrier at its `k`-th corner is `markTurn` of that corner mark: `τ_i` at the vertex
`i`, `crossingSign P v.2 (visitTwin v).2` at the selected visit `v` (port of
`turn_ccpCornerPolygon_eq_markTurn`; U2b's `geoCornerPolygon_turn_vertex/_visit`). -/
theorem turn_geoCornerPolygon_eq_markTurn (hn : 3 ≤ n) (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    turn (geoCornerPolygon hP S q) k = markTurn P (geoCornerMark hP S q k) := by
  cases hm : geoCornerMark hP S q k with
  | inl i => rw [geoCornerPolygon_turn_vertex hn hP hS q k i hm, markTurn_inl]
  | inr v =>
    have hv : v.1 ∈ S := by
      have h := (geoCornerMark_mem hP S q k).2
      rw [hm] at h
      exact h
    rw [geoCornerPolygon_turn_visit hn hP hS q k v hv hm, markTurn_inr]

/-- The accepted `geoCornerTurn` at a true corner is `markTurn` of that mark. -/
theorem geoCornerTurn_eq_markTurn (hn : 3 ≤ n) (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) {a : Mark P} (ha : IsTrueCorner S a) :
    geoCornerTurn hP S a = markTurn P a := by
  cases a with
  | inl i => exact geoCornerTurn_vertex hn hP hS i
  | inr v => exact geoCornerTurn_visit hn hP hS v ((isTrueCorner_visit S v).mp ha)

/-- "All turns of `Q` are `τ`" read on the true corners owned by `Q`. -/
theorem forall_turn_geoCornerPolygon_iff (hn : 3 ≤ n) (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S) (τ : SignType) :
    (∀ k, turn (geoCornerPolygon hP S q) k = τ) ↔
      ∀ a : Mark P, IsTrueCorner S a → geoOwner hP S a = q → markTurn P a = τ := by
  constructor
  · intro h a ha hq
    obtain ⟨k, hk⟩ := geoCornerMark_exists_of_owner hP S q a hq ha
    subst hk
    rw [← turn_geoCornerPolygon_eq_markTurn hn hP hS q k]
    exact h k
  · intro h k
    rw [turn_geoCornerPolygon_eq_markTurn hn hP hS q k]
    exact h _ (geoCornerMark_mem hP S q k).2 (geoCornerMark_mem hP S q k).1

/-- A carrier is uniform iff one nonzero sign is the `markTurn` of every true corner it owns. -/
theorem geoCarrierUniform_iff_corners (hn : 3 ≤ n) (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S) :
    geoCarrierUniform hP S q ↔
      ∃ τ : SignType, τ ≠ 0 ∧
        ∀ a : Mark P, IsTrueCorner S a → geoOwner hP S a = q → markTurn P a = τ :=
  exists_congr fun τ => and_congr_right fun _ => forall_turn_geoCornerPolygon_iff hn hP hS q τ

end MarkTurns

/-! ## 5. def:wind's weights on the geometric carrier layer (mirror of SM/CX1.lean `carrierWeight`,
`wind`; tier 0) -/

section Wind

variable {P : LabelledTuple n}

/-- "wt(L) = 1 if all its turns are right, (−1)^{k(L)} if all are left, and 0 if its turns are
mixed" (port of `carrierWeight`): the accepted `geoCarrierSelector` of def:flat-carriers / cor (iii). -/
noncomputable def geoCarrierWeight (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : ℤ :=
  geoCarrierSelector hP S q

@[simp] theorem geoCarrierWeight_eq_selector (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : geoCarrierWeight hP S q = geoCarrierSelector hP S q := rfl

/-- "wind(S) = ∏_L wt(L)" over the carriers of `S` (port of `wind`). -/
noncomputable def geoWind (hP : CrossingGeometry P) (S : Finset (Crossing P)) : ℤ :=
  ∏ q : GeoComponent hP S, geoCarrierWeight hP S q

theorem geoWind_eq_prod_selector (hP : CrossingGeometry P) (S : Finset (Crossing P)) :
    geoWind hP S = ∏ q : GeoComponent hP S, geoCarrierSelector hP S q := rfl

/-- wt(L) = 1 if all turns of `L` are right (`CX1Data.weight_right`). -/
theorem geoCarrierWeight_of_all_right (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (h : ∀ k, turn (geoCornerPolygon hP S q) k = -1) :
    geoCarrierWeight hP S q = 1 :=
  cornerSelector_of_all_right _ h

/-- wt(L) = (−1)^{k(L)} if all turns of `L` are left (`CX1Data.weight_left`). -/
theorem geoCarrierWeight_of_all_left (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (h : ∀ k, turn (geoCornerPolygon hP S q) k = 1) :
    geoCarrierWeight hP S q = (-1 : ℤ) ^ geoCornerCount hP S q :=
  cornerSelector_of_all_left _ h

/-- wt(L) = 0 if the turns of `L` are mixed (`CX1Data.weight_mixed`). -/
theorem geoCarrierWeight_of_mixed (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (h1 : ¬ ∀ k, turn (geoCornerPolygon hP S q) k = -1)
    (h2 : ¬ ∀ k, turn (geoCornerPolygon hP S q) k = 1) : geoCarrierWeight hP S q = 0 :=
  cornerSelector_of_mixed _ h1 h2

/-- A uniform carrier has weight `(−1)^{#left corners}`: `(−1)^{k(L)}` if all-left, `1` if all-right
(port of `carrierWeight_eq_of_uniform`). -/
theorem geoCarrierWeight_eq_of_uniform (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (hu : geoCarrierUniform hP S q) :
    geoCarrierWeight hP S q = (-1) ^ geoCarrierLeftTurns hP S q := by
  obtain ⟨τ, hτ, h⟩ := hu
  rcases SignType.trichotomy τ with rfl | rfl | rfl
  · -- all turns right
    rw [geoCarrierWeight_of_all_right hP S q h]
    have h0 : geoCarrierLeftTurns hP S q = 0 := by
      unfold geoCarrierLeftTurns leftTurns
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _ hk
      rw [h k] at hk
      exact absurd hk (by decide)
    rw [h0, pow_zero]
  · exact absurd rfl hτ
  · -- all turns left
    rw [geoCarrierWeight_of_all_left hP S q h]
    congr 1
    unfold geoCarrierLeftTurns leftTurns
    rw [Finset.filter_true_of_mem (fun k _ => h k), Finset.card_univ, ZMod.card]

/-- "a mixed carrier makes its selector product zero" (port of `carrierWeight_eq_zero_of_not_uniform`). -/
theorem geoCarrierWeight_eq_zero_of_not_uniform (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (hu : ¬ geoCarrierUniform hP S q) :
    geoCarrierWeight hP S q = 0 :=
  geoCarrierWeight_of_mixed hP S q (fun h => hu ⟨-1, by decide, h⟩) (fun h => hu ⟨1, by decide, h⟩)

/-- A carrier's weight is nonzero exactly when it is uniform. -/
theorem geoCarrierWeight_ne_zero_iff (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : geoCarrierWeight hP S q ≠ 0 ↔ geoCarrierUniform hP S q := by
  constructor
  · intro hq
    by_contra hm
    exact hq (geoCarrierWeight_eq_zero_of_not_uniform hP S q hm)
  · rintro ⟨τ, hτ, hτk⟩
    cases τ with
    | zero => exact absurd rfl hτ
    | neg =>
      rw [geoCarrierWeight_of_all_right hP S q hτk]
      exact one_ne_zero
    | pos =>
      rw [geoCarrierWeight_of_all_left hP S q hτk]
      exact pow_ne_zero _ (by norm_num)

/-- **§5 U3 target `geoCarrierSelector_ne_zero_iff_uniform`**: the accepted selector of a carrier is
nonzero iff the carrier is uniform. -/
theorem geoCarrierSelector_ne_zero_iff_uniform (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : geoCarrierSelector hP S q ≠ 0 ↔ geoCarrierUniform hP S q :=
  geoCarrierWeight_ne_zero_iff hP S q

theorem geoWind_eq_zero_of_not_uniform (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (hu : ¬ geoUniformSupport hP S) : geoWind hP S = 0 := by
  obtain ⟨q, hq⟩ := not_forall.mp hu
  exact Finset.prod_eq_zero (Finset.mem_univ q) (geoCarrierWeight_eq_zero_of_not_uniform hP S q hq)

/-- For a uniform set, `wind(S) = (−1)^{total number of left carrier corners}` (port of
`wind_eq_pow_of_uniform`). -/
theorem geoWind_eq_pow_of_uniform (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (hu : geoUniformSupport hP S) :
    geoWind hP S = (-1) ^ ∑ q : GeoComponent hP S, geoCarrierLeftTurns hP S q := by
  unfold geoWind
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun q _ => geoCarrierWeight_eq_of_uniform hP S q (hu q)

/-- **§5 U3 target `geoWind_ne_zero_iff`**: `wind(S) ≠ 0` iff every carrier of `S` is uniform ("a
product of integers is nonzero only if every factor is, and the weight of a mixed carrier is 0"). -/
theorem geoWind_ne_zero_iff (hP : CrossingGeometry P) (S : Finset (Crossing P)) :
    geoWind hP S ≠ 0 ↔ geoUniformSupport hP S := by
  constructor
  · intro hw q
    by_contra hq
    exact hw (Finset.prod_eq_zero (Finset.mem_univ q) (geoCarrierWeight_eq_zero_of_not_uniform hP S q hq))
  · intro hu
    rw [geoWind_eq_pow_of_uniform hP S hu]
    exact pow_ne_zero _ (by norm_num)

end Wind

/-! ## 6. Agreement with the accepted lane on SM-generic polygons

Through the accepted §4b lemmas (SM/FlatCarriersDefs.lean:638–724) and `generic_geoCornerTurn_vertex/_visit`
(SM/FlatCarriers.lean:3414–3425) only. Write `hc := generic_crossingGeometry hn hP`,
`e := geoComponentEquivGeneric hn hP S`. The agreements of `geoCarrierRotation`, `geoCarrierLeftTurns`,
`geoCarrierRotationInt` need the corner polygon recast along the equal corner counts
(`recastTuple`, SM/CChamber.lean; `geoCornerPolygon_eq_generic`, SM/CS3.lean §B) and belong to U6. -/

section GenericAgreement

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (S : Finset (Crossing P))

/-- On a generic polygon, geometric independence is membership in `Ind(G_P)` (the accepted
`geoIndependent_iff_isDecomposition`, restated on `independentSupports`). -/
theorem geoIndependent_iff_mem_independentSupports :
    GeoIndependent (generic_crossingGeometry hn hP) S ↔ S ∈ independentSupports hn hP :=
  geoIndependent_iff_isDecomposition hn hP S

/-- `N(S)` of the geo layer is the accepted `supportNeighbors` (interlacement agrees definitionally,
`geometricInterlaces_iff_generic`). -/
theorem geoSupportNeighbors_eq_generic :
    geoSupportNeighbors (generic_crossingGeometry hn hP) S = supportNeighbors hn hP S := by
  ext y
  rw [mem_geoSupportNeighbors, mem_supportNeighbors]
  exact Iff.rfl

/-- `U(S)` of the geo layer is the accepted `supportUnselected`. -/
theorem geoSupportUnselected_eq_generic :
    geoSupportUnselected (generic_crossingGeometry hn hP) S = supportUnselected hn hP S := by
  rw [geoSupportUnselected_eq, supportUnselected_eq, geoSupportNeighbors_eq_generic]

/-- Ownership agrees through `geoComponentEquivGeneric`. -/
theorem geoOwner_eq_iff_generic (a : Mark P) (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoOwner (generic_crossingGeometry hn hP) S a = q ↔
      owner hn hP S a = geoComponentEquivGeneric hn hP S q := by
  rw [← geoComponentEquivGeneric_owner hn hP S a]
  exact (geoComponentEquivGeneric hn hP S).injective.eq_iff.symm

/-- The corner counts agree (the corner lists agree, `geoComponentCornerList_eq_generic`). -/
theorem geoCornerCount_eq_ccp (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoCornerCount (generic_crossingGeometry hn hP) S q =
      ccpCornerCount hn hP S (geoComponentEquivGeneric hn hP S q) := by
  unfold geoCornerCount ccpCornerCount
  rw [geoComponentCornerList_eq_generic]

/-- "All turns of `Q` are `τ`" read on the true corners owned by `Q`, accepted side
(`turn_ccpCornerPolygon_eq_markTurn`, SM/CX1.lean). -/
theorem forall_turn_ccpCornerPolygon_iff {S : Finset (Crossing P)}
    (hS : S ∈ independentSupports hn hP) (q' : Component hn hP S) (τ : SignType) :
    (∀ j, turn (ccpCornerPolygon hn hP S q') j = τ) ↔
      ∀ a : Mark P, IsTrueCorner S a → owner hn hP S a = q' → markTurn P a = τ := by
  constructor
  · intro h a ha hq
    obtain ⟨j, hj⟩ := ccpCornerMark_exists hn hP S q' a hq ha
    subst hj
    rw [← turn_ccpCornerPolygon_eq_markTurn hn hP hS q' j]
    exact h j
  · intro h j
    rw [turn_ccpCornerPolygon_eq_markTurn hn hP hS q' j]
    exact h _ (ccpCornerMark_isTrueCorner hn hP S q' j) (ccpCornerMark_owner hn hP S q' j)

/-- The turns of a geo corner polygon are all `τ` iff those of the accepted corner polygon of the
same carrier are (both are the `markTurn`s of the same true corners). -/
theorem forall_turn_eq_generic {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : GeoComponent (generic_crossingGeometry hn hP) S) (τ : SignType) :
    (∀ k, turn (geoCornerPolygon (generic_crossingGeometry hn hP) S q) k = τ) ↔
      ∀ j, turn (ccpCornerPolygon hn hP S (geoComponentEquivGeneric hn hP S q)) j = τ := by
  rw [forall_turn_geoCornerPolygon_iff hn (generic_crossingGeometry hn hP)
    ((geoIndependent_iff_mem_independentSupports hn hP S).mpr hS) q τ,
    forall_turn_ccpCornerPolygon_iff hn hP hS _ τ]
  exact forall_congr' fun a => imp_congr_right fun _ =>
    imp_congr_left (geoOwner_eq_iff_generic hn hP S a q)

/-- def:uniform agrees: a geo carrier of a generic polygon is uniform iff the accepted carrier is. -/
theorem geoCarrierUniform_iff_generic {S : Finset (Crossing P)}
    (hS : S ∈ independentSupports hn hP) (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoCarrierUniform (generic_crossingGeometry hn hP) S q ↔
      CarrierUniform hn hP S (geoComponentEquivGeneric hn hP S q) :=
  exists_congr fun τ => and_congr_right fun _ => forall_turn_eq_generic hn hP hS q τ

theorem geoCarrierMixed_iff_generic {S : Finset (Crossing P)}
    (hS : S ∈ independentSupports hn hP) (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoCarrierMixed (generic_crossingGeometry hn hP) S q ↔
      CarrierMixed hn hP S (geoComponentEquivGeneric hn hP S q) :=
  not_congr (geoCarrierUniform_iff_generic hn hP hS q)

/-- A generic polygon's set `S` is uniform on the geo layer iff it is a uniform decomposition. -/
theorem geoUniformSupport_iff_generic {S : Finset (Crossing P)}
    (hS : S ∈ independentSupports hn hP) :
    geoUniformSupport (generic_crossingGeometry hn hP) S ↔ UniformDecomposition hn hP S := by
  constructor
  · intro h q'
    have hq := (geoCarrierUniform_iff_generic hn hP hS ((geoComponentEquivGeneric hn hP S).symm q')).mp
      (h _)
    rwa [Equiv.apply_symm_apply] at hq
  · intro h q
    exact (geoCarrierUniform_iff_generic hn hP hS q).mpr (h _)

/-- def:wind's weight agrees with lem:C-X1's `carrierWeight` (the accepted `carrierWeight_eq_geoCarrierSelector`
of SM/CS3.lean §B proves the same equality through the recast corner polygon; here through the corner
marks, without the row module). -/
theorem geoCarrierWeight_eq_generic {S : Finset (Crossing P)}
    (hS : S ∈ independentSupports hn hP) (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoCarrierWeight (generic_crossingGeometry hn hP) S q =
      carrierWeight hn hP S (geoComponentEquivGeneric hn hP S q) := by
  have hR := forall_turn_eq_generic hn hP hS q (-1)
  have hL := forall_turn_eq_generic hn hP hS q 1
  by_cases h1 : ∀ k, turn (geoCornerPolygon (generic_crossingGeometry hn hP) S q) k = -1
  · rw [geoCarrierWeight_of_all_right _ S q h1]
    unfold carrierWeight
    rw [ite_eq_left (hR.mp h1)]
  · by_cases h2 : ∀ k, turn (geoCornerPolygon (generic_crossingGeometry hn hP) S q) k = 1
    · rw [geoCarrierWeight_of_all_left _ S q h2, geoCornerCount_eq_ccp hn hP S q]
      unfold carrierWeight
      rw [ite_eq_right (fun h => h1 (hR.mpr h)), ite_eq_left (hL.mp h2)]
    · rw [geoCarrierWeight_of_mixed _ S q h1 h2]
      unfold carrierWeight
      rw [ite_eq_right (fun h => h1 (hR.mpr h)), ite_eq_right (fun h => h2 (hL.mpr h))]

/-- `wind(S)` agrees with lem:C-X1's `wind`. -/
theorem geoWind_eq_generic {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) :
    geoWind (generic_crossingGeometry hn hP) S = wind hn hP S := by
  unfold geoWind wind
  exact Fintype.prod_equiv (geoComponentEquivGeneric hn hP S) _ _
    fun q => geoCarrierWeight_eq_generic hn hP hS q

end GenericAgreement

end SM.GeoCarrier
