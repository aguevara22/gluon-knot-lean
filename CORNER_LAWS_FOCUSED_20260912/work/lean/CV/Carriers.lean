import CV.CarrierBridges
import SM.FlatCarriers
import SM.GeoCarrierOrder
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Ported 2026-09-14 from work/drafts/cvdom/U7a/CVCarriers.lean (CV-DOM unit U7a, decision work/drafts/cvdom/DECISION_FINAL.md: CV rows on their printed binders over the accepted geo carrier layer; REPORT.md in the same directory). Rows CV:def:smoothing (`CV.smoothing_definition`), CV:def:wind (`CV.wind_definition`), CV:def:pieces (`CV.pieces_definition`). Only this header added. -/

/-! # CV/Carriers.lean — CV:def:smoothing (135), CV:def:wind (138), CV:def:pieces (139) on the
accepted geometric carrier layer (CV-DOM unit U7a)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor, for the CV-DOM decision
(work/drafts/cvdom/DECISION_FINAL.md §0 option (C), §2 fidelity, §3 rulings R1–R5, §4 review notes,
§5 unit U7a, §6 order of rows). Draft home work/drafts/cvdom/U7a/CVCarriers.lean; intended home
work/lean/CV/Carriers.lean (the row module of CV:def:smoothing / lem:carriers / lem:carrierword; the
def:wind and def:pieces parts may be split off into CV/Wind.lean and CV/Pieces.lean as §5 lists).
Source: reference/R/CV/d1_setup.tex (frozen): def:smoothing 355–361, def:wind 487–512, def:pieces
514–520; the subsection preamble 303–313 ("Fix a diagrammatic polygon P … Everything in this
subsection … is stated for that class") fixes the standing binder.

Row declarations: `CV.smoothing_definition : CV.SmoothingDefinitionData hD S hS` (135),
`CV.wind_definition : CV.WindDefinitionData hG S hS` (138; hypothesis form
`CV.wind_definition_of_traced`), `CV.pieces_definition : CV.PiecesDefinitionData hD S hS` (139).
Each field of a `…DefinitionData` structure renders one printed clause and quotes it.

## Binders (as printed; DECISION_FINAL §2 "Fidelity", no domain change)

* def:smoothing, def:pieces: `hD : CV.Diagrammatic P` (the subsection's standing hypothesis,
  d1:305–309) and `hS : S ∈ CV.Ind hD.crossingGeometry` (the accepted CV:def:interlace, `CV.Ind`).
* def:wind: `hG : CV.Generic P` ("Let P be generic … the generic binder is part of this
  definition and not decoration", d1:488–499) and `hS : S ∈ CV.Ind hG.crossingGeometry`.
* `hn : 3 ≤ n` (CV def:polygon "Let n ≥ 3", d1:9; prop:chamberinv "Fix n ≥ 3", d1:932) is NOT a
  parameter of any bundle or row theorem; the fields whose geo lemmas consume it quantify it
  locally (`∀ (_hn : 3 ≤ n), …`), the pattern of the accepted `CV.InterlaceData.vertices`
  (ruling R5: keep `hn` exactly where the source proofs use it).

## Printed notions → Lean (the accepted `SM.GeoCarrier` objects of def:flat-carriers,
SM/FlatCarriersDefs.lean, read through `hD.crossingGeometry` / `hG.crossingGeometry`; write `hP`)

* the traversal circle marked at every original vertex and every crossing visit: `Mark P =
  ZMod n ⊕ Visit P` at the positions `geoMarkPosition hP`; its successor `ρ = geoMarkSuccessor hP`.
* "the oriented smoothing of P along S": the reconnected successor `ρ_S = geoSmoothingSuccessor hP S
  = ρ ∘ selectedMarkPerm S` — at the two visits `v`, `visitTwin v` of each selected crossing the two
  outgoing successors are exchanged; nothing else changes. The ownership of the two visits of a
  selected crossing (which visit belongs to which carrier) follows SM conv:selected-visits
  (`SM.selected_visits_convention`, the SAME `selectedMarkPerm`): a mark keeps its own cycle, the
  incoming arc at `v` continues along the outgoing arc of `visitTwin v` — a disambiguation the CV
  text leaves implicit and which every review cites (DECISION_FINAL §4).
* "the carriers of S": the cycles of `ρ_S`, the accepted `GeoComponent hP S`; `geoOwner hP S a` is
  the carrier through the mark `a`; the closed oriented curve a carrier traces is
  `geoComponentPlaneCycle hP S q` (its marks `geoComponentMarkList hP S q` in inherited order,
  consecutive marks joined by the inherited straight pieces `geoSmoothingSegment hP S a`).
* "corner of a carrier": a mark of the carrier that is an original vertex or a smoothing site
  (selected visit): `IsTrueCorner S`, listed in `geoComponentCornerList hP S q`, enumerated as
  `geoCornerMark hP S q k`, `k : ZMod c(L)` with `c(L) = geoCornerCount hP S q`; the carrier read
  at its corners is the polygon `geoCornerPolygon hP S q`, whose `turn … k ∈ {−1, 0, +1}` (`+1` =
  left turn, `−1` = right turn, `SM.turn = sign det(in, out)`, `turn_det`) is the carrier's turn at
  its `k`-th corner. The incoming/outgoing original edge directions at a corner mark `a` are
  `edge P (geoInEdge hP a)` / `edge P (geoOutSlot hP S a).1` (SM/FlatCarriers.lean §4).
* uniform / mixed carrier: `CV.CarrierUniform` / `CV.CarrierMixed`; weight `wt(L)`: `CV.weight`
  (= the accepted `geoCarrierSelector`, the `cornerSelector` of the corner polygon: `+1` all right,
  `(−1)^{c(L)}` all left, `0` mixed); `wind(S) = ∏_L wt(L)`: `CV.wind`.
* `U(S) = [m] ∖ (S ∪ N_{G_P}(S))`: the accepted `CV.U hP S` (`CV.N` = `N_{G_P}`; vertex set `[m]` =
  `SM.Crossing P`, CV:def:interlace); "the induced subgraph `G_P[U(S)]`": `CV.residualGraph hP S`
  (Mathlib `SimpleGraph.induce` of the accepted `geometricInterlacementGraph hP`); "the residual
  pieces … connected components `H ∈ π₀(G_P[U(S)])`": `CV.Piece hP S`
  (`SimpleGraph.ConnectedComponent`), the piece of `c ∈ U(S)` is `CV.pieceOf hP S c hc`, its
  label set `CV.pieceLabels hP S H : Finset (Crossing P)`. Auxiliary notation for the later rows
  (def:piecediagram's `w(H) = |H|`, def:X1's "pieces carried by L"): `CV.pieceWrithe`,
  `CV.piecesOn` (lem:carriers (iv), row 136, is the theorem that every piece is carried by exactly
  one carrier; it is NOT a clause of def:pieces).

## On SM-generic polygons

these ARE the accepted def:smoothing / lem:carriers objects: `geoSmoothingSuccessor_eq_generic`,
`geoComponentEquivGeneric`, `geoComponentCornerList_eq_generic` (SM/FlatCarriersDefs.lean:638–724),
`generic_geoCornerTurn_vertex/_visit` (SM/FlatCarriers.lean:3414–3425), `CV.Ind_eq_generic`,
`CV.U_eq_generic` (CV/Events.lean). No accepted declaration is redefined or shadowed.

## Dependence on the port (DECISION_FINAL §5)

Placeholder-free. The only lane input beyond the accepted library is unit U1b's
`SM.GeoCarrier.geoTracedSuccessor_of_independent` (SM/GeoCarrierOrder.lean, landed 2026-09-14): for an
independent `S`, consecutive entries of a carrier's inherited mark list are `ρ_S`-successors
(`SM.GeoCarrier.TracedSuccessor`, the field `traced_successor` of the accepted `GeoCarrierSpec`),
wrapped here as `CV.tracedSuccessor_of_mem_Ind` on the CV binder `S ∈ Ind hP`. It is consumed only
by the def:wind fields `turn_sign`, `turn_ne_zero`, `vertex_corner`, `smoothing_corner`,
`uniform_same_way`, through `CV.wind_definition_of_traced` (the bundle with `TracedSuccessor` as an
explicit hypothesis); given `TracedSuccessor`, the accepted tier-0 lemma
`geoCornerPolygon_turn_eq_sign` yields `turn = sign det(in, out)`, and nonvanishing follows from
CV's (G1) (`CV.Generic.turn_ne_zero`) at vertex corners and from (G5) / `CrossingGeometry` clause 2
(`crossing_det_ne_zero_of_geometry`) at smoothing corners — no tier-2 (U2b) fact is needed.
def:smoothing and def:pieces use only the accepted library.

Checked with `cd work/lean && lake env lean ../drafts/cvdom/U7a/CVCarriers.lean`. -/

namespace CV

open SM SM.Carrier SM.GeoCarrier

/-! ## 1. The printed counterexample of def:wind (d1_setup.tex:496–499): `((0,0),(1,0),(2,0),(0,1))` is
diagrammatic with a zero turn

Placed before the classical instance so that the `ZMod 4` casework is decided by `decide` (as in
the accepted tangency example, CV/Events.lean `remote4_iff`, `zmod4_cases`, which are reused). -/

section FlatExample

/-- "`((0,0),(1,0),(2,0),(0,1))`" (d1_setup.tex:497), vertices `p_1, …, p_4` at the indices
`0, …, 3`. -/
noncomputable def flatExample : LabelledTuple 4 :=
  (![((0 : ℝ), (0 : ℝ)), (1, 0), (2, 0), (0, 1)] : Fin 4 → Plane)

theorem flatExample_vals :
    flatExample 0 = (0, 0) ∧ flatExample 1 = (1, 0) ∧ flatExample 2 = (2, 0) ∧
    flatExample 3 = (0, 1) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem zmod4_indices : (0 : ZMod 4) + 1 = 1 ∧ (1 : ZMod 4) + 1 = 2 ∧ (2 : ZMod 4) + 1 = 3 ∧
    (3 : ZMod 4) + 1 = 0 ∧ (1 : ZMod 4) - 1 = 0 := by
  decide

theorem flatExample_edges :
    edge flatExample 0 = (1, 0) ∧ edge flatExample 1 = (1, 0) ∧ edge flatExample 2 = (-2, 1) ∧
    edge flatExample 3 = (0, -1) := by
  obtain ⟨p0, p1, p2, p3⟩ := flatExample_vals
  obtain ⟨a0, a1, a2, a3, -⟩ := zmod4_indices
  simp only [edge, a0, a1, a2, a3, p0, p1, p2, p3]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (ext <;> norm_num)

/-- "its turn at `p_2` is exactly zero" (the vertex `(1,0)`, index `1`). -/
theorem flatExample_turn : turn flatExample 1 = 0 := by
  obtain ⟨e0, e1, -, -⟩ := flatExample_edges
  rw [turn_det, zmod4_indices.2.2.2.2, e0, e1]
  simp [det]

/-- No point of a closed edge of the example lies on a closed remote edge (the pairs `{0, 2}`,
`{1, 3}`). -/
theorem flatExample_remote_disjoint (i j : ZMod 4) (hr : remote i j) (x : Plane)
    (hi : x ∈ edgeSegment flatExample i) (hj : x ∈ edgeSegment flatExample j) : False := by
  obtain ⟨p0, p1, p2, p3⟩ := flatExample_vals
  obtain ⟨e0, e1, e2, e3⟩ := flatExample_edges
  obtain ⟨t, ht0, ht1, hx⟩ := hi
  obtain ⟨s, hs0, hs1, hy⟩ := hj
  rw [hx] at hy
  rcases (remote4_iff i j).mp hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [edgePoint, p0, p1, p2, p3, e0, e1, e2, e3, Prod.ext_iff, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hy <;>
    obtain ⟨h1, h2⟩ := hy <;> nlinarith

/-- Any three distinct edges of a 4-gon contain a remote pair. -/
theorem zmod4_triple_remote (i j k : ZMod 4) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    remote i j ∨ remote j k ∨ remote i k := by
  revert i j k; unfold remote adjacent; decide

theorem flatExample_crossingGeometry : CrossingGeometry flatExample := by
  obtain ⟨e0, e1, e2, e3⟩ := flatExample_edges
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [e0, e1, e2, e3, ne_eq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] <;> norm_num
  · intro i j hr x hi hj
    exact (flatExample_remote_disjoint i j hr x hi hj).elim
  · rintro ⟨i, j, k, x, hij, hjk, hik, hi, hj, hk⟩
    rcases zmod4_triple_remote i j k hij hjk hik with hr | hr | hr
    · exact flatExample_remote_disjoint i j hr x (edgeInterior_subset_edgeSegment _ _ hi)
        (edgeInterior_subset_edgeSegment _ _ hj)
    · exact flatExample_remote_disjoint j k hr x (edgeInterior_subset_edgeSegment _ _ hj)
        (edgeInterior_subset_edgeSegment _ _ hk)
    · exact flatExample_remote_disjoint i k hr x (edgeInterior_subset_edgeSegment _ _ hi)
        (edgeInterior_subset_edgeSegment _ _ hk)

/-- No vertex of the example lies on a closed edge not incident to it. -/
theorem flatExample_vertex_off (k e : ZMod 4) (h : ¬ incident k e) :
    flatExample k ∉ edgeSegment flatExample e := by
  obtain ⟨p0, p1, p2, p3⟩ := flatExample_vals
  obtain ⟨e0, e1, e2, e3⟩ := flatExample_edges
  rintro ⟨t, ht0, ht1, hx⟩
  rcases zmod4_cases k with rfl | rfl | rfl | rfl <;> rcases zmod4_cases e with rfl | rfl | rfl | rfl <;>
    first
    | exact h (by unfold incident; decide)
    | (simp only [edgePoint, p0, p1, p2, p3, e0, e1, e2, e3, Prod.ext_iff, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hx
       obtain ⟨h1, h2⟩ := hx
       nlinarith)

/-- "`((0,0),(1,0),(2,0),(0,1))` is diagrammatic". -/
theorem flatExample_diagrammatic : Diagrammatic flatExample :=
  diagrammatic_of_crossingGeometry (by norm_num) flatExample_crossingGeometry flatExample_vertex_off

/-- … and hence not generic: "the generic binder is part of this definition and not decoration". -/
theorem flatExample_not_generic : ¬ Generic flatExample :=
  fun h => h.turn_ne_zero 1 flatExample_turn

end FlatExample

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-! ## 2. The inherited order of the carriers (unit U1b), on the CV binder -/

/-- Unit U1b's `SM.GeoCarrier.geoTracedSuccessor_of_independent` (SM/GeoCarrierOrder.lean) on the CV
binder `S ∈ Ind(G_P)` (ruling R2, `CV.mem_Ind_iff_geoIndependent`): for an independent support `S` on
a geometric record domain, consecutive entries of a carrier's inherited mark list are
`ρ_S`-successors (cyclically) — the `traced_successor` field of the accepted `GeoCarrierSpec`
(lem:carriers (i), "each carrier traverses the visits assigned to it in the cyclic order inherited
from the original traversal circle"). -/
theorem tracedSuccessor_of_mem_Ind (hn : 3 ≤ n) (hP : CrossingGeometry P) {S : Finset (Crossing P)}
    (hS : S ∈ Ind hP) (q : GeoComponent hP S) : TracedSuccessor hP S q :=
  geoTracedSuccessor_of_independent hn hP ((mem_Ind_iff_geoIndependent hP S).mp hS) q

/-! ## 3. Small geometric facts at a selected crossing (tier 0) -/

section SelectedSite

omit [NeZero n] in
/-- The two edges met at a crossing visit `v` — its own edge `v.2` and its twin's edge — are the
edge pair of the crossing `v.1` (`visit_crossing_val_eq_pair`), hence transverse on the geometric
record domain (`CrossingGeometry` clause 2 = CV's (G5) at an active crossing). -/
theorem det_visit_twin_ne_zero (hP : CrossingGeometry P) (v : Visit P) :
    det (edge P v.2.val) (edge P (visitTwin v).2.val) ≠ 0 := by
  have hcr : IsCrossing P {v.2.val, (visitTwin v).2.val} := by
    have h := v.1.property
    rwa [visit_crossing_val_eq_pair v] at h
  exact crossing_det_ne_zero_of_geometry hP hcr

omit [NeZero n] in
theorem crossingSign_visit_twin_ne_zero (hP : CrossingGeometry P) (v : Visit P) :
    crossingSign P v.2.val (visitTwin v).2.val ≠ 0 :=
  sign_ne_zero.mpr (det_visit_twin_ne_zero hP v)

omit [NeZero n] in
/-- Both visits of a crossing are marked at the crossing point. -/
theorem geoMarkPosition_evaluation_visit_twin (hP : CrossingGeometry P) (v : Visit P) :
    traversalEvaluation P (geoMarkPosition hP (Sum.inr (visitTwin v))) = crossingPoint v.1 :=
  geoMarkPosition_evaluation_visit hP (visitTwin v)

end SelectedSite

/-- `IsTrueCorner S a` spelled out: an original vertex, or a visit of a selected crossing. -/
theorem isTrueCorner_iff (S : Finset (Crossing P)) (a : Mark P) :
    IsTrueCorner S a ↔ (∃ i : ZMod n, a = Sum.inl i) ∨ ∃ v : Visit P, a = Sum.inr v ∧ v.1 ∈ S := by
  cases a with
  | inl i => exact ⟨fun _ => Or.inl ⟨i, rfl⟩, fun _ => isTrueCorner_vertex S i⟩
  | inr v =>
    constructor
    · intro h
      exact Or.inr ⟨v, rfl, (isTrueCorner_visit S v).mp h⟩
    · rintro (⟨i, hi⟩ | ⟨w, hw, hwS⟩)
      · exact (Sum.inr_ne_inl hi).elim
      · rw [Sum.inr.inj hw]
        exact (isTrueCorner_visit S w).mpr hwS

/-! ## 4. Row 135 — CV:def:smoothing (d1_setup.tex:355–361)

Printed text: "For `S ∈ Ind(G_P)`, the *oriented smoothing of `P` along `S`* replaces, at each double
point of `S`, the two transversally crossing arcs by the two arcs that respect the orientation of
`P` and do not cross. The result is a disjoint union of closed oriented curves, called the
*carriers* of `S`."

Read on the marked traversal circle (the finite successor model of SM def:smoothing /
conv:selected-visits, restated on the geometric record domain by the accepted def:flat-carriers):
`ρ = geoMarkSuccessor hP`, `ρ_S = geoSmoothingSuccessor hP S`, `hP = hD.crossingGeometry`. -/

section Smoothing

variable (hD : Diagrammatic P) (S : Finset (Crossing P))

/-- CV:def:smoothing, one field per printed clause, at one support `S ∈ Ind(G_P)` of a
diagrammatic polygon `P`. Notation in the docstrings: `ρ = geoMarkSuccessor`, `ρ_S =
geoSmoothingSuccessor`, `⟦a⟧ = traversalEvaluation P (geoMarkPosition hP a)` (the plane point of the
mark `a`), `hP = hD.crossingGeometry`. -/
structure SmoothingDefinitionData (_hS : S ∈ Ind hD.crossingGeometry) : Prop where
  /-- "at each double point of `S`": the smoothing acts at the two visits `v`, `visitTwin v` of every
  selected crossing — the arc arriving at `v` continues along the arc leaving `visitTwin v` and the
  arc arriving at `visitTwin v` along the arc leaving `v` (`ρ_S v = ρ (twin v)`, `ρ_S (twin v) = ρ v`;
  SM conv:selected-visits, the same `selectedMarkPerm`) -/
  reconnect_selected : ∀ v : Visit P, v.1 ∈ S →
    geoSmoothingSuccessor hD.crossingGeometry S (Sum.inr v) =
        geoMarkSuccessor hD.crossingGeometry (Sum.inr (visitTwin v)) ∧
    geoSmoothingSuccessor hD.crossingGeometry S (Sum.inr (visitTwin v)) =
        geoMarkSuccessor hD.crossingGeometry (Sum.inr v)
  /-- … and only there: a visit of an unselected crossing keeps its outgoing successor -/
  keep_unselected : ∀ v : Visit P, v.1 ∉ S →
    geoSmoothingSuccessor hD.crossingGeometry S (Sum.inr v) =
      geoMarkSuccessor hD.crossingGeometry (Sum.inr v)
  /-- … and so does every original vertex -/
  keep_vertex : ∀ i : ZMod n,
    geoSmoothingSuccessor hD.crossingGeometry S (Sum.inl i) =
      geoMarkSuccessor hD.crossingGeometry (Sum.inl i)
  /-- "the two transversally crossing arcs": at a double point `v.1 ∈ S` the two arcs are the edges
  `v.2` and `(visitTwin v).2` of the crossing, both visits are marked at the crossing point, and the
  two edge directions are transverse (`det ≠ 0`) -/
  transverse : ∀ v : Visit P, v.1 ∈ S →
    v.1.val = {v.2.val, (visitTwin v).2.val} ∧
    traversalEvaluation P (geoMarkPosition hD.crossingGeometry (Sum.inr v)) = crossingPoint v.1 ∧
    traversalEvaluation P (geoMarkPosition hD.crossingGeometry (Sum.inr (visitTwin v))) =
      crossingPoint v.1 ∧
    det (edge P v.2.val) (edge P (visitTwin v).2.val) ≠ 0
  /-- "the two arcs that respect the orientation of `P`": the new arc through the visit `v` of a
  selected crossing arrives along the edge `v.2` in its positive direction and leaves along the
  twin's edge `(visitTwin v).2` in its positive direction (the incoming displacement at `v` is a
  positive multiple of `edge P v.2`, the outgoing one a positive multiple of
  `edge P (visitTwin v).2`); `n ≥ 3` -/
  oriented_arcs : ∀ (_hn : 3 ≤ n) (v : Visit P), v.1 ∈ S →
    (∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hD.crossingGeometry (Sum.inr v)) -
        traversalEvaluation P (geoMarkPosition hD.crossingGeometry
          ((geoSmoothingSuccessor hD.crossingGeometry S).symm (Sum.inr v))) =
        c • edge P v.2.val) ∧
    (∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hD.crossingGeometry
          (geoSmoothingSuccessor hD.crossingGeometry S (Sum.inr v))) -
        traversalEvaluation P (geoMarkPosition hD.crossingGeometry (Sum.inr v)) =
        c • edge P (visitTwin v).2.val)
  /-- "and do not cross": the two new arcs at a double point of `S` bend to opposite sides of the
  crossing point — the arc through `v` turns from `edge P v.2` to `edge P (visitTwin v).2` with the
  nonzero sign `sgn det(d_{v.2}, d_{twin})`, the arc through `visitTwin v` with the opposite sign
  (the oriented resolution; the original pairing `v ↦ v`, `twin ↦ twin` is the one that crosses) -/
  noncrossing_arcs : ∀ v : Visit P, v.1 ∈ S →
    crossingSign P v.2.val (visitTwin v).2.val ≠ 0 ∧
    crossingSign P (visitTwin v).2.val v.2.val = - crossingSign P v.2.val (visitTwin v).2.val
  /-- "called the *carriers* of `S`": the carriers are the cycles of `ρ_S` — two marks lie on the
  same carrier iff they are in the same `ρ_S`-cycle (a mark keeps its own cycle: conv:selected-visits) -/
  carriers : ∀ a b : Mark P,
    geoOwner hD.crossingGeometry S a = geoOwner hD.crossingGeometry S b ↔
      (geoSmoothingSuccessor hD.crossingGeometry S).SameCycle a b
  /-- "closed oriented curves": each carrier is carried into itself by `ρ_S` (closed, and oriented
  by the direction of traversal), and every carrier is the cycle of one of its marks -/
  closed_oriented :
    (∀ a : Mark P, geoOwner hD.crossingGeometry S (geoSmoothingSuccessor hD.crossingGeometry S a) =
      geoOwner hD.crossingGeometry S a) ∧
    ∀ q : GeoComponent hD.crossingGeometry S, ∃ a : Mark P, geoOwner hD.crossingGeometry S a = q
  /-- "a disjoint union": every mark of the traversal circle lies on exactly one carrier — the mark
  lists of distinct carriers are disjoint and together exhaust the marks -/
  disjoint_union :
    (∀ (m : Mark P) (q q' : GeoComponent hD.crossingGeometry S),
      m ∈ geoComponentMarkList hD.crossingGeometry S q →
      m ∈ geoComponentMarkList hD.crossingGeometry S q' → q = q') ∧
    ∀ m : Mark P, ∃ q : GeoComponent hD.crossingGeometry S,
      m ∈ geoComponentMarkList hD.crossingGeometry S q
  /-- the curve a carrier traces: the closed polygonal cycle of the plane points of its marks in
  the inherited cyclic order; its mark list is duplicate-free, nonempty, and lists exactly the marks
  it owns -/
  traced_curve : ∀ q : GeoComponent hD.crossingGeometry S,
    geoComponentPlaneCycle hD.crossingGeometry S q =
      ((geoComponentMarkList hD.crossingGeometry S q).map
        (fun m => traversalEvaluation P (geoMarkPosition hD.crossingGeometry m)) : Cycle Plane) ∧
    (geoComponentMarkList hD.crossingGeometry S q).Nodup ∧
    0 < (geoComponentMarkList hD.crossingGeometry S q).length ∧
    ∀ m : Mark P, m ∈ geoComponentMarkList hD.crossingGeometry S q ↔
      geoOwner hD.crossingGeometry S m = q
  /-- its sides are the inherited straight pieces: from each mark `a` straight to its `ρ_S`-successor,
  inside the closed original edge of the outgoing slot of `a` (the edge of `a` itself, or of its twin
  at a selected visit) -/
  straight_pieces : ∀ (a : Mark P) (u : ℝ),
    geoSmoothingSegment hD.crossingGeometry S a u =
      traversalEvaluation P (geoMarkPosition hD.crossingGeometry a) +
        u • (traversalEvaluation P (geoMarkPosition hD.crossingGeometry
            (geoSmoothingSuccessor hD.crossingGeometry S a)) -
          traversalEvaluation P (geoMarkPosition hD.crossingGeometry a)) ∧
    (0 ≤ u → u ≤ 1 →
      geoSmoothingSegment hD.crossingGeometry S a u ∈
        edgeSegment P (geoOutSlot hD.crossingGeometry S a).1)
  /-- … and each piece runs in the positive direction of that original edge (the orientation of
  `P` is respected along every carrier); `n ≥ 3` -/
  inherited_direction : ∀ (_hn : 3 ≤ n) (a : Mark P), ∃ c : ℝ, 0 < c ∧
    traversalEvaluation P (geoMarkPosition hD.crossingGeometry
        (geoSmoothingSuccessor hD.crossingGeometry S a)) -
      traversalEvaluation P (geoMarkPosition hD.crossingGeometry a) =
      c • edge P (geoOutSlot hD.crossingGeometry S a).1

/-- **Row 135, CV:def:smoothing**, on the printed binder `hD : Diagrammatic P`, `S ∈ Ind(G_P)`. -/
theorem smoothing_definition (hS : S ∈ Ind hD.crossingGeometry) :
    SmoothingDefinitionData hD S hS where
  reconnect_selected v hv :=
    ⟨geoSmoothingSuccessor_visit_of_mem hD.crossingGeometry S v hv, by
      rw [geoSmoothingSuccessor_visit_of_mem hD.crossingGeometry S (visitTwin v)
        (by rw [visitTwin_crossing]; exact hv), visitTwin_involutive]⟩
  keep_unselected := geoSmoothingSuccessor_visit_of_not_mem hD.crossingGeometry S
  keep_vertex _ := rfl
  transverse v _ :=
    ⟨visit_crossing_val_eq_pair v, geoMarkPosition_evaluation_visit hD.crossingGeometry v,
      geoMarkPosition_evaluation_visit_twin hD.crossingGeometry v,
      det_visit_twin_ne_zero hD.crossingGeometry v⟩
  oriented_arcs hn v hv :=
    ⟨geo_visit_incoming_direction hn hD.crossingGeometry S v,
      geo_selected_visit_outgoing_direction hn hD.crossingGeometry S v hv⟩
  noncrossing_arcs v _ :=
    ⟨crossingSign_visit_twin_ne_zero hD.crossingGeometry v,
      crossingSign_swap P v.2.val (visitTwin v).2.val⟩
  carriers := geoOwner_eq_iff hD.crossingGeometry S
  closed_oriented := ⟨geoOwner_successor hD.crossingGeometry S, geoOwner_surjective hD.crossingGeometry S⟩
  disjoint_union :=
    ⟨fun m q q' hq hq' =>
      ((mem_geoComponentMarkList hD.crossingGeometry S q m).mp hq).symm.trans
        ((mem_geoComponentMarkList hD.crossingGeometry S q' m).mp hq'),
      fun m => ⟨geoOwner hD.crossingGeometry S m,
        (mem_geoComponentMarkList hD.crossingGeometry S _ m).mpr rfl⟩⟩
  traced_curve q :=
    ⟨rfl, geoComponentMarkList_nodup hD.crossingGeometry S q,
      geoComponentMarkList_length_pos hD.crossingGeometry S q,
      mem_geoComponentMarkList hD.crossingGeometry S q⟩
  straight_pieces a u :=
    ⟨rfl, fun hu0 hu1 => geoSmoothingSegment_mem_edgeSegment hD.crossingGeometry S a u hu0 hu1⟩
  inherited_direction hn a := geoSmoothingSegment_positive_direction hn hD.crossingGeometry S a

end Smoothing

/-! ## 5. Row 138 — CV:def:wind (d1_setup.tex:487–512)

Printed text: "Let `P` be *generic* and `S ∈ Ind(G_P)` — the binders under which the definition is
read […]. A *corner* of a carrier of `S` is either a vertex `p_i` of `P` traversed by it or a
smoothing site of `S` traversed by it. At each corner the carrier turns *left* or *right* according
to the sign of the determinant of the incoming and outgoing directions, which under genericity is
nonzero: at a vertex by (G1), unconditional and hence relevant, at a smoothing site by (G5), active
at a crossing. On a merely diagrammatic polygon the vertex clause is false — `((0,0),(1,0),(2,0),(0,1))`
is diagrammatic and its turn at `p_2` is exactly zero — which is why the generic binder is part of
this definition and not decoration. A carrier is *uniform* if all its corners turn the same way and
*mixed* otherwise. Its *weight* is `wt(L) = +1` (`L` uniform, all turns right), `(−1)^{c(L)}` (`L`
uniform, all turns left, `c(L) = #corners`), `0` (`L` mixed), and `wind(S) = ∏_L wt(L)`, the product
over the `|S|+1` carriers of `S`. In particular `wind(S) ≠ 0` forces every carrier of `S` to be
uniform: `wind(S)` is a product of integers, a product of integers is nonzero only if every factor
is, and the weight of a mixed carrier is `0`."

Conventions: SM `turn = sign det(incoming, outgoing)` (`turn_det`); `+1` = left turn, `−1` = right
turn (the same convention as CV def:rot's `ε_i = +1` case, `det(δ_{i−1},δ_i) > 0`, CV/Rotation.lean).
The definitions are stated on `hP : CrossingGeometry P` (they are read at `hG.crossingGeometry`
in the row and at SM-generic polygons in Bridge:B4); only the turn clauses use genericity. -/

section WindDefs

variable (hP : CrossingGeometry P) (S : Finset (Crossing P))

/-- def:wind: `wt(L)` — `+1` if all corners turn right, `(−1)^{c(L)}` if all turn left, `0` if
mixed: the accepted `cornerSelector` of the carrier's corner polygon (`geoCarrierSelector`). -/
noncomputable def weight (q : GeoComponent hP S) : ℤ := geoCarrierSelector hP S q

/-- def:wind: `wind(S) = ∏_L wt(L)`, the product over the carriers of `S`. -/
noncomputable def wind : ℤ := ∏ q : GeoComponent hP S, weight hP S q

/-- def:wind: "uniform if all its corners turn the same way" — one nonzero sign `τ` at every corner
(the SM def:uniform form; equivalent to "all turns equal" once turns are nonzero,
`uniform_iff_same_way_of_ne_zero`). -/
def CarrierUniform (q : GeoComponent hP S) : Prop :=
  ∃ τ : SignType, τ ≠ 0 ∧ ∀ k, turn (geoCornerPolygon hP S q) k = τ

/-- def:wind: "and mixed otherwise". -/
def CarrierMixed (q : GeoComponent hP S) : Prop := ¬ CarrierUniform hP S q

theorem weight_of_all_right (q : GeoComponent hP S)
    (h : ∀ k, turn (geoCornerPolygon hP S q) k = -1) : weight hP S q = 1 :=
  cornerSelector_of_all_right _ h

theorem weight_of_all_left (q : GeoComponent hP S)
    (h : ∀ k, turn (geoCornerPolygon hP S q) k = 1) :
    weight hP S q = (-1 : ℤ) ^ geoCornerCount hP S q :=
  cornerSelector_of_all_left _ h

theorem weight_of_mixed (q : GeoComponent hP S) (h : CarrierMixed hP S q) : weight hP S q = 0 := by
  apply cornerSelector_of_mixed
  · intro hr
    exact h ⟨-1, by decide, hr⟩
  · intro hl
    exact h ⟨1, by decide, hl⟩

/-- A carrier's weight is nonzero exactly when it is uniform. -/
theorem weight_ne_zero_iff (q : GeoComponent hP S) : weight hP S q ≠ 0 ↔ CarrierUniform hP S q := by
  constructor
  · intro hq
    by_contra hm
    exact hq (weight_of_mixed hP S q hm)
  · rintro ⟨τ, hτ, hτk⟩
    cases τ with
    | zero => exact absurd rfl hτ
    | neg =>
      rw [weight_of_all_right hP S q hτk]
      exact one_ne_zero
    | pos =>
      rw [weight_of_all_left hP S q hτk]
      exact pow_ne_zero _ (by norm_num)

/-- "`wind(S)` is a product of integers, a product of integers is nonzero only if every factor is,
and the weight of a mixed carrier is `0`." -/
theorem wind_ne_zero_imp (hw : wind hP S ≠ 0) :
    (∀ q, weight hP S q ≠ 0) ∧ ∀ q, CarrierUniform hP S q := by
  have hq : ∀ q, weight hP S q ≠ 0 := fun q h0 =>
    hw (Finset.prod_eq_zero (Finset.mem_univ q) h0)
  exact ⟨hq, fun q => (weight_ne_zero_iff hP S q).mp (hq q)⟩

/-- Once every turn of a carrier is nonzero, "uniform" is literally "all corners turn the same way". -/
theorem uniform_iff_same_way_of_ne_zero (q : GeoComponent hP S)
    (h0 : ∀ k, turn (geoCornerPolygon hP S q) k ≠ 0) :
    CarrierUniform hP S q ↔ ∀ k k', turn (geoCornerPolygon hP S q) k = turn (geoCornerPolygon hP S q) k' := by
  constructor
  · rintro ⟨τ, -, hτ⟩ k k'
    rw [hτ k, hτ k']
  · intro h
    exact ⟨turn (geoCornerPolygon hP S q) 0, h0 0, fun k => h k 0⟩

/-- The corners of a carrier are enumerated without repetition by `geoCornerMark q k`,
`k : ZMod c(L)`, `c(L) = geoCornerCount` = the length of its corner list. -/
theorem corners_enumerated (q : GeoComponent hP S) :
    geoCornerCount hP S q = (geoComponentCornerList hP S q).length ∧
    Function.Injective (geoCornerMark hP S q) ∧
    ∀ a ∈ geoComponentCornerList hP S q, ∃ k, geoCornerMark hP S q k = a := by
  refine ⟨rfl, geoCornerMark_injective hP S q, ?_⟩
  intro a ha
  obtain ⟨hq, hc⟩ := (mem_geoComponentCornerList hP S q a).mp ha
  subst hq
  exact geoCornerMark_exists hP S hc

/-! ### Turns at the corners, given the inherited order (`TracedSuccessor`, unit U1b) -/

/-- "At each corner the carrier turns left or right according to the sign of the determinant of the
incoming and outgoing directions": the accepted tier-0 `geoCornerPolygon_turn_eq_sign`. -/
theorem turn_eq_sign_of_traced (hn : 3 ≤ n) (q : GeoComponent hP S) (htr : TracedSuccessor hP S q)
    (k : ZMod (geoCornerCount hP S q)) :
    turn (geoCornerPolygon hP S q) k =
      SignType.sign (det (edge P (geoInEdge hP (geoCornerMark hP S q k)))
        (edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1)) :=
  geoCornerPolygon_turn_eq_sign hn hP S q htr k

/-- At an original vertex `p_i` the carrier arrives along `e_{i-1}` and leaves along `e_i`: its
turn there is the turn `τ_i` of `P`. -/
theorem turn_vertex_of_traced (hn : 3 ≤ n) (q : GeoComponent hP S) (htr : TracedSuccessor hP S q)
    (k : ZMod (geoCornerCount hP S q)) (i : ZMod n) (h : geoCornerMark hP S q k = Sum.inl i) :
    turn (geoCornerPolygon hP S q) k = turn P i := by
  rw [turn_eq_sign_of_traced hP S hn q htr k, h, geoInEdge_vertex hn, geoOutSlot_vertex, turn_det]

/-- At a smoothing site (the visit `v` of a selected crossing) the carrier arrives along the edge
`v.2` and leaves along the twin's edge: its turn there is `sgn det(d_{v.2}, d_{twin})`. -/
theorem turn_visit_of_traced (hn : 3 ≤ n) (q : GeoComponent hP S) (htr : TracedSuccessor hP S q)
    (k : ZMod (geoCornerCount hP S q)) (v : Visit P) (h : geoCornerMark hP S q k = Sum.inr v)
    (hv : v.1 ∈ S) :
    turn (geoCornerPolygon hP S q) k = crossingSign P v.2.val (visitTwin v).2.val := by
  rw [turn_eq_sign_of_traced hP S hn q htr k, h, geoInEdge_visit hn, geoOutSlot_selected hP S v hv]
  rfl

end WindDefs

section WindGeneric

variable (hG : Generic P) (S : Finset (Crossing P))

/-- "which under genericity is nonzero: at a vertex by (G1) …, at a smoothing site by (G5)". -/
theorem turn_ne_zero_of_traced (hn : 3 ≤ n) (q : GeoComponent hG.crossingGeometry S)
    (htr : TracedSuccessor hG.crossingGeometry S q) (k : ZMod (geoCornerCount hG.crossingGeometry S q)) :
    turn (geoCornerPolygon hG.crossingGeometry S q) k ≠ 0 := by
  have hc := isTrueCorner_geoCornerMark hG.crossingGeometry S q k
  cases hm : geoCornerMark hG.crossingGeometry S q k with
  | inl i =>
    rw [turn_vertex_of_traced hG.crossingGeometry S hn q htr k i hm]
    exact hG.turn_ne_zero i
  | inr v =>
    have hv : v.1 ∈ S := by
      rw [hm] at hc
      exact hc
    rw [turn_visit_of_traced hG.crossingGeometry S hn q htr k v hm hv]
    exact crossingSign_visit_twin_ne_zero hG.crossingGeometry v


/-- CV:def:wind (d1_setup.tex:487–512), one field per printed clause, on the printed binder
`hG : Generic P`, `S ∈ Ind(G_P)`; `hP = hG.crossingGeometry`. Fields quantifying `_hn : 3 ≤ n`
(CV def:polygon's standing `n ≥ 3`) are those whose geo lemmas consume it. -/
structure WindDefinitionData (_hS : S ∈ Ind hG.crossingGeometry) : Prop where
  /-- "A corner of a carrier of `S` is either a vertex `p_i` of `P` traversed by it or a smoothing
  site of `S` traversed by it": the corner list of the carrier `q` consists of the marks it owns that
  are original vertices or visits of selected crossings -/
  corner_iff : ∀ (q : GeoComponent hG.crossingGeometry S) (a : Mark P),
    a ∈ geoComponentCornerList hG.crossingGeometry S q ↔
      geoOwner hG.crossingGeometry S a = q ∧
        ((∃ i : ZMod n, a = Sum.inl i) ∨ ∃ v : Visit P, a = Sum.inr v ∧ v.1 ∈ S)
  /-- `c(L) = #corners`: the corners of `L` are `geoCornerMark L k`, `k : ZMod c(L)`, without
  repetition, `c(L) = geoCornerCount` = the length of the corner list -/
  corner_count : ∀ q : GeoComponent hG.crossingGeometry S,
    geoCornerCount hG.crossingGeometry S q = (geoComponentCornerList hG.crossingGeometry S q).length ∧
    Function.Injective (geoCornerMark hG.crossingGeometry S q) ∧
    ∀ a ∈ geoComponentCornerList hG.crossingGeometry S q, ∃ k, geoCornerMark hG.crossingGeometry S q k = a
  /-- "At each corner the carrier turns left or right according to the sign of the determinant of the
  incoming and outgoing directions": the turn of `L` at its `k`-th corner is
  `sgn det(d_in, d_out)`, `d_in` = the original edge direction carrying the incoming piece,
  `d_out` = that of the outgoing piece (`+1` left, `−1` right) -/
  turn_sign : ∀ (_hn : 3 ≤ n) (q : GeoComponent hG.crossingGeometry S)
    (k : ZMod (geoCornerCount hG.crossingGeometry S q)),
    turn (geoCornerPolygon hG.crossingGeometry S q) k =
      SignType.sign (det (edge P (geoInEdge hG.crossingGeometry (geoCornerMark hG.crossingGeometry S q k)))
        (edge P (geoOutSlot hG.crossingGeometry S (geoCornerMark hG.crossingGeometry S q k)).1))
  /-- "which under genericity is nonzero" -/
  turn_ne_zero : ∀ (_hn : 3 ≤ n) (q : GeoComponent hG.crossingGeometry S)
    (k : ZMod (geoCornerCount hG.crossingGeometry S q)),
    turn (geoCornerPolygon hG.crossingGeometry S q) k ≠ 0
  /-- "at a vertex by (G1), unconditional and hence relevant": at the corner `p_i` the carrier's turn
  is the turn `τ_i` of `P` (incoming `e_{i-1}`, outgoing `e_i`), nonzero by (G1) -/
  vertex_corner : ∀ (_hn : 3 ≤ n) (q : GeoComponent hG.crossingGeometry S)
    (k : ZMod (geoCornerCount hG.crossingGeometry S q)) (i : ZMod n),
    geoCornerMark hG.crossingGeometry S q k = Sum.inl i →
      turn (geoCornerPolygon hG.crossingGeometry S q) k = turn P i ∧ turn P i ≠ 0
  /-- "at a smoothing site by (G5), active at a crossing": at the smoothing site `v` (a selected
  visit) the carrier arrives along the edge `v.2` and leaves along the twin's edge, turning with the
  sign `sgn det(d_{v.2}, d_{twin})`, nonzero since the crossing is transverse -/
  smoothing_corner : ∀ (_hn : 3 ≤ n) (q : GeoComponent hG.crossingGeometry S)
    (k : ZMod (geoCornerCount hG.crossingGeometry S q)) (v : Visit P),
    geoCornerMark hG.crossingGeometry S q k = Sum.inr v → v.1 ∈ S →
      turn (geoCornerPolygon hG.crossingGeometry S q) k = crossingSign P v.2.val (visitTwin v).2.val ∧
      crossingSign P v.2.val (visitTwin v).2.val ≠ 0
  /-- "On a merely diagrammatic polygon the vertex clause is false — `((0,0),(1,0),(2,0),(0,1))` is
  diagrammatic and its turn at `p_2` is exactly zero — which is why the generic binder is part of
  this definition and not decoration" -/
  not_decoration : Diagrammatic flatExample ∧ turn flatExample 1 = 0 ∧ ¬ Generic flatExample
  /-- "A carrier is uniform if all its corners turn the same way": one nonzero sign at every corner -/
  uniform : ∀ q : GeoComponent hG.crossingGeometry S,
    CarrierUniform hG.crossingGeometry S q ↔
      ∃ τ : SignType, τ ≠ 0 ∧ ∀ k, turn (geoCornerPolygon hG.crossingGeometry S q) k = τ
  /-- … literally "all its corners turn the same way" (the turns being nonzero) -/
  uniform_same_way : ∀ (_hn : 3 ≤ n) (q : GeoComponent hG.crossingGeometry S),
    CarrierUniform hG.crossingGeometry S q ↔
      ∀ k k', turn (geoCornerPolygon hG.crossingGeometry S q) k =
        turn (geoCornerPolygon hG.crossingGeometry S q) k'
  /-- "and mixed otherwise" -/
  mixed : ∀ q : GeoComponent hG.crossingGeometry S,
    CarrierMixed hG.crossingGeometry S q ↔ ¬ CarrierUniform hG.crossingGeometry S q
  /-- "`wt(L) = +1`, `L` uniform, all turns right" (`turn = −1`) -/
  weight_right : ∀ q : GeoComponent hG.crossingGeometry S,
    (∀ k, turn (geoCornerPolygon hG.crossingGeometry S q) k = -1) → weight hG.crossingGeometry S q = 1
  /-- "`wt(L) = (−1)^{c(L)}`, `L` uniform, all turns left, `c(L) = #corners`" (`turn = +1`) -/
  weight_left : ∀ q : GeoComponent hG.crossingGeometry S,
    (∀ k, turn (geoCornerPolygon hG.crossingGeometry S q) k = 1) →
      weight hG.crossingGeometry S q = (-1 : ℤ) ^ geoCornerCount hG.crossingGeometry S q
  /-- "`wt(L) = 0`, `L` mixed" -/
  weight_mixed : ∀ q : GeoComponent hG.crossingGeometry S,
    CarrierMixed hG.crossingGeometry S q → weight hG.crossingGeometry S q = 0
  /-- "`wind(S) = ∏_L wt(L)`, the product over the `|S|+1` carriers of `S`" (the carriers form the
  finite type `GeoComponent`; that there are `|S|+1` of them is lem:carriers (i), row 136) -/
  wind_eq : wind hG.crossingGeometry S = ∏ q : GeoComponent hG.crossingGeometry S, weight hG.crossingGeometry S q
  /-- "In particular `wind(S) ≠ 0` forces every carrier of `S` to be uniform: `wind(S)` is a product
  of integers, a product of integers is nonzero only if every factor is, and the weight of a mixed
  carrier is `0`" -/
  wind_ne_zero : wind hG.crossingGeometry S ≠ 0 →
    (∀ q, weight hG.crossingGeometry S q ≠ 0) ∧ ∀ q, CarrierUniform hG.crossingGeometry S q

/-- **Row 138, CV:def:wind, hypothesis form**: the bundle given the inherited order of the carriers
(`TracedSuccessor`, lem:carriers (i) / unit U1b) for `n ≥ 3`; uses only the accepted library. -/
theorem wind_definition_of_traced (hS : S ∈ Ind hG.crossingGeometry)
    (htr : 3 ≤ n → ∀ q : GeoComponent hG.crossingGeometry S, TracedSuccessor hG.crossingGeometry S q) :
    WindDefinitionData hG S hS where
  corner_iff q a := by
    rw [mem_geoComponentCornerList, isTrueCorner_iff]
  corner_count := corners_enumerated hG.crossingGeometry S
  turn_sign hn q k := turn_eq_sign_of_traced hG.crossingGeometry S hn q (htr hn q) k
  turn_ne_zero hn q k := turn_ne_zero_of_traced hG S hn q (htr hn q) k
  vertex_corner hn q k i h :=
    ⟨turn_vertex_of_traced hG.crossingGeometry S hn q (htr hn q) k i h, hG.turn_ne_zero i⟩
  smoothing_corner hn q k v h hv :=
    ⟨turn_visit_of_traced hG.crossingGeometry S hn q (htr hn q) k v h hv,
      crossingSign_visit_twin_ne_zero hG.crossingGeometry v⟩
  not_decoration := ⟨flatExample_diagrammatic, flatExample_turn, flatExample_not_generic⟩
  uniform _ := Iff.rfl
  uniform_same_way hn q :=
    uniform_iff_same_way_of_ne_zero hG.crossingGeometry S q
      (turn_ne_zero_of_traced hG S hn q (htr hn q))
  mixed _ := Iff.rfl
  weight_right := weight_of_all_right hG.crossingGeometry S
  weight_left := weight_of_all_left hG.crossingGeometry S
  weight_mixed := weight_of_mixed hG.crossingGeometry S
  wind_eq := rfl
  wind_ne_zero := wind_ne_zero_imp hG.crossingGeometry S

/-- **Row 138, CV:def:wind**, on the printed binder `hG : Generic P`, `S ∈ Ind(G_P)` (the inherited
order from unit U1b, `tracedSuccessor_of_mem_Ind`). -/
theorem wind_definition (hS : S ∈ Ind hG.crossingGeometry) : WindDefinitionData hG S hS :=
  wind_definition_of_traced hG S hS
    (fun hn q => tracedSuccessor_of_mem_Ind hn hG.crossingGeometry hS q)

end WindGeneric

/-! ## 6. Row 139 — CV:def:pieces (d1_setup.tex:514–520)

Printed text: "For `S ∈ Ind(G_P)` put `U(S) = [m] ∖ (S ∪ N_{G_P}(S))`. The *residual pieces* of `S`
are the connected components `H ∈ π₀(G_P[U(S)])` of the induced subgraph on `U(S)`."

`[m]` = `SM.Crossing P` and `G_P` = `geometricInterlacementGraph hP` (accepted CV:def:interlace,
`CV.interlace_definition`); `U(S)` = the accepted `CV.U hP S`, `N_{G_P}(S)` = `CV.N hP S`. -/

section PiecesDefs

variable (hP : CrossingGeometry P) (S : Finset (Crossing P))

/-- def:pieces: "the induced subgraph on `U(S)`", `G_P[U(S)]` (Mathlib `SimpleGraph.induce`). -/
abbrev residualGraph : SimpleGraph (↑(U hP S) : Set (Crossing P)) :=
  (geometricInterlacementGraph hP).induce (↑(U hP S) : Set (Crossing P))

/-- def:pieces: "the residual pieces of `S` are the connected components `H ∈ π₀(G_P[U(S)])`". -/
abbrev Piece := (residualGraph hP S).ConnectedComponent

noncomputable instance : Fintype (Piece hP S) := Fintype.ofFinite _

/-- The piece of a crossing `c ∈ U(S)`. -/
def pieceOf (c : Crossing P) (hc : c ∈ U hP S) : Piece hP S :=
  (residualGraph hP S).connectedComponentMk ⟨c, hc⟩

/-- The crossings (labels) of a piece: the `c ∈ U(S)` whose piece is `H`. -/
noncomputable def pieceLabels (H : Piece hP S) : Finset (Crossing P) :=
  Finset.univ.filter fun c : Crossing P => ∃ hc : c ∈ U hP S, pieceOf hP S c hc = H

/-- def:piecediagram's `w(H) = |H|` ("every crossing is positive, so its writhe is `w(H) = |H|`"),
recorded here as notation for the later rows. -/
noncomputable def pieceWrithe (H : Piece hP S) : ℤ := (pieceLabels hP S H).card

/-- "the residual pieces assigned to `L` by Lemma lem:carriers (iv)" (def:X1): the pieces both
occurrences of each of whose crossings lie on the carrier `L`. lem:carriers (iv) (row 136) is the
theorem that every piece is assigned to exactly one carrier; it is not a clause of def:pieces. -/
noncomputable def piecesOn (q : GeoComponent hP S) : Finset (Piece hP S) :=
  Finset.univ.filter fun H : Piece hP S =>
    ∀ c ∈ pieceLabels hP S H, ∀ v : Visit P, v.1 = c → geoOwner hP S (Sum.inr v) = q

theorem mem_pieceLabels (H : Piece hP S) (c : Crossing P) :
    c ∈ pieceLabels hP S H ↔ ∃ hc : c ∈ U hP S, pieceOf hP S c hc = H := by
  simp only [pieceLabels, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_piecesOn (q : GeoComponent hP S) (H : Piece hP S) :
    H ∈ piecesOn hP S q ↔
      ∀ c ∈ pieceLabels hP S H, ∀ v : Visit P, v.1 = c → geoOwner hP S (Sum.inr v) = q := by
  simp only [piecesOn, Finset.mem_filter, Finset.mem_univ, true_and]

theorem pieceOf_mem_pieceLabels (c : Crossing P) (hc : c ∈ U hP S) :
    c ∈ pieceLabels hP S (pieceOf hP S c hc) :=
  (mem_pieceLabels hP S _ c).mpr ⟨hc, rfl⟩

theorem pieceLabels_subset (H : Piece hP S) : pieceLabels hP S H ⊆ U hP S := by
  intro c hc
  obtain ⟨hcU, -⟩ := (mem_pieceLabels hP S H c).mp hc
  exact hcU

theorem pieceLabels_nonempty (H : Piece hP S) : (pieceLabels hP S H).Nonempty := by
  obtain ⟨⟨c, hc⟩, hH⟩ := H.exists_rep
  exact ⟨c, (mem_pieceLabels hP S H c).mpr ⟨hc, hH⟩⟩

theorem pieceLabels_disjoint (H H' : Piece hP S) (hne : H ≠ H') :
    Disjoint (pieceLabels hP S H) (pieceLabels hP S H') := by
  rw [Finset.disjoint_left]
  intro c hc hc'
  obtain ⟨hcU, hH⟩ := (mem_pieceLabels hP S H c).mp hc
  obtain ⟨hcU', hH'⟩ := (mem_pieceLabels hP S H' c).mp hc'
  exact hne (hH.symm.trans hH')

theorem pieceLabels_cover (c : Crossing P) (hc : c ∈ U hP S) :
    ∃ H : Piece hP S, c ∈ pieceLabels hP S H :=
  ⟨pieceOf hP S c hc, pieceOf_mem_pieceLabels hP S c hc⟩

/-- The pieces partition `U(S)`: `U(S) = ⋃_H H`. -/
theorem biUnion_pieceLabels : (Finset.univ : Finset (Piece hP S)).biUnion (pieceLabels hP S) = U hP S := by
  ext c
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨H, -, hc⟩
    exact pieceLabels_subset hP S H hc
  · intro hc
    obtain ⟨H, hH⟩ := pieceLabels_cover hP S c hc
    exact ⟨H, Finset.mem_univ H, hH⟩

end PiecesDefs

section Pieces

variable (hD : Diagrammatic P) (S : Finset (Crossing P))

/-- CV:def:pieces (d1_setup.tex:514–520), one field per printed clause, on the printed binder
`hD : Diagrammatic P`, `S ∈ Ind(G_P)`; `hP = hD.crossingGeometry`. -/
structure PiecesDefinitionData (_hS : S ∈ Ind hD.crossingGeometry) : Prop where
  /-- "put `U(S) = [m] ∖ (S ∪ N_{G_P}(S))`": a crossing is undominated iff it is neither in `S` nor
  adjacent to an element of `S` -/
  undominated : ∀ x : Crossing P,
    x ∈ U hD.crossingGeometry S ↔ x ∉ S ∧ x ∉ N hD.crossingGeometry S
  /-- the same, as a set difference on the vertex set `[m] = Crossing P` -/
  undominated_eq : U hD.crossingGeometry S = Finset.univ \ (S ∪ N hD.crossingGeometry S)
  /-- `N_{G_P}(S)` spelled out (CV:def:interlace): adjacent to some element of `S` -/
  neighbors : ∀ x : Crossing P,
    x ∈ N hD.crossingGeometry S ↔ ∃ y ∈ S, GeometricInterlaces hD.crossingGeometry x y
  /-- "the induced subgraph on `U(S)`": `G_P[U(S)]` has vertex set `U(S)` and the adjacency of `G_P` -/
  induced_adj : ∀ x y : (↑(U hD.crossingGeometry S) : Set (Crossing P)),
    (residualGraph hD.crossingGeometry S).Adj x y ↔ GeometricInterlaces hD.crossingGeometry x y
  /-- "the connected components `H ∈ π₀(G_P[U(S)])`": two undominated crossings lie in the same
  residual piece iff they are joined by a path in `G_P[U(S)]` -/
  same_piece_iff : ∀ (x y : Crossing P) (hx : x ∈ U hD.crossingGeometry S) (hy : y ∈ U hD.crossingGeometry S),
    pieceOf hD.crossingGeometry S x hx = pieceOf hD.crossingGeometry S y hy ↔
      (residualGraph hD.crossingGeometry S).Reachable ⟨x, hx⟩ ⟨y, hy⟩
  /-- the labels of a piece `H` are the undominated crossings whose piece is `H` -/
  piece_labels : ∀ (H : Piece hD.crossingGeometry S) (c : Crossing P),
    c ∈ pieceLabels hD.crossingGeometry S H ↔
      ∃ hc : c ∈ U hD.crossingGeometry S, pieceOf hD.crossingGeometry S c hc = H
  /-- the pieces are nonempty subsets of `U(S)` … -/
  pieces_nonempty : ∀ H : Piece hD.crossingGeometry S,
    pieceLabels hD.crossingGeometry S H ⊆ U hD.crossingGeometry S ∧
      (pieceLabels hD.crossingGeometry S H).Nonempty
  /-- … pairwise disjoint … -/
  pieces_disjoint : ∀ H H' : Piece hD.crossingGeometry S, H ≠ H' →
    Disjoint (pieceLabels hD.crossingGeometry S H) (pieceLabels hD.crossingGeometry S H')
  /-- … and they cover `U(S)` (a partition of `U(S)`, `π₀`) -/
  pieces_cover :
    (Finset.univ : Finset (Piece hD.crossingGeometry S)).biUnion (pieceLabels hD.crossingGeometry S) =
      U hD.crossingGeometry S

/-- **Row 139, CV:def:pieces**, on the printed binder `hD : Diagrammatic P`, `S ∈ Ind(G_P)`. -/
theorem pieces_definition (hS : S ∈ Ind hD.crossingGeometry) : PiecesDefinitionData hD S hS where
  undominated := mem_U hD.crossingGeometry S
  undominated_eq := by
    ext x
    rw [mem_U hD.crossingGeometry S x]
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, not_or, true_and]
  neighbors := mem_N hD.crossingGeometry S
  induced_adj _ _ := Iff.rfl
  same_piece_iff _ _ _ _ := SimpleGraph.ConnectedComponent.eq
  piece_labels := mem_pieceLabels hD.crossingGeometry S
  pieces_nonempty H :=
    ⟨pieceLabels_subset hD.crossingGeometry S H, pieceLabels_nonempty hD.crossingGeometry S H⟩
  pieces_disjoint := pieceLabels_disjoint hD.crossingGeometry S
  pieces_cover := biUnion_pieceLabels hD.crossingGeometry S

end Pieces

end CV

/-! ## Axiom check (removed at porting, as in the accepted CV modules) -/

