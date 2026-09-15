# U7a — REPORT (CV:def:smoothing 135, CV:def:wind 138, CV:def:pieces 139 on the accepted geo layer)

Written 2026-09-14 (≈02:50–03:10 UTC / 10:50–11:10pm ET) by the U7a prover subagent (claude-fable-5-1) of the
pod executor, for the CV-DOM decision work/drafts/cvdom/DECISION_FINAL.md (§0 option (C), §2 fidelity + three
readings, §3 rulings R1–R5, §4 review-note template, §5 unit U7a, §6 order of rows). Paths relative to the
package root /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912.
Nothing under work/lean was written.

## 0. Deliverable and status

| item | value |
|---|---|
| file | `work/drafts/cvdom/U7a/CVCarriers.lean` (831 lines incl. ≈100 lines of module docstring, ≈95 lines for the printed counterexample of def:wind and the trailing `#print axioms` block); intended home `work/lean/CV/Carriers.lean` (the def:wind / def:pieces sections may be split into `CV/Wind.lean`, `CV/Pieces.lean` as §5 lists — the file is sectioned for it) |
| imports | `CV.CarrierBridges` (U0: tiers, `mem_Ind_iff_geoIndependent`, `mem_U_iff`), `SM.FlatCarriers` (accepted geo lemmas), `SM.GeoCarrierOrder` (unit U1b, landed in work/lean 2026-09-14 ≈02:59Z with a built olean, sorry-free: `geoTracedSuccessor_of_independent`), `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected` |
| check | `cd work/lean && lake env lean ../drafts/cvdom/U7a/CVCarriers.lean` → **exit 0**, no errors, no warnings |
| sorries | **none**. (The first draft carried one `sorry`, a forward reference to U1b's inherited-order lemma; U1b landed in work/lean while U7a was being checked and the reference was discharged, §4.) |
| row theorems PROVED (standard axioms `[propext, Classical.choice, Quot.sound]`) | `CV.smoothing_definition` (135), `CV.wind_definition` (138; also its hypothesis form `CV.wind_definition_of_traced`), `CV.pieces_definition` (139) |
| tier-2 (U2b) facts used | none — no field of these rows waits for U2b (§3) |
| accepted declarations modified / `geo*` names redefined | none (ruling R3) |
| new names | namespace `CV`: `SmoothingDefinitionData`, `smoothing_definition`; `weight`, `wind`, `CarrierUniform`, `CarrierMixed`, `WindDefinitionData`, `wind_definition_of_traced`, `wind_definition`; `residualGraph`, `Piece`, `pieceOf`, `pieceLabels`, `pieceWrithe`, `piecesOn`, `PiecesDefinitionData`, `pieces_definition`; helpers `tracedSuccessor_of_mem_Ind`, `isTrueCorner_iff`, `det_visit_twin_ne_zero`, `crossingSign_visit_twin_ne_zero`, `geoMarkPosition_evaluation_visit_twin`, `weight_of_all_right/left/mixed`, `weight_ne_zero_iff`, `wind_ne_zero_imp`, `uniform_iff_same_way_of_ne_zero`, `corners_enumerated`, `turn_eq_sign_of_traced`, `turn_vertex_of_traced`, `turn_visit_of_traced`, `turn_ne_zero_of_traced`, `mem_pieceLabels`, `mem_piecesOn`, `pieceOf_mem_pieceLabels`, `pieceLabels_subset/_nonempty/_disjoint/_cover`, `biUnion_pieceLabels`; counterexample `flatExample`, `flatExample_vals/_edges/_turn/_remote_disjoint/_crossingGeometry/_vertex_off/_diagrammatic/_not_generic`, `zmod4_indices`, `zmod4_triple_remote`. (`CV.zmod4_cases`, `CV.remote4_iff` of the accepted CV/Events.lean are reused, not redeclared.) |

`#print axioms` (from the compiled file; the `#print` block at the end of the draft is removed at porting as
in the accepted CV modules):

```
'CV.smoothing_definition' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.pieces_definition' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.wind_definition_of_traced' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.wind_definition' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.tracedSuccessor_of_mem_Ind' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.flatExample_diagrammatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.turn_ne_zero_of_traced' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.weight_ne_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 1. Conventions common to the three rows

* **Binders as printed** (DECISION_FINAL §2 "Fidelity"): `hD : CV.Diagrammatic P` for 135 and 139 (the
  subsection's standing hypothesis, d1_setup.tex:305–309 "Fix a diagrammatic polygon P … Everything in this
  subsection … is stated for that class"), `hG : CV.Generic P` for 138 (d1:488–499 "the generic binder is part
  of this definition and not decoration"); in all three `hS : S ∈ CV.Ind hP` with `hP := hD.crossingGeometry` /
  `hG.crossingGeometry` (ruling R2; accepted CV:def:interlace). `hS` is a parameter of each bundle because it is
  the printed binder ("For S ∈ Ind(G_P)"); no field of 135/139 needs independence (all their clauses are
  definitional on the geometric record domain), and 138's fields need it only through `TracedSuccessor` (§3–4).
* **`hn : 3 ≤ n`** (CV def:polygon "Let n ≥ 3", d1:9) is NOT a parameter of any bundle or row theorem
  (ruling R5). The fields whose accepted geo lemmas consume it quantify it locally, `∀ (_hn : 3 ≤ n), …`
  — the pattern of the accepted `CV.InterlaceData.vertices` (CV/Events.lean). Affected fields: 135
  `oriented_arcs`, `inherited_direction`; 138 `turn_sign`, `turn_ne_zero`, `vertex_corner`,
  `smoothing_corner`, `uniform_same_way`.
* **Objects** are the accepted `SM.GeoCarrier` ones (def:flat-carriers, SM/FlatCarriersDefs.lean) read through
  `hP`: marks `Mark P = ZMod n ⊕ Visit P` at `geoMarkPosition hP`, `ρ = geoMarkSuccessor hP`,
  `ρ_S = geoSmoothingSuccessor hP S = ρ ∘ selectedMarkPerm S`, carriers `GeoComponent hP S`, `geoOwner`,
  `geoComponentMarkList/PlaneCycle`, `geoSmoothingSegment`, corners `geoComponentCornerList`, `geoCornerMark`,
  `geoCornerCount`, `geoCornerPolygon`, `turn`, selector `geoCarrierSelector`; incoming/outgoing original edges
  at a corner mark: `geoInEdge hP a` / `(geoOutSlot hP S a).1` (SM/FlatCarriers.lean §4, accepted module).
  On SM-generic polygons these are def:smoothing's objects (`geoSmoothingSuccessor_eq_generic`,
  `geoComponentEquivGeneric`, `geoComponentCornerList_eq_generic`, FlatCarriersDefs.lean:638–724).
* **Ownership convention** at a selected crossing = SM conv:selected-visits (the same `selectedMarkPerm`: a
  mark keeps its own cycle; the arc arriving at `v` continues along the arc leaving `visitTwin v`), cited in
  the module docstring and in the docstrings of `reconnect_selected` and `carriers` (DECISION_FINAL §4).
* **Sign convention**: SM `turn = sign det(incoming, outgoing)` (`turn_det`); `+1` = left, `−1` = right — the
  same as CV def:rot's `ε_i = +1` case `det(δ_(i−1), δ_i) > 0` (CV/Rotation.lean). So "all turns right" is
  `∀ k, turn … k = -1` and "all turns left" is `∀ k, turn … k = 1`.

## 2. Row 135 — CV:def:smoothing (d1_setup.tex:355–361)

Printed: "For S ∈ Ind(G_P), the oriented smoothing of P along S replaces, at each double point of S, the two
transversally crossing arcs by the two arcs that respect the orientation of P and do not cross. The result is
a disjoint union of closed oriented curves, called the carriers of S."

Binder: `(hD : Diagrammatic P) (S : Finset (Crossing P)) (hS : S ∈ Ind hD.crossingGeometry)`.
Bundle `CV.SmoothingDefinitionData hD S hS`; row theorem `CV.smoothing_definition hD S hS` — **PROVED** from the
accepted library alone.

| printed clause | field | proved from |
|---|---|---|
| "at each double point of S" (the smoothing acts at the two visits `v`, `visitTwin v` of each selected crossing: `ρ_S v = ρ (twin v)`, `ρ_S (twin v) = ρ v`) | `reconnect_selected` | `geoSmoothingSuccessor_visit_of_mem`, `visitTwin_crossing`, `visitTwin_involutive` |
| … and only there (unselected visits, original vertices keep `ρ`) | `keep_unselected`, `keep_vertex` | `geoSmoothingSuccessor_visit_of_not_mem`, `rfl` |
| "the two transversally crossing arcs" (edge pair `{v.2, twin.2}` of the crossing, both visits at the crossing point, `det ≠ 0`) | `transverse` | `visit_crossing_val_eq_pair`, `geoMarkPosition_evaluation_visit`, `crossing_det_ne_zero_of_geometry` (= CV (G5) at an active crossing / `CrossingGeometry` clause 2) |
| "the two arcs that respect the orientation of P" (through `v ∈ S`: in along `edge v.2` positively, out along `edge twin.2` positively) | `oriented_arcs` (`n ≥ 3`) | `geo_visit_incoming_direction`, `geo_selected_visit_outgoing_direction` (FlatCarriers.lean §2–3, tier 0) |
| "and do not cross" | `noncrossing_arcs` | `sign_ne_zero`, `crossingSign_swap` — **reading**: the two new arcs at the site turn with opposite nonzero signs `sgn det(d_v, d_twin)` and `sgn det(d_twin, d_v)`, i.e. bend to opposite sides of the crossing point (the oriented resolution; the original pairing is the one that crosses). The reviewer checks this rendering. |
| "called the carriers of S" (= the cycles of `ρ_S`) | `carriers` | `geoOwner_eq_iff` |
| "closed oriented curves" (each carrier is `ρ_S`-invariant; every carrier is the cycle of one of its marks) | `closed_oriented` | `geoOwner_successor`, `geoOwner_surjective` |
| "a disjoint union" (every mark on exactly one carrier: disjoint mark lists exhausting the marks) | `disjoint_union` | `mem_geoComponentMarkList` |
| the traced curve of a carrier (plane cycle of its marks in inherited order; mark list nodup, nonempty, exactly the owned marks) | `traced_curve` | `rfl`, `geoComponentMarkList_nodup/_length_pos`, `mem_geoComponentMarkList` |
| its sides: the inherited straight pieces, inside the closed original edge of the outgoing slot | `straight_pieces` | `rfl`, `geoSmoothingSegment_mem_edgeSegment` (tier 0, no `hn`) |
| … running in that edge's positive direction | `inherited_direction` (`n ≥ 3`) | `geoSmoothingSegment_positive_direction` |

Not clauses of this row (deliberately absent): corners (def:wind, row 138), retained crossings
`geoCarrierCrossings` (SM def:smoothing only), the inherited cyclic order `TracedSuccessor` (lem:carriers (i),
row 136 / unit U1b), the count `|S|+1` (lem:carriers (i)).

```lean
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

theorem smoothing_definition (hS : S ∈ Ind hD.crossingGeometry) :
    SmoothingDefinitionData hD S hS where
```

## 3. Row 138 — CV:def:wind (d1_setup.tex:487–512)

Binder: `(hG : Generic P) (S : Finset (Crossing P)) (hS : S ∈ Ind hG.crossingGeometry)`.
Definitions on `hP : CrossingGeometry P` (prototype names kept): `CV.weight hP S q := geoCarrierSelector hP S q`
(the accepted `cornerSelector` of the corner polygon), `CV.wind hP S := ∏ q, weight hP S q`,
`CV.CarrierUniform hP S q := ∃ τ ≠ 0, ∀ k, turn (geoCornerPolygon hP S q) k = τ`, `CV.CarrierMixed := ¬ CarrierUniform`.
Bundle `CV.WindDefinitionData hG S hS`. Theorems: `CV.wind_definition_of_traced hG S hS htr` — **PROVED** from the
accepted library alone, with `htr : 3 ≤ n → ∀ q, TracedSuccessor hG.crossingGeometry S q` as an explicit
hypothesis; `CV.wind_definition hG S hS` — **PROVED**, = the former applied to `tracedSuccessor_of_mem_Ind` (U1b's
`geoTracedSuccessor_of_independent` on the CV binder, §4).

| printed clause | field | proved from |
|---|---|---|
| "A corner of a carrier of S is either a vertex p_i of P traversed by it or a smoothing site of S traversed by it" | `corner_iff` | `mem_geoComponentCornerList`, `isTrueCorner_iff` |
| `c(L) = #corners` (corners enumerated without repetition by `geoCornerMark q k`, `k : ZMod c(L)`) | `corner_count` | `geoCornerMark_injective`, `geoCornerMark_exists` |
| "At each corner the carrier turns left or right according to the sign of the determinant of the incoming and outgoing directions" | `turn_sign` (`n ≥ 3`) | `TracedSuccessor` (U1b) + accepted tier-0 `geoCornerPolygon_turn_eq_sign` (FlatCarriers.lean:3326) |
| "which under genericity is nonzero" | `turn_ne_zero` (`n ≥ 3`) | `TracedSuccessor` (U1b); vertex corners by `CV.Generic.turn_ne_zero` (CV (G1)), smoothing corners by `crossing_det_ne_zero_of_geometry` (CV (G5)) — **no U2b fact** |
| "at a vertex by (G1), unconditional and hence relevant" (turn at `p_i` = `τ_i(P)`, nonzero) | `vertex_corner` (`n ≥ 3`) | `TracedSuccessor`, `geoInEdge_vertex`, `geoOutSlot_vertex`, `turn_det`, `hG.turn_ne_zero` |
| "at a smoothing site by (G5), active at a crossing" (turn at `v ∈ S` = `crossingSign P v.2 twin.2`, nonzero) | `smoothing_corner` (`n ≥ 3`) | `TracedSuccessor`, `geoInEdge_visit`, `geoOutSlot_selected`, `crossing_det_ne_zero_of_geometry` |
| "On a merely diagrammatic polygon the vertex clause is false — ((0,0),(1,0),(2,0),(0,1)) is diagrammatic and its turn at p_2 is exactly zero — which is why the generic binder is part of this definition" | `not_decoration` | `CV.flatExample` with `Diagrammatic flatExample ∧ turn flatExample 1 = 0 ∧ ¬ Generic flatExample` (via `diagrammatic_of_crossingGeometry`, `remote4_iff`, `zmod4_cases` of the accepted CV/Events.lean, and `Generic.turn_ne_zero`) |
| "A carrier is uniform if all its corners turn the same way" | `uniform` (SM def:uniform form, `Iff.rfl`), `uniform_same_way` (`n ≥ 3`; literally "all turns equal", needs `turn_ne_zero`) | `Iff.rfl` / `TracedSuccessor` + `uniform_iff_same_way_of_ne_zero` |
| "and mixed otherwise" | `mixed` | `Iff.rfl` |
| `wt(L) = +1` (uniform, all right) | `weight_right` | `cornerSelector_of_all_right` |
| `wt(L) = (−1)^(c(L))` (uniform, all left) | `weight_left` | `cornerSelector_of_all_left` |
| `wt(L) = 0` (mixed) | `weight_mixed` | `cornerSelector_of_mixed` |
| "wind(S) = ∏_L wt(L), the product over the |S|+1 carriers of S" | `wind_eq` | `rfl` (the count `|S|+1` is lem:carriers (i), row 136 — noted in the docstring, not asserted here) |
| "In particular wind(S) ≠ 0 forces every carrier of S to be uniform: … a product of integers is nonzero only if every factor is, and the weight of a mixed carrier is 0" | `wind_ne_zero` | `Finset.prod_eq_zero`, `weight_ne_zero_iff` |

The plan's clause "`weight ≠ 0 ↔ uniform`" (§5 U7a) is the standalone theorem `CV.weight_ne_zero_iff` (not a
printed sentence, hence not a field).

**What the turn clauses rest on (nothing waits).** §5 of the decision expected the last three fields to wait
for U2b (tier-2 corner-polygon turn facts). In fact, given `SM.GeoCarrier.TracedSuccessor hP S q` (the inherited
order, `GeoCarrierSpec.traced_successor`, **U1b**'s `geoTracedSuccessor_of_independent`, now in work/lean), the
accepted tier-0 lemma `geoCornerPolygon_turn_eq_sign` gives `turn = sign det(d_in, d_out)` with `d_in = edge P
(geoInEdge hP a)`, `d_out = edge P (geoOutSlot hP S a).1`, and the two corner kinds evaluate by
`geoInEdge_vertex/_visit`, `geoOutSlot_vertex/_selected` to `det(edge (i−1), edge i)` and
`det(edge v.2, edge twin.2)`, whose nonvanishing is CV's (G1) (`hG.turn_ne_zero`) and (G5)
(`crossing_det_ne_zero_of_geometry`). So **no field of def:wind uses a U2b fact**; five fields (`turn_sign`,
`turn_ne_zero`, `vertex_corner`, `smoothing_corner`, `uniform_same_way`) use U1b's lemma through
`tracedSuccessor_of_mem_Ind`. (`three_le_geoCornerCount` / `geoCornerPolygon_regular` of U2b are not needed by
this row; they are selector_A / def:X1 material.)

```lean
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

theorem wind_definition_of_traced (hS : S ∈ Ind hG.crossingGeometry)
    (htr : 3 ≤ n → ∀ q : GeoComponent hG.crossingGeometry S, TracedSuccessor hG.crossingGeometry S q) :
    WindDefinitionData hG S hS where
  …

theorem wind_definition (hS : S ∈ Ind hG.crossingGeometry) : WindDefinitionData hG S hS :=
  wind_definition_of_traced hG S hS
    (fun hn q => tracedSuccessor_of_mem_Ind hn hG.crossingGeometry hS q)
```

## 4. The inherited order on the CV binder (formerly the forward reference)

```lean
theorem tracedSuccessor_of_mem_Ind (hn : 3 ≤ n) (hP : CrossingGeometry P) {S : Finset (Crossing P)}
    (hS : S ∈ Ind hP) (q : GeoComponent hP S) : TracedSuccessor hP S q :=
  geoTracedSuccessor_of_independent hn hP ((mem_Ind_iff_geoIndependent hP S).mp hS) q
```

`SM.GeoCarrier.TracedSuccessor hP S q` (FlatCarriers.lean:3147, accepted) is
`∀ i : Fin (geoComponentMarkList hP S q).length, ρ_S (L[i]) = L[(i+1) % L.length]`. The first draft of this
unit carried this declaration as a `sorry` forward reference (the U1b deliverable of DECISION_FINAL §5);
unit U1b landed in work/lean (SM/GeoCarrierOrder.lean, olean built, sorry-free) while U7a was being checked,
and the body is now U1b's lemma through U0's `CV.mem_Ind_iff_geoIndependent` (CV/CarrierBridges.lean). The
wrapper is in namespace `CV` under a non-`geo` name (ruling R3); the assembler may inline it.

## 5. Row 139 — CV:def:pieces (d1_setup.tex:514–520)

Printed: "For S ∈ Ind(G_P) put U(S) = [m] ∖ (S ∪ N_(G_P)(S)). The residual pieces of S are the connected
components H ∈ π₀(G_P[U(S)]) of the induced subgraph on U(S)."

Binder: `(hD : Diagrammatic P) (S : Finset (Crossing P)) (hS : S ∈ Ind hD.crossingGeometry)`.
Definitions on `hP : CrossingGeometry P` (prototype names kept, `CV.pieceOf` added):
`CV.residualGraph hP S := (geometricInterlacementGraph hP).induce ↑(U hP S)` (`G_P[U(S)]`),
`CV.Piece hP S := (residualGraph hP S).ConnectedComponent` (with `Fintype`), `CV.pieceOf hP S c hc` (the piece of
`c ∈ U(S)`), `CV.pieceLabels hP S H : Finset (Crossing P)` (the crossings of a piece), and the notation of the later
rows `CV.pieceWrithe` (def:piecediagram's `w(H) = |H|`) and `CV.piecesOn hP S q` (def:X1's "pieces carried by L").
Bundle `CV.PiecesDefinitionData hD S hS`; row theorem `CV.pieces_definition hD S hS` — **PROVED** from the accepted
library alone.

| printed clause | field | proved from |
|---|---|---|
| "put U(S) = [m] ∖ (S ∪ N_(G_P)(S))" | `undominated` (iff form), `undominated_eq` (set difference on `[m] = Crossing P`) | accepted `CV.mem_U`; `Finset.ext` |
| `N_(G_P)(S)` spelled out (CV:def:interlace) | `neighbors` | accepted `CV.mem_N` |
| "the induced subgraph on U(S)" (vertex set `U(S)`, adjacency of `G_P`) | `induced_adj` | `Iff.rfl` (`SimpleGraph.induce_adj`) |
| "the connected components H ∈ π₀(G_P[U(S)])" (same piece ⇔ joined by a path in `G_P[U(S)]`) | `same_piece_iff` | `SimpleGraph.ConnectedComponent.eq` |
| the labels of a piece | `piece_labels` | `Finset.mem_filter` |
| the pieces partition `U(S)`: nonempty subsets … | `pieces_nonempty` | `ConnectedComponent.exists_rep` |
| … pairwise disjoint … | `pieces_disjoint` | `Finset.disjoint_left` (+ proof irrelevance) |
| … covering `U(S)` | `pieces_cover` (`Finset.univ.biUnion pieceLabels = U hP S`) | `biUnion_pieceLabels` |

"Each piece lies on one carrier" is lem:carriers (iv) (row 136, unit U7b, Gap G3) and is deliberately NOT a
clause of this row; `piecesOn` is only the notation it will feed (`CV.mem_piecesOn` unfolds it).

```lean
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

theorem pieces_definition (hS : S ∈ Ind hD.crossingGeometry) : PiecesDefinitionData hD S hS where
```

## 6. Review notes to attach (DECISION_FINAL §4 template, filled)

For each of the three rows: "Stated on the printed binder (`hD : CV.Diagrammatic P` for 135/139, `hG : CV.Generic P`
for 138) and `S ∈ CV.Ind hP`; no domain change (CV-DOM decision, AUTHOR_NOTES 2026-09-14). The carriers, their
marks, corners, corner polygons, turns are the accepted `SM.GeoCarrier` objects (def:flat-carriers,
SM/FlatCarriersDefs.lean) read through `hD.crossingGeometry` / `hG.crossingGeometry`; `Ind(G_P)`, `N`, `U` are the
accepted CV:def:interlace objects. On SM-generic polygons these are the accepted def:smoothing / lem:carriers
objects by `geoSmoothingSuccessor_eq_generic`, `geoComponentEquivGeneric`, `geoComponentCornerList_eq_generic`
(FlatCarriersDefs.lean:638–724) and `CV.Ind_eq_generic`, `CV.U_eq_generic`. The ownership of the two visits of a
selected crossing follows SM conv:selected-visits (the same `selectedMarkPerm`), a disambiguation the CV text
leaves implicit. The reviewer checks: same binder as printed, same quantifiers, each printed sentence = one
bundle field, and that the `geo*` object named in each field is the one the sentence describes."

Row-specific points the reviewer should see:
1. `hn : 3 ≤ n` appears only as a local binder inside the fields whose geo lemmas consume it (§1).
2. 135 `noncrossing_arcs` renders "do not cross" as opposite nonzero turning signs of the two new arcs (§2).
3. 138: the definition's turn clauses are proved from `TracedSuccessor` (U1b, landed), not from U2b (§3);
   `wind_definition_of_traced` isolates that hypothesis. The printed counterexample is fully formalised
   (`not_decoration`).
4. 139: the row is pure definition; lem:carriers (iv) is not a clause.

## 7. Order of rows (DECISION_FINAL §6)

Step 1 ("now: 135, 139 statable and provable today; 138 statement + the clauses that need no tier-2 fact") is
met and exceeded: all three rows are fully stated on their printed binders and fully proved (138 through U1b's
inherited-order lemma, which landed during this unit), with the printed counterexample included. Step 3
("after U2b: 138 complete") is already met; nothing in these three rows waits for U2b.
