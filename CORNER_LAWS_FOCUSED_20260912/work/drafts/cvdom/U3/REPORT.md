# CV-DOM unit U3 — REPORT (2026-09-14, ~03:53 UTC / 11:53pm ET)

Prover: Claude Code subagent (claude-fable-5-1) of the pod executor. Spec: work/drafts/cvdom/DECISION_FINAL.md
§0, §3 (rulings R1–R5) and §5 row **U3**. Nothing under work/lean was written. Paths relative to the package root
/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912.

## Deliverable

| file | intended home | lines | status |
|---|---|---:|---|
| `work/drafts/cvdom/U3/GeoCarriersLemma.lean` | `work/lean/SM/GeoCarriersLemma.lean` (new library module, namespace `SM.GeoCarrier`, `open Carrier`, CV-free; imports `SM.GeoCornerPolygon` (U2b), `SM.GeoCarrierSelfIntersections` (U2c), `SM.GeoCarrierNoncrossing` (U2a), `SM.CX1`; picked up by the lakefile glob `SM.+`) | 791 | `cd work/lean && lake env lean ../drafts/cvdom/U3/GeoCarriersLemma.lean` → **exit 0, no output (no warnings), no `sorry`** (grep count 0); ~7 s |

48 declarations (4 `structure`, 9 `def`, 35 `theorem`). `#print axioms` on every one of them (copy with the 48 lines
appended, /tmp/U3_axioms.lean): `[propext, Classical.choice, Quot.sound]` only (standard), 48/48, 0 non-standard.

Name safety (ruling R3): each of the 48 names grepped against every declaration head under work/lean (excluding
`.lake`): zero hits. No accepted or ported `geo*` name is re-declared (`geoCarrierSelector`, `cornerSelector`,
`geoCarrierCrossingCount` (U2a), `geoComponentCycle`, `GeoInheritsMarkOrder`, `geoSupportNeighbors/Unselected`,
`GeoIsSelfIntersection`, `GeoIsTriplePoint`, `geoComponentTraceEdge`, `markTurn` are referenced, not redefined).
The one accepted lemma restated here under a *different* name is `geoIndependent_iff_isDecomposition`
(SM/FlatCarriers.lean:164) → `geoIndependent_iff_mem_independentSupports` (one-line alias on `independentSupports`).
Deliberately avoided: the accepted names `geoCornerCount_eq_generic` / `geoCornerPolygon_eq_generic` (SM/CS3.lean §B,
namespace `SM`) — the corner-count agreement here is `geoCornerCount_eq_ccp`, so that a file opening both `SM` and
`SM.GeoCarrier` (as SM/CS3.lean itself does) sees no ambiguity.

Tier hygiene: no `Generic P`, `hP.2`, `independentSupports` or `IsDecomposition` outside §6 (the agreement section,
which is ABOUT SM-generic polygons); `hP.1` does not occur.

**Mechanical shape check** (python, /tmp/u3_shape2.py; docstrings and comments stripped, whitespace normalised,
both bodies split at `∧`): the body of the accepted `CarriersLemmaData` (SM/CarriersLemma.lean:42–122) under the
renaming `Component/componentCycle/markCycle/owner/InheritsMarkOrder/smoothingSegment/ccpCornerCount/ccpCornerPolygon/
ccpCornerMark/IsSelfIntersection/IsTriplePoint/carrierCrossings/supportNeighbors/supportUnselected hn hP (S) ↦
GeoComponent/geoComponentCycle/geoMarkCycle/geoOwner/GeoInheritsMarkOrder/geoSmoothingSegment/geoCornerCount/
geoCornerPolygon/geoCornerMark/GeoIsSelfIntersection/GeoIsTriplePoint/geoCarrierCrossings/geoSupportNeighbors/
geoSupportUnselected hG.cg (S)`, `markPosition hn hP.1 ↦ geoMarkPosition hG.cg`, `visitPosition hn hP.1 ↦
geometricVisitPosition hG.cg`, index `j ↦ k` is **40 conjunct chunks; `GeoCarriersLemmaData` is 39; the single
difference is the removed chunk `(∀ (q) (k), turn (geoCornerPolygon hG.cg S q) k ≠ 0)`** = `GeoCornerTurnsData.turn_ne_zero`.
The accepted `SmoothingData` (SM/SmoothingDefinition.lean:39–150) under the analogous renaming
(`componentPlaneCycle/componentMarkList/componentCornerCycle/componentTraceEdge/smoothingSuccessor/markSuccessor/
carrierCrossingCount ↦ geo*`, on `hP`) and `GeoSmoothingData` are **identical (30 chunks each)**.

## §5 U3 targets — status (all proved)

| §5 target | draft decl | tier | status |
|---|---|:-:|---|
| `structure GeoCarriersLemmaData (hn) (hG : CarrierGeometry P) (S) (hS : GeoIndependent hG.cg S) : Prop` with the fields of `CarriersLemmaData` on `geo*` | `GeoCarriersLemmaData` (9 fields: `count`, `component_cycle`, `inherited_order`, `selected_visits_separated`, `corner_polygons` (7 clauses), `self_intersections`, `neighbor_visits_separated`, `nonneighbor_visits_together`, `noncrossing`) | 1 | **stated as specified**; shape-checked against the accepted bundle (above) |
| turn ≠ 0 field "under an extra `hW : WeakGeneric P` or in a separate `GeoCornerTurnsData hW`" (ruling R4) | `GeoCornerTurnsData (hn) (hW : WeakGeneric P) (S) (hS : GeoIndependent (weak_crossingGeometry hW) S)` with `turn_ne_zero` (polygon index) and `cornerTurn_ne_zero` (accepted `geoCornerTurn`) | 2 | **separate structure**, as R4 prefers |
| `theorem geo_carriers_lemma : GeoCarriersLemmaData …` | `geo_carriers_lemma (hn) (hG) {S} (hS) : GeoCarriersLemmaData hn hG S hS` | 1 | **proved** from U1a/U1b/U2a/U2b/U2c (table below); plus `geo_corner_turns (hn) (hW) (hS) : GeoCornerTurnsData …` (U2b) and `geo_carriers_lemma_of_weak (hn) (hW) (hS) : GeoCarriersLemmaData hn hW.carrierGeometry S hS ∧ GeoCornerTurnsData hn hW S hS` (both bundles at tier 2; proof irrelevance identifies `hW.carrierGeometry.cg` with `weak_crossingGeometry hW`) |
| `GeoSmoothingData` mirror of SmoothingDefinition.lean:39–150 | `GeoSmoothingData (hP : CrossingGeometry P) (S) : Prop`, 17 fields; `geo_smoothing_data (hn) (hP) (hS) : GeoSmoothingData hP S`; `GeoSmoothingDefinitionData` / `geo_smoothing_definition` (mirror of lines 182–187) | **0** | **proved** at tier 0 (def:smoothing needs no genericity: the accepted geo layer + U1b + U2a; transversality at a smoothing corner is `CrossingGeometry` clause 2) |
| `def geoCarrierUniform (hP) (S) (q) : Prop := ∃ τ : SignType, τ ≠ 0 ∧ ∀ k, turn (geoCornerPolygon hP S q) k = τ` | `geoCarrierUniform` (exactly this body, the accepted `CarrierUniform` form; `CV.CarrierUniform` of U7a has the same body, so the CV↔SM identification is `Iff.rfl`) | 0 | **defined** |
| `geoCarrierMixed`, `geoUniformSupport` | `geoCarrierMixed := ¬ geoCarrierUniform`, `geoUniformSupport hP S := ∀ q, geoCarrierUniform hP S q` (port of `UniformDecomposition`; "support" because "decomposition" is `SM.Generic`-bound, R2) | 0 | **defined** |
| `geoCarrierRotation := rotationNumber (geoCornerPolygon …)`, `geoCarrierRotationInt` (integer, `rotationNumber_integer` on the regular polygon) | `geoCarrierRotation`, `geoCarrierLeftTurns := leftTurns (geoCornerPolygon …)`, `geoCarrierRotationInt := round (geoCarrierRotation …)` (SM/CornerStateSum.lean:61 shape); `geoCarrierRotation_exists_int (hn) (hG) (hS) (q) : ∃ k : ℤ, geoCarrierRotation hG.cg S q = k`, `geoCarrierRotationInt_cast (hn) (hG) (hS) (q) : ((geoCarrierRotationInt hG.cg S q : ℤ) : ℝ) = geoCarrierRotation hG.cg S q` | 0 (defs) / **1** (integrality, via U2b's `geoCornerPolygon_regular`) | **proved** |
| def:uniform bundle (mirror of `UniformDefinitionData`) | `GeoUniformDefinitionData` (7 fields: `uniform`, `mixed`, `uniform_support`, `regular_carrier` [tier 1: `3 ≤ geoCornerCount ∧ Regular`], `rotation`, `crossings` (`geoCarrierCrossingCount = card`), `left_turns`), `geo_uniform_definition` | 0/1 | **proved** (`Iff.rfl`/`rfl` except `regular_carrier` = U2b's `three_le_geoCornerCount` + `geoCornerPolygon_regular`) |
| `geoCarrierSelector_ne_zero_iff_uniform` | `geoCarrierSelector_ne_zero_iff_uniform (hP) (S) (q) : geoCarrierSelector hP S q ≠ 0 ↔ geoCarrierUniform hP S q` | 0 | **proved** (via `cornerSelector_of_all_right/_all_left/_mixed`, SM/FlatCarriers.lean:4856–4880) |
| `geoWind hP S := ∏ q, geoCarrierSelector hP S q` | `geoCarrierWeight hP S q := geoCarrierSelector hP S q` (port of `carrierWeight`; `geoCarrierWeight_eq_selector : rfl`), `geoWind hP S := ∏ q, geoCarrierWeight hP S q`, `geoWind_eq_prod_selector : geoWind hP S = ∏ q, geoCarrierSelector hP S q := rfl` | 0 | **defined** |
| `geoWind_ne_zero_iff` | `geoWind_ne_zero_iff (hP) (S) : geoWind hP S ≠ 0 ↔ geoUniformSupport hP S`; also `geoWind_eq_zero_of_not_uniform`, `geoWind_eq_pow_of_uniform : geoWind hP S = (-1) ^ ∑ q, geoCarrierLeftTurns hP S q` | 0 | **proved** |
| agreement lemmas with the accepted lane on SM-generic polygons "where the §4b lemmas make them one-liners" | §6 (below) | — | **9 proved**; 3 deferred to U6 with reason (below) |

Nothing left unproved in the spec; no obstacle; no tier deviation from R4 (the corner-polygon geometry is consumed at
tier 1, only the nonzero-turn clause at tier 2).

## Mirror table — accepted field → geo field → source unit / lemma (tier)

### `CarriersLemmaData` (SM/CarriersLemma.lean:42–122, lem:carriers) → `GeoCarriersLemmaData` (tier 1) + `GeoCornerTurnsData` (tier 2)

| accepted field (clause) | geo field | proof term | source unit (tier) |
|---|---|---|---|
| `count : card (Component) = |S|+1` (i) | `count : Fintype.card (GeoComponent hG.cg S) = S.card + 1` | `geoComponent_card hn hG.cg hS` | U1a GeoCarrierCount:1720 (0) |
| `component_cycle : componentCycle q = (markCycle).filter (owner = q)` (i) | `component_cycle` on `geoComponentCycle`/`geoMarkCycle`/`geoOwner` | `geoComponentCycle_eq_filter hG.cg S q` (`rfl`) | U1b GeoCarrierOrder:51 (0) |
| `inherited_order : InheritsMarkOrder` (i) | `inherited_order : GeoInheritsMarkOrder hG.cg S` | `geoInheritsMarkOrder_of_independent hG.cg hS` | U1a :1734 (0) |
| `selected_visits_separated` (i) | same on `geoOwner` | `geo_selected_visits_separated hG.cg hS v hv` | U1a :1727 (0) |
| `corner_polygons` clause 1: trace `⋃ owned segments = ⋃ edgeSegment (ccpCornerPolygon)` (ii) | clause 1 on `geoSmoothingSegment`/`geoCornerPolygon` (accepted side order kept) | `(geoCornerPolygon_trace hn hG.cg hS q).symm` | U2b GeoCornerPolygon:749 (0) |
| clause 2: `edge ≠ 0 ∧ ∃ c e, 0 < c ∧ edge = c • edge P e` | clause 2 | `geoCornerPolygon_edge_ne_zero_of_independent`, `geoCornerPolygon_edge_smul` (witness `e := (geoOutSlot …).1`) | U2b :424, :400 (0) |
| clause 3: `3 ≤ ccpCornerCount` | clause 3 | `three_le_geoCornerCount hn hG hS q` | U2b :646 (**1**) |
| clause 4: no antiparallel consecutive edges | clause 4 | `geoCornerPolygon_not_antiparallel hn hG hS q k` | U2b :604 (**1**) |
| clause 5: `Regular (ccpCornerPolygon)` | clause 5 | `geoCornerPolygon_regular hn hG hS q` | U2b :633 (**1**) |
| clause 6: `turn ≠ 0` | **`GeoCornerTurnsData.turn_ne_zero`** (+ `cornerTurn_ne_zero` on `geoCornerTurn`) | `geoCornerPolygon_turn_ne_zero hn hW hS q k`, `geoCornerTurn_ne_zero hn hW hS a` | U2b :580, :590 (**2**, ruling R4) |
| clause 7: vertex corner turn `= turn P i` | clause 6 | `geoCornerPolygon_turn_vertex hn hG.cg hS q k i h` | U2b :444 (0) |
| clause 8: the two smoothing corners of a selected crossing: owners differ, turns `crossingSign P i j` / `crossingSign P j i`, `turn' = -turn`, `(1,-1) ∨ (-1,1)` | clause 7 | `geoCornerPolygon_turn_visit_twin hn hG.cg hS v hv` | U2b :486 (0) |
| `self_intersections` (iii): self-intersections = crossing points of `carrierCrossings`; transverse (four conjuncts); not at vertices, not at selected crossing points, not at true corners, no true corner's point; no triple point | same on `GeoIsSelfIntersection`/`GeoIsTriplePoint`/`geoCarrierCrossings`/`geoSmoothingSegment`/`geoMarkPosition` | `geo_self_intersections hn hG hS q` | U2c GeoCarrierSelfIntersections:763 (**1**) |
| `neighbor_visits_separated` (iii) | same on `geoSupportNeighbors` | `geo_neighbor_visits_separated hn hG.cg hS` | U2a GeoCarrierCrossings:654 (0) |
| `nonneighbor_visits_together` (iii) | same on `geoSupportUnselected` | `geo_nonneighbor_visits_together hn hG.cg hS` | U2a :672 (0) |
| `noncrossing` (iv) | same on `geometricVisitPosition hG.cg` | `geo_noncrossing hn hG.cg hS` | U2a GeoCarrierNoncrossing:398 (0) |

### `SmoothingData` (SM/SmoothingDefinition.lean:39–150, def:smoothing) → `GeoSmoothingData` (tier 0)

| accepted field | geo field (same name) | proof term | source (tier) |
|---|---|---|---|
| `reconnection : ρ_S a = ρ (selectedMarkPerm S a)` | on `geoSmoothingSuccessor`/`geoMarkSuccessor` | `geoSmoothingSuccessor_apply hP S a` | accepted FlatCarriersDefs:239 (0) |
| `carriers : owner a = owner b ↔ SameCycle` | on `geoOwner` | `geoOwner_eq_iff hP S a b` | accepted :266 (0) |
| `traced_curve` | on `geoComponentPlaneCycle`/`geoComponentMarkList`/`geoMarkPosition` | `rfl` | accepted :310 (0) |
| `corners : componentCornerCycle = (componentCycle).filter IsTrueCorner` | on `geoComponentCornerCycle`/`geoComponentCycle` | `rfl` | U1a :1685 (0) |
| `corner_vertex`, `corner_visit` | same | `isTrueCorner_vertex S i`, `isTrueCorner_visit S v` | accepted (hypothesis-free) |
| `vertex_corner` (arrives along `ℓ_{i-1}`, leaves along `ℓ_i`; 7 conjuncts) | same on geo objects | `geo_vertex_corner_directions hn hP S q i hq` | U2a :268 (0) |
| `smoothing_corner` (arrives along `ℓ_i`, leaves along `ℓ_j`; 8 conjuncts) | same | `geo_smoothing_corner_directions hn hP S q v hv hq` | U2a :229 (0) |
| `traced_marks` (Nodup, nonempty, `= componentCycle`, membership = ownership) | same | `geoComponentMarkList_data hP S q` | U1b :122 (0) |
| `traced_successor` (consecutive entries are `ρ_S`-successors, cyclically) | same (explicit modular index, no `let`) | `geoTracedSuccessor_of_independent hn hP hS q i` | U1b :154 (0) |
| `traced_sides` (edge = segment, positive length, closing, continuous) | same on `geoComponentTraceEdge` | `geoComponentTraceEdge_data hn hP hS q i` | U1b :186 (0) |
| `unselected_visit_straight` (incoming on `E_{v.2}`; incoming/outgoing displacements positive multiples of `ℓ_{v.2}`) | same | `geo_visit_incoming_mem_edgeSegment hn hP S v` (U2a :185), `geo_visit_incoming_direction hn hP S v`, `geo_unselected_visit_outgoing_direction hn hP S v hv` (accepted FlatCarriers:2943, 2965) | (0) |
| `smoothing_corner_transverse : det (edge P v.2) (edge P (twin v).2) ≠ 0` | same | `crossing_det_ne_zero_of_geometry hP hc` with `hc` from `v.1.property` + `visit_crossing_val_eq_pair` (the source used `crossing_edgeParameter_det_ne_zero hn hP.1`, G1 site SmoothingDefinition:173) | accepted GeometricParameters:11 = `CrossingGeometry` clause 2 (0) |
| `crossings_of : x ∈ carrierCrossings q ↔ x ∉ S ∧ ∀ v, v.1 = x → owner (inr v) = q` | same on `geoCarrierCrossings` | `mem_geoCarrierCrossings hP S q x` | U2a :91 (0) |
| `crossing_count : carrierCrossingCount = card` | same on `geoCarrierCrossingCount` | `geoCarrierCrossingCount_eq_card hP S q` | U2a :136 (0) |
| `neighbor_visits` | same on `geoSupportNeighbors` | `geo_neighbor_visit_owners_ne hP hS hx v hv` | U2a :531 (0) |
| `neighbor_no_carrier` | same | `geo_neighbor_not_mem_geoCarrierCrossings hP hS hx q` | U2a :643 (0) |
| `SmoothingDefinitionData` (∀ k [NeZero k] (hk) P (hP : Generic P) S, IsDecomposition → SmoothingData), `smoothing_definition` | `GeoSmoothingDefinitionData` (∀ k [NeZero k] (_ : 3 ≤ k) P (hP : CrossingGeometry P) S, GeoIndependent hP S → GeoSmoothingData hP S), `geo_smoothing_definition` | `geo_smoothing_data hk hP hS` | (0) |

Binder difference from the source: `GeoSmoothingData (hP) (S)` takes no `hn` (no field mentions it); the theorem
`geo_smoothing_data (hn) (hP) (hS)` does (U2a's direction lemmas and U1b's `geoComponentTraceEdge_data` take it; R5).

### `UniformDefinition.lean` (def:uniform) → §3 (tier 0; `regular_carrier` tier 1)

| accepted | geo | note |
|---|---|---|
| `CarrierUniform (hn) (hP : Generic) (S) (q)` | `geoCarrierUniform (hP : CrossingGeometry P) (S) (q)` | same body |
| `CarrierMixed` | `geoCarrierMixed` | |
| `UniformDecomposition` | `geoUniformSupport` | renamed (R2) |
| `carrierRotation := rotationNumber (ccpCornerPolygon …)` | `geoCarrierRotation := rotationNumber (geoCornerPolygon …)` | |
| `carrierLeftTurns := leftTurns (ccpCornerPolygon …)` | `geoCarrierLeftTurns` | |
| `UniformDefinitionData.{uniform, mixed, uniform_decomposition, regular_carrier, rotation, crossings, left_turns}`, `uniform_definition` | `GeoUniformDefinitionData.{uniform, mixed, uniform_support, regular_carrier, rotation, crossings, left_turns}`, `geo_uniform_definition` | `regular_carrier` quantifies `(_hn : 3 ≤ n) (hG : CarrierGeometry P)`, `GeoIndependent hG.cg S →` (tier 1; the source's `IsDecomposition hn hP S →`); the geo objects do not take `hn`, so it is unreferenced in the type (named `_hn`, the U7a pattern) but consumed by the proof |
| SM/CornerStateSum.lean:61–77 `carrierRotationInt`, `carrierRotation_exists_int (hS : IsDecomposition)`, `carrierRotationInt_cast` | `geoCarrierRotationInt`, `geoCarrierRotation_exists_int (hn) (hG) (hS)`, `geoCarrierRotationInt_cast (hn) (hG) (hS)` | tier 1 via `geoCornerPolygon_regular` |

### `CX1.lean` (lem:C-X1's `carrierWeight`, `wind`, helpers) → §4–§5 (tier 0)

| accepted | geo | note |
|---|---|---|
| `carrierWeight := if ∀ j, turn = -1 then 1 else if ∀ j, turn = 1 then (-1)^ccpCornerCount else 0` | `geoCarrierWeight := geoCarrierSelector hP S q` (= `cornerSelector (geoCornerPolygon …)`, the same `ite` on the geo polygon, accepted FlatCarriersDefs:466–474) | the accepted geo object IS the weight; `geoCarrierWeight_eq_selector : rfl` |
| `wind := ∏ q, carrierWeight` | `geoWind := ∏ q, geoCarrierWeight`; `geoWind_eq_prod_selector : rfl` | |
| `CX1Data.weight_right/_left/_mixed/wind_eq` | `geoCarrierWeight_of_all_right/_of_all_left/_of_mixed`, `geoWind_eq_prod_selector` | as theorems (not a bundle: lem:C-X1 is an SM row, not a CV row) |
| `turn_ccpCornerPolygon_eq_markTurn (hS : S ∈ independentSupports)` | `turn_geoCornerPolygon_eq_markTurn (hn) (hP) (hS : GeoIndependent) (q) (k)`; also `geoCornerTurn_eq_markTurn (hn) (hP) (hS) (ha : IsTrueCorner S a)` | from U2b's `geoCornerPolygon_turn_vertex/_visit` |
| `carrierWeight_eq_of_uniform`, `carrierWeight_eq_zero_of_not_uniform`, `wind_eq_zero_of_not_uniform`, `wind_eq_pow_of_uniform` | `geoCarrierWeight_eq_of_uniform`, `geoCarrierWeight_eq_zero_of_not_uniform`, `geoWind_eq_zero_of_not_uniform`, `geoWind_eq_pow_of_uniform` | verbatim proofs |
| (new) | `geoCarrierWeight_ne_zero_iff`, `geoCarrierSelector_ne_zero_iff_uniform`, `geoWind_ne_zero_iff` (§5 targets); `forall_turn_geoCornerPolygon_iff`, `geoCarrierUniform_iff_corners` ("uniform" read on the true corners owned by `q`) | |

### §6 Agreement on SM-generic polygons (`hn : 3 ≤ n`, `hP : Generic P`; `hc := generic_crossingGeometry hn hP`, `e := geoComponentEquivGeneric hn hP S`)

| geo notion | agreement lemma | proof route |
|---|---|---|
| `GeoIndependent hc S` | `geoIndependent_iff_mem_independentSupports : … ↔ S ∈ independentSupports hn hP` | accepted `geoIndependent_iff_isDecomposition` |
| `geoSupportNeighbors hc S`, `geoSupportUnselected hc S` | `geoSupportNeighbors_eq_generic = supportNeighbors hn hP S`, `geoSupportUnselected_eq_generic = supportUnselected hn hP S` | `ext`; `GeometricInterlaces hc = Interlaces hn hP` definitionally (`geometricInterlaces_iff_generic`) |
| `geoOwner hc S a = q` | `geoOwner_eq_iff_generic : … ↔ owner hn hP S a = e q` | `geoComponentEquivGeneric_owner` + injectivity |
| `geoCornerCount hc S q` | `geoCornerCount_eq_ccp : … = ccpCornerCount hn hP S (e q)` | `geoComponentCornerList_eq_generic` (same fact as the accepted `SM.geoCornerCount_eq_generic`, SM/CS3.lean:1393, which lives in a row module — see below) |
| turns | `forall_turn_ccpCornerPolygon_iff` (accepted side, via CX1's `turn_ccpCornerPolygon_eq_markTurn`), `forall_turn_eq_generic (hS : S ∈ independentSupports hn hP) (q) (τ) : (∀ k, turn (geoCornerPolygon hc S q) k = τ) ↔ ∀ j, turn (ccpCornerPolygon hn hP S (e q)) j = τ` | both sides are "`markTurn` of every true corner owned by the carrier" (`generic_geoCornerTurn_vertex/_visit` enter through U2b's tier-0 turn lemmas) |
| `geoCarrierUniform`, `geoCarrierMixed`, `geoUniformSupport` | `geoCarrierUniform_iff_generic (hS) (q) : … ↔ CarrierUniform hn hP S (e q)`, `geoCarrierMixed_iff_generic`, `geoUniformSupport_iff_generic (hS) : … ↔ UniformDecomposition hn hP S` | one-liners on `forall_turn_eq_generic` |
| `geoCarrierWeight`, `geoWind` | `geoCarrierWeight_eq_generic (hS) (q) : geoCarrierWeight hc S q = carrierWeight hn hP S (e q)`, `geoWind_eq_generic (hS) : geoWind hc S = wind hn hP S` | three cases of the `ite`s via `forall_turn_eq_generic` at `τ = -1, 1` and `geoCornerCount_eq_ccp`; `Fintype.prod_equiv e` |

**Not mirrored here (with reason).**
1. `geoCarrierRotation_eq_generic`, `geoCarrierLeftTurns_eq_generic`, `geoCarrierRotationInt_eq_generic` (and the
   corner polygon itself, `geoCornerPolygon hc S q = recastTuple … (ccpCornerPolygon …)`): these need the polygon
   re-indexed along the equal corner counts, i.e. `recastTuple` / `rotationNumber_recastTuple` / `forall_turn_recastTuple`
   (SM/CChamber.lean:76–110, the prop:C-chamber row module) — not a §4b one-liner, and a library module should not
   import a row module (the rule U2b applied to CSilent.lean). **They are already accepted in SM/CS3.lean §B
   "GenericIdentification" (namespace `SM`, `variable (hn) (hP) (S)`): `geoCornerCount_eq_generic` (1393),
   `geoCornerPolygon_eq_generic` (1400), `cornerSelector_recastTuple` (1448), `carrierWeight_eq_geoCarrierSelector`
   (1459), `wind_eq_prod_geoCarrierSelector` (1465), `carrierCrossings_eq_geo` (1472), `positiveLift_eq_geo`.** U6
   (SM/GeoCarrierAgreement.lean) should re-export/consume those rather than re-prove them; DECISION_FINAL §5's U6 row
   lists them as work to do, which is no longer the case. `rotationNumber (geoCornerPolygon hc S q) = carrierRotation hn hP S (e q)`
   is then `by rw [geoCornerPolygon_eq_generic, rotationNumber_recastTuple]` in a module that may import SM.CS3.
2. Consequently `geoCarrierWeight_eq_generic` / `geoWind_eq_generic` here re-derive (through the corner marks, without
   the row module) the equalities CS3.lean:1459/1465 prove through the recast polygon. They are kept because they make
   this module's def:uniform/def:wind story self-contained for CV/Wind (U7a's `CV.weight`/`CV.wind` are
   `geoCarrierSelector`/`∏ geoCarrierSelector`, so `CV.wind hc S = geoWind hc S` is `rfl`); if the assembler prefers a
   single proof, replace their bodies by the CS3 lemmas in a module that imports SM.CS3.
3. SM/CX1.lean's left-corner count `Σ_L ℓ_L = ℓ(P) + |S|` (`carrierLeftTurns_eq_card_marks` … `sum_carrierLeftTurns`,
   lines 146–236) and `selector_form` (`C(P) = Σ wind ∏ c(L)`): they are the body of lem:C-X1 (an SM row about
   `cornerStateSum`), not of lem:carriers / def:smoothing / def:uniform / def:wind; not asked, not needed by U4–U7.
4. `GeoCarriersLemmaData` keeps the §5-prescribed parameter `hS : GeoIndependent hG.cg S` although no field mentions it
   (the accepted `CarriersLemmaData` has no such parameter); Lean emits no warning for an unused structure parameter.
   Drop it if the assembler prefers the accepted shape (`geo_carriers_lemma` then returns `GeoCarriersLemmaData hn hG S`).

## Method

1. Read DECISION_FINAL §0/§3/§5, the accepted SM/CarriersLemma.lean, SM/SmoothingDefinition.lean, SM/UniformDefinition.lean,
   SM/CX1.lean, SM/CornerStateSum.lean:50–80, the U0–U2c REPORTs and the declaration lists of the seven landed geo modules,
   the exact statements of every consumed lemma, SM/FlatCarriersDefs.lean §3–§5 (definitions, agreement lemmas,
   `GeoCarrierSpec`), SM/FlatCarriers.lean §7 (`generic_geoCornerTurn_*`), §TurnBookkeeping, §SelectorClauses,
   SM/CS3.lean §B and SM/CChamber.lean §0 (to decide the import question above), and U7a's CV/Carriers.lean (weight proofs).
2. Wrote the bundles by transcribing the accepted structures under the port renaming; wrote the proofs as the accepted
   `carriers_lemma` / `smoothing_data` / `uniform_definition` / CX1 do, with the ported names.
3. Compile rounds: round 1 exit 0 with one `unusedVariables` warning (`hn` in `regular_carrier` → `_hn`) and five
   deprecation warnings (`if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`); round 2 exit 0, no output. Then `#print axioms`
   (48/48 standard), name grep (0 collisions), tier grep, and the mechanical shape diff against the two accepted bundles.

## Notes for the assembler and downstream units (U4, U5a, U6, U7b/c)

- **Import graph.** `SM.GeoCarriersLemma` imports `SM.GeoCornerPolygon` (→ GeoCarrierOrder → GeoCarrierCount → FlatCarriers;
  → GeoCarrierGeometry), `SM.GeoCarrierSelfIntersections` (→ GeoCarrierCrossings), `SM.GeoCarrierNoncrossing`, and
  `SM.CX1` (→ CornerStateSum → PositiveLiftDefinition, UniformDefinition, DecompositionDefinition, LinkInterfaces; all
  Carrier-lane row modules already reachable from FlatCarriersDefs' imports of CarriersLemma/UniformDefinition/
  SmoothingDefinition — same layering direction). It does NOT import SM.CChamber, SM.CS3, SM.CSilent or anything CV.
- **For U4 (`geoCarrierPolyComp`, `geoPositiveLift`):** `GeoUniformDefinitionData.regular_carrier` / `geo_carriers_lemma … |>.corner_polygons`
  give `3 ≤ geoCornerCount hG.cg S q ∧ Regular (geoCornerPolygon hG.cg S q)` at tier 1; `geoCarrierRotationInt_cast hn hG hS q`
  is the integer-rotation input of the corner coefficient `d_Q`.
- **For U5a (rotation constant along a family):** `geoCarrierRotation hP S q = rotationNumber (geoCornerPolygon hP S q)` by
  `rfl`; `geoCarrierRotation_exists_int` at tier 1.
- **For U6 (agreement, B4):** use SM/CS3.lean §B (see "Not mirrored" 1) for the recast polygon; the CV def:wind objects are
  `CV.weight hP S q = geoCarrierWeight hP S q` and `CV.wind hP S = geoWind hP S` (both `rfl`), so `CV.wind hc S = SM.wind hn hP S`
  is `geoWind_eq_generic hn hP hS` (with `hS : S ∈ independentSupports hn hP`, i.e. `(CV.Ind_eq_generic …) ▸` on the CV binder).
- **For U7b/c:** `geo_carriers_lemma hn (CarrierGeometry.ofDiagrammatic hD) hS` is CV lem:carriers' whole content on the printed
  binder (`hS` from `CV.mem_Ind_iff_geoIndependent`); `geo_smoothing_data` likewise for def:smoothing's remaining sentences.
- **Call shapes:** `geo_carriers_lemma hn hG hS`, `geo_corner_turns hn hW hS`, `geo_smoothing_data hn hP hS` take `hS` implicitly
  in `S`; the def:uniform/def:wind definitions take `(hP) (S) (q)` explicitly (no `hn`); §6 lemmas take
  `(hn) (hP : Generic P)` explicitly, `S` implicit where `hS : S ∈ independentSupports hn hP` is present.
- **Time.** ≈ 1.6 h including reading the decision, the four accepted sources, the seven landed units' interfaces and
  reports, the CS3/CChamber import question, writing, two compile rounds, the checks and this report.
