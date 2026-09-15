# CV-DOM unit U4 — REPORT (2026-09-14, ~03:56 UTC / 11:56pm ET)

Prover: Claude Code subagent (claude-fable-5-1) of the pod executor. Spec: work/drafts/cvdom/DECISION_FINAL.md
§0, §3 (rulings R1–R5; R4 = the positive lift is TIER 1, `CarrierGeometry`) and §5 row **U4**. Nothing under
work/lean was written. Paths relative to the package root
/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912.

## Deliverable

| file | intended home | lines | status |
|---|---|---:|---|
| `work/drafts/cvdom/U4/GeoPositiveLift.lean` | `work/lean/SM/GeoPositiveLift.lean` (new library module, namespace `SM.GeoCarrier`, `open Carrier Link`, CV-free; imports `SM.GeoCornerPolygon` (U2b), `SM.GeoCarrierSelfIntersections` (U2c), `SM.LinkPositiveLift` (accepted positive lift, for the agreement lemmas), `SM.LinkDiagramRecord` (layer module, for `Diagram.record` / `RecordIso`); picked up by the lakefile glob `SM.+`) | 859 | `cd work/lean && lake env lean ../drafts/cvdom/U4/GeoPositiveLift.lean` → **exit 0, no output (no warnings), no `sorry`** (grep count 0); ≈ 6.6 s |

**64 declarations** (6 `def`/`abbrev`: `geoCarrierPolyComp`, `geoCarrierShadow`, `GeoBlockInterior`, `geoPositiveLift`,
`geoToCarrierCrossing`, `geoCarrierCrossingEquiv`; 58 theorems).
`#print axioms` on every one of them (copy of the file with the lines appended, /tmp/U4_axioms.lean, /tmp/u4_gamma.lean):
`[propext, Classical.choice, Quot.sound]` only (standard) on 63; `getElem_congr_of_eq` depends on no axioms. 64/64 standard.

Name safety (ruling R3): each of the 64 names grepped against every declaration head in work/lean (excluding `.lake`):
**zero hits**. No accepted or ported `geo*` name is re-declared. In particular the row modules' lemmas
`SM.geoCornerCount_eq_generic`, `SM.geoCornerPolygon_eq_generic`, `SM.carrierShadow_eq_single_geo`,
`SM.positiveLift_eq_geo` (SM/CS3.lean, row thm:C-S3) and `SM.geoCornerPolygon_tail_off_of_weak` /
`_transverse_of_weak` / `_no_triple_of_weak`, `SM.GeoBlock`, `SM.exists_geoBlock` (SM/CSilent.lean, row prop:C-silent) are
neither imported nor shadowed: the agreement lemmas here carry distinct names (`geoCornerCount_eq_ccpCornerCount`,
`geoCornerPolygon_apply_eq_generic`, `geoCarrierPolyComp_eq_generic`, `geoCarrierShadow_eq_generic`,
`geoPositiveLift_eq_generic`), and the block record is `GeoBlockInterior` (the accepted lane's `BlockInterior` shape),
not CSilent's `GeoBlock`. `recastTuple` (SM/CChamber.lean, row prop:C-chamber) is NOT used: the agreement is recast-free.

Tier hygiene: `Generic P`, `hP.2`, `IsDecomposition`, `independentSupports`, `WeakGeneric` occur only in the header
docstring and in §6 (lines 755–856, the agreement section, which is ABOUT SM-generic polygons). §1–§5 are tier 0/1.

## §5 U4 targets — status (all proved, all at tier 1 as R4 prescribes; no `hW` fallback anywhere)

| §5 target (shape as printed) | draft line | tier | status / note |
|---|---:|:-:|---|
| `abbrev geoCarrierPolyComp (hn) (hG : CarrierGeometry P) (hS) (q) : PolyComp := ⟨geoCornerCount hG.cg S q, three_le_geoCornerCount …, geoCornerPolygon hG.cg S q⟩` | 89 | 1 | **exact**: `⟨geoCornerCount hG.cg S q, three_le_geoCornerCount hn hG hS q, geoCornerPolygon hG.cg S q⟩`; binders `(hn : 3 ≤ n) {P} (hG : CarrierGeometry P) {S} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)` (the U2b/U2c implicitness pattern) |
| `geoCarrierShadow := Shadow.single (geoCarrierPolyComp …)` | 95 | 1 | **exact** |
| `geoCornerPolygon_tail_off` | 454 | **1** | **proved** `(hn) (hG) (hS) (q) (a b) (hab : ¬ incident a b) : Q a ∉ edgeSegment Q b` |
| `geoCornerPolygon_transverse` | 466 | **1** | **proved** `(hn) (hG) (hS) (q) (a b) (hab : ¬ adjacent a b) (hmeet) : det (edge Q a) (edge Q b) ≠ 0` |
| `geoCornerPolygon_no_triple` | 484 | **1** | **proved** `(hn) (hG) (hS) (q) : ¬ ∃ a b c, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ (edgeInterior Q a ∩ edgeInterior Q b ∩ edgeInterior Q c).Nonempty` |
| `geoCarrierShadow_generic : (geoCarrierShadow …).Generic` | 509 | **1** | **proved** via `Shadow.single_generic_of` + U2b `geoCornerPolygon_regular` + the three above |
| `def geoPositiveLift (hn) (hG) (hS) (q) : Diagram := (geoCarrierShadow …).positiveDiagram (geoCarrierShadow_generic …)` | 525 | **1** | **exact** |
| `geoPositiveLift_isPositive` | 546 | 1 | **proved** `(x) : (geoPositiveLift …).IsPositive x`; also `geoPositiveLift_sign … = 1` (550) |
| `geoPositiveLift_componentCount = 1` | 538 | 1 | **proved** (`rfl`); also `geoPositiveLift_Γ` (simp, 535), `geoPositiveLift_comp (i : Fin 1) : ((…).Γ.comp i).P = geoCornerPolygon hG.cg S q` (541) |
| `geoCarrierCrossingEquiv : (geoCarrierShadow …).Crossing ≃ geoCarrierCrossings hG.cg S q` | 696 | 1 | **proved** as `≃ {c // c ∈ geoCarrierCrossings hG.cg S q}` (the accepted `carrierCrossingEquiv`'s subtype form); `_apply` (701), `crossingPoint_geoCarrierCrossingEquiv` (705: the equivalence preserves the crossing point) |
| `geoPositiveLift_writhe : writhe = (geoCarrierCrossings hG.cg S q).card` | 718 | 1 | **proved**, exact shape; plus `geoPositiveLift_writhe_eq_geoCarrierCrossingCount` (723, U2a's `geoCarrierCrossingCount`) and `geoPositiveLift_writhe_eq_card_crossing` (555, `Fintype.card (…).Crossing`) |
| `eq_geoPositiveLift_of_isPositive` | 561 | 1 | **proved** `(D : Diagram) (hD : D.Γ = geoCarrierShadow …) (hpos : ∀ x, D.IsPositive x) : D = geoPositiveLift …` |
| AGREEMENT with the accepted `positiveLift` (task: "in the strongest form you can prove; at least RecordIso") | 818 | — | **proved as literal equality of `Diagram`s** (below), hence records equal (834), `RecordIso` (842), writhes equal (850) |

Nothing left unproved; no obstacle; **no tier-2 need arose** (risk 3 of §7 discharged for the positive lift: `geoPositiveLift`
and hence CV def:piecediagram / lem:piececurve are statable on `CV.Diagrammatic` as printed).

## The exact agreement statement proved

```lean
theorem SM.GeoCarrier.geoPositiveLift_eq_generic {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (hG : CarrierGeometry P) (hS' : GeoIndependent hG.cg S)
    (hS : IsDecomposition hn hP S) (q : GeoComponent hG.cg S) :
    geoPositiveLift hn hG hS' q = positiveLift hn hP S (geoComponentEquivGeneric hn hP S q) hS
```
(`#check` output: `geoPositiveLift hn hG hS' q = positiveLift hn hP S ((geoComponentEquivGeneric hn hP S) q) hS`.)
It holds for ANY tier-1 witness `hG : CarrierGeometry P` and ANY independence proof `hS'` (proof irrelevance identifies
`geoOwner hG.cg S`, `GeoComponent hG.cg S`, `geoCornerPolygon hG.cg S q` with their `generic_crossingGeometry hn hP`
forms, so `q : GeoComponent hG.cg S` is accepted by `e := geoComponentEquivGeneric hn hP S` directly). Specialisation
to the canonical witness (826):
```lean
theorem geoPositiveLift_ofGeneric_eq (hS : IsDecomposition hn hP S) (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoPositiveLift hn (CarrierGeometry.ofGeneric hn hP) ((geoIndependent_iff_isDecomposition hn hP S).mpr hS) q =
      positiveLift hn hP S (geoComponentEquivGeneric hn hP S q) hS
```
Corollaries (all stated with the general `hG`, `hS'`):
- `geoPositiveLift_record_eq_generic` (834): `(geoPositiveLift hn hG hS' q).record = (positiveLift hn hP S (e q) hS).record`;
- `geoPositiveLift_recordIso_generic` (842): `Nonempty (RecordIso (geoPositiveLift hn hG hS' q).record (positiveLift hn hP S (e q) hS).record)`
  — the form `SM.presentations` consumes (`P (geoPositiveLift …) = P (positiveLift …)` is one application of
  `SM.presentations` downstream; not stated here because SM/PolynomialBlock.lean is a row module);
- `geoPositiveLift_writhe_eq_generic` (850).

Proof chain (recast-free; the "one non-`rfl` agreement point" of DECISION_FINAL §7 risk 2):
1. `geoCornerCount_eq_ccpCornerCount` (760): `geoCornerCount hc S q = ccpCornerCount hn hP S (e q)` — `unfold` +
   accepted `geoComponentCornerList_eq_generic` (FlatCarriersDefs).
2. `geoCornerPolygon_apply_eq_generic` (768): `k.val = k'.val → geoCornerPolygon hc S q k = ccpCornerPolygon hn hP S (e q) k'`
   — `geoMarkPosition_eq_generic` + list-index congruence `getElem_congr_of_eq` (67) along the corner-list equality.
3. `geoCarrierPolyComp_eq_generic` (795): `geoCarrierPolyComp hn hG hS' q = carrierPolyComp hn hP S (e q) hS` as `PolyComp`s —
   both are `⟨L.length, _, polyOfList L pos⟩` for their corner lists and position maps (definitionally; `polyOfList` is the
   accepted FlatCarriers §7 abbrev), so `polyComp_polyOfList_congr` (74: `subst` on the list and map equalities; the two
   `NeZero` instances are passed explicitly as `geoCornerCount_neZero` / `ccpCornerCount_neZero`) closes it. This replaces
   CChamber's `recastTuple`/`polyComp_recastTuple` pattern (row module, not importable) by the FlatCarriers `polyOfList`/`subst`
   pattern.
4. `geoCarrierShadow_eq_generic` (809): `congrArg Shadow.single`.
5. `geoPositiveLift_eq_generic` (818): accepted `eq_positiveLift_of_isPositive` with `D := geoPositiveLift …`,
   `hD := geoCarrierShadow_eq_generic`, `hpos := geoPositiveLift_isPositive`.
Also `geoCarrierCrossings_eq_generic` (778): `geoCarrierCrossings hc S q = carrierCrossings hn hP S (e q)` and
`geoCarrierCrossingCount_eq_generic` (787) — the "crossings ↔ geoCarrierCrossings correspondence mirroring the accepted lane"
on the generic side (the U6 half the U2c report left open).

## Ported declarations (source SM/LinkPositiveLift.lean:202-840 → geo name, tier, hand edits)

"verbatim" = the source proof under the renaming `ccpCornerCount/Mark/Polygon → geoCornerCount/Mark/Polygon`,
`smoothingSuccessor hn hP S → geoSmoothingSuccessor hP S`, `smoothingSegment → geoSmoothingSegment`, `owner → geoOwner`,
`Component → GeoComponent`, `carrierCrossings → geoCarrierCrossings`, `ccpOutSlot → geoOutSlot`,
`markPosition hn hP.1 → geoMarkPosition hP`, `IsCarrierParameter → GeoIsCarrierParameter`, `carrierTrace → geoCarrierTrace`,
`IsSelfIntersection → GeoIsSelfIntersection`, `S ∈ independentSupports / IsDecomposition → GeoIndependent`, and the lemma
map `ccpCornerMark_owner → geoOwner_geoCornerMark`, `ccpCornerMark_isTrueCorner → isTrueCorner_geoCornerMark`,
`ccpCornerMark_injective → geoCornerMark_injective` (FlatCarriers, namespace `SM`, args `hP S q`), `ccpCornerPolygon_apply →
geoCornerPolygon_apply`, `ccp_pow_owner → geo_pow_owner`, `ccp_previous_corner → geo_previous_corner`, `ccpCornerMark_exists →
geoCornerMark_exists_of_owner`, `ccpCornerPolygon_block → geoCornerPolygon_block`, `ccpCornerPolygon_edgeSegment →
geoCornerPolygon_edgeSegment`, `ccpCornerPolygon_edge → geoCornerPolygon_edge_smul`, `ccpCornerPolygon_edge_ne_zero →
geoCornerPolygon_edge_ne_zero_of_independent`, `ccpCornerPolygon_regular → geoCornerPolygon_regular`, `ccpCornerCount_ge_three →
three_le_geoCornerCount` (all U2b), `csi_mark_ne_of_param_ne → geoCsi_mark_ne_of_param_ne`, `csi_trace_meet → geoCsi_trace_meet`,
`carrier_selfIntersection_iff → geo_carrier_selfIntersection_iff`, `carrier_selfIntersection_not_corner →
geo_carrier_selfIntersection_not_corner` (no `hn`), `carrier_no_triple_point → geo_carrier_no_triple_point`,
`csi_crossing_edges_det_ne_zero hn hP.1 → geoCsi_crossing_edges_det_ne_zero hP` (all U2c), `smoothingSegment_zero/_glue →
geoSmoothingSegment_zero/_glue` (U1b), `markPosition_evaluation_visit → geoMarkPosition_evaluation_visit`,
`mem_carrierCrossings → mem_geoCarrierCrossings` (U2a). Hypothesis-free source lemmas (`adjacent_of_eq`, `adjacent_of_eq_add_one`,
`adjacent_of_add_one_eq` in `SM.Link`; `ccp_det_smul_smul`, `isTrueCorner_visit`, `visitTwin_*`, `visit_eq_or_twin`,
`crossing_visits_exist` in `SM.Carrier`/`SM`) are shared through `open Carrier Link`, not re-declared. `hn` is kept exactly
where a consumed lemma takes it (`geoCornerPolygon_block hn`, `geoCornerPolygon_edge_ne_zero_of_independent hn`,
`geoCsi_mark_ne_of_param_ne hn`, `geoCsi_trace_meet hn`, `geo_carrier_selfIntersection_iff hn`, `three_le_geoCornerCount hn`) and
on the §5 targets; dropped on the pure `ρ_S`-combinatorics (§2 first half).

### §1 The carrier as a one-component shadow (source 202-233) — tier 1

| source | geo | hand edits |
|---|---|---|
| `carrierPolyComp (hn) (hP) (S) (q) (hS)` | **`geoCarrierPolyComp (hn) (hG) {S} (hS) (q)`** | `ccpCornerCount_ge_three hn hP hS q → three_le_geoCornerCount hn hG hS q` |
| `carrierShadow` | **`geoCarrierShadow`** | verbatim |
| `carrierPolyComp_k/_P`, `carrierShadow_c/_comp` | `geoCarrierPolyComp_k/_P`, `geoCarrierShadow_c/_comp` | `rfl` |

### §2 Block parametrisation (source 237-370) — tier 0, `hP : CrossingGeometry P`

| source | geo | hand edits |
|---|---|---|
| `BlockInterior (hn) (hP) (S) (q) (j) (r)` | **`GeoBlockInterior (hP) (S) (q) (k) (r) : Prop`** | body verbatim (`ccpOutSlot hn hP S → geoOutSlot hP S`) |
| `BlockInterior.mono/.not_trueCorner/.eq_zero_of_trueCorner/.visit_edge` | `GeoBlockInterior.mono/.not_trueCorner/.eq_zero_of_trueCorner/.visit_edge (hP) (S) (q) …` | verbatim; `hn` dropped |
| `isCarrierParameter_block` | `geoIsCarrierParameter_block (hP) (S) (q) (k) (r) (hu0) (hu1)` | `ccp_pow_owner → geo_pow_owner`, `ccpCornerMark_owner → geoOwner_geoCornerMark` |
| `corner_param` | `geo_corner_param (hP) (S) (q) (k)` | `smoothingSegment_zero hn hP S _ → geoSmoothingSegment_zero hP S _` |
| `prevCorner_unique_of_le`, `prevCorner_unique`, `block_mark_eq` | `geo_prevCorner_unique_of_le (hP) (S) …`, `geo_prevCorner_unique`, `geo_block_mark_eq (hP) (S) (q) …` | verbatim (pure `Equiv.Perm` combinatorics); `hn` dropped |
| `edgeSegment_param (hn) (hP) (S) (q) (hS) (j) (hx)` | `geo_edgeSegment_param (hn) (hP) (hS) (q) (k) (hx)` | verbatim (`smoothingSegment_glue → geoSmoothingSegment_glue`) |
| `edgeInterior_param` | `geo_edgeInterior_param (hn) (hP) (hS) (q) (k) (hx)` | verbatim (`ccpCornerPolygon_edge_ne_zero hn hP hS q j → geoCornerPolygon_edge_ne_zero_of_independent hn hP hS q k`) |
| `mark_block` (source 636) | `geo_mark_block (hn) (hP) (hS) (q) (m) (hm)` | verbatim (`ccp_previous_corner hn hP S q → geo_previous_corner hP S q`, `ccpCornerMark_exists hn hP S q a ha hac → geoCornerMark_exists_of_owner hP S q a ha hac`) |

### §3 Corner uniqueness and the meeting lemma (source 372-527) — tier 1, `hG : CarrierGeometry P`

| source | geo | hand edits (the `Generic` sites) |
|---|---|---|
| `param_eq_of_corner` | `geo_param_eq_of_corner (hn) (hG) (hS) (q) {p p'} (hp) (hp') {m} (hm) (hx) (hx')` | `carrier_selfIntersection_iff hn hP hS q → geo_carrier_selfIntersection_iff hn hG hS q`; `carrier_selfIntersection_not_corner hn hP S q hc → geo_carrier_selfIntersection_not_corner hG S q hc` |
| `ccpCornerPolygon_injective` | **`geoCornerPolygon_injective (hn) (hG) (hS) (q) : Function.Injective (geoCornerPolygon hG.cg S q)`** | verbatim |
| `block_param_corner` | `geo_block_param_corner (hn) (hG) (hS) (q) {a b} {r} {u} (hu0) (hu1) (hb) (h) : a = b` | verbatim |
| `nonadjacent_meet` | `geo_nonadjacent_meet (hn) (hG) (hS) (q) {a b} (hab) {x} (hxa) (hxb)` (seven-clause conclusion as in the source) | `csi_mark_ne_of_param_ne hn hP S → geoCsi_mark_ne_of_param_ne hn hG.cg S`; `csi_trace_meet hn hP S → geoCsi_trace_meet hn hG S`; G1 site `independent_selected_pair_owners_ne hn hP hS w → geo_selected_visits_separated hG.cg hS w` (U1a) |
| `nonadjacent_meet_crossing` | `geo_nonadjacent_meet_crossing` | verbatim |

### §4 The four genericity facts and CarrierGeneric (source 529-580) — tier 1

| source | geo | hand edits |
|---|---|---|
| `ccpCornerPolygon_tail_off` | **`geoCornerPolygon_tail_off`** (§5 target) | verbatim |
| `ccpCornerPolygon_transverse` | **`geoCornerPolygon_transverse`** (§5 target) | `ccpCornerPolygon_edge hn hP hS q → geoCornerPolygon_edge_smul hn hG.cg hS q`; G1 site `csi_crossing_edges_det_ne_zero hn hP.1 c → geoCsi_crossing_edges_det_ne_zero hG.cg c` (tier 0, `CrossingGeometry` clause 2) |
| `ccpCornerPolygon_no_triple` | **`geoCornerPolygon_no_triple`** (§5 target) | `carrier_no_triple_point hn hP S q x → geo_carrier_no_triple_point hn hG S q x` |
| `carrierShadow_generic` | **`geoCarrierShadow_generic`** (§5 target) | `ccpCornerPolygon_regular hn hP hS q → geoCornerPolygon_regular hn hG hS q` (U2b, tier 1) |

### §5 The positive lift and its double points (source 582-840) — tier 1

| source | geo | hand edits |
|---|---|---|
| `positiveLift` | **`geoPositiveLift`** (§5 target) | verbatim |
| `positiveLift_Γ`, `_componentCount`, `_comp`, `_isPositive`, `_sign`, `_writhe`, `eq_positiveLift_of_isPositive` | `geoPositiveLift_Γ`, **`geoPositiveLift_componentCount`**, `geoPositiveLift_comp`, **`geoPositiveLift_isPositive`**, `geoPositiveLift_sign`, `geoPositiveLift_writhe_eq_card_crossing`, **`eq_geoPositiveLift_of_isPositive`** | verbatim (`rfl` / `Shadow.positiveDiagram_*`) |
| `exists_carrierCrossing`, `toCarrierCrossing`, `crossingPoint_toCarrierCrossing`, `toCarrierCrossing_injective` | `geo_exists_carrierCrossing`, `geoToCarrierCrossing`, `crossingPoint_geoToCarrierCrossing`, `geoToCarrierCrossing_injective` | verbatim |
| `consecutive_meet (hn) (hP) (S) (q) (hS) (j) (hx) (hx')` — **the source's one tier-2 site** (`ccpCornerPolygon_det_ne_zero`, nonzero turns) | **`geo_consecutive_meet (hn) (hG) (hS) (q) (k) {x} (hx) (hx') : x = Q (k+1)`** | REWRITTEN (ruling R4): `meet_next_eq_corner_of_vertex_off (three_le_geoCornerCount hn hG hS q) (geoCornerPolygon_tail_off hn hG hS q) k hx hx'` — U0's fold-back exclusion applied to the corner polygon `Q` itself, whose `vertex_off` clause is the tier-1 `geoCornerPolygon_tail_off` and whose `3 ≤ k` is the tier-1 `three_le_geoCornerCount`. (Alternative not used: a copy of `regular_adjacent_meet`, SM/CS3.lean:84, from `geoCornerPolygon_regular` — CS3 is a row module.) |
| `carrierCrossing_edges` | `geo_carrierCrossing_edges (hn) (hG) (hS) (q) {c} (hc)` | verbatim (`mark_block → geo_mark_block hn hG.cg hS q`, `markPosition_evaluation_visit → geoMarkPosition_evaluation_visit`, `consecutive_meet → geo_consecutive_meet`) |
| `toCarrierCrossing_surjective` | `geoToCarrierCrossing_surjective` | G1 site `generic_crossingPoint_injective hn hP → crossingPoint_injective_of_geometry hG.cg` |
| `carrierCrossingEquiv`, `_apply`, `crossingPoint_carrierCrossingEquiv` | **`geoCarrierCrossingEquiv`** (§5 target), `geoCarrierCrossingEquiv_apply`, `crossingPoint_geoCarrierCrossingEquiv` | verbatim |
| `card_carrierShadow_crossing`, `positiveLift_writhe_eq_carrierCrossingCount` | `card_geoCarrierShadow_crossing`, **`geoPositiveLift_writhe`** (§5 shape, `.card`), `geoPositiveLift_writhe_eq_geoCarrierCrossingCount` | `carrierCrossingCount → (geoCarrierCrossings hG.cg S q).card` / `geoCarrierCrossingCount hG.cg S q` (U2a, `rfl`) |
| `carrierShadow_crossingPoint`, `positiveLift_isCrossingFreeCircle` | `geoCarrierShadow_crossingPoint`, `geoPositiveLift_isCrossingFreeCircle` | verbatim |

### §0 New helpers (hypothesis-free) and §6 agreement (new, small; see above)

`getElem_congr_of_eq` (67), `polyComp_polyOfList_congr` (74); `geoCornerCount_eq_ccpCornerCount` (760),
`geoCornerPolygon_apply_eq_generic` (768), `geoCarrierCrossings_eq_generic` (778), `geoCarrierCrossingCount_eq_generic` (787),
`geoCarrierPolyComp_eq_generic` (795), `geoCarrierShadow_eq_generic` (809), `geoPositiveLift_eq_generic` (818),
`geoPositiveLift_ofGeneric_eq` (826), `geoPositiveLift_record_eq_generic` (834), `geoPositiveLift_recordIso_generic` (842),
`geoPositiveLift_writhe_eq_generic` (850). The `geoCarrierCrossings` and `PolyComp`/shadow/lift agreement lemmas are the
pieces §5 U6 (SM/GeoCarrierAgreement.lean) lists as `geoCarrierCrossings_eq_generic`, `geoPositiveLift_eq_generic`; U6 can
re-export or skip them. `geoCornerCount_eq_ccpCornerCount` / `geoCornerPolygon_apply_eq_generic` are the recast-free
counterparts of CS3's `geoCornerCount_eq_generic` / `geoCornerPolygon_eq_generic`; if U6 wants the printed
`recastTuple` form it must import CChamber (row module) — or move `recastTuple` to a layer module first.

## Method

1. Read DECISION_FINAL §0/§3/§5/§7, the source SM/LinkPositiveLift.lean in full (845 lines), the U2b and U2c REPORTs and the
   signatures of every U0/U1b/U2a/U2b/U2c lemma consumed, the accepted agreement layer (FlatCarriersDefs §4b, FlatCarriers §7
   `polyOfList`/`generic_corner_props`, `geoIndependent_iff_isDecomposition`), CChamber's recast toolkit (76-110, row module →
   not imported), CS3's GenericIdentification section (1385-1500, row module → not imported; its shapes mirrored under new names),
   CSilent's `GeoBlock`/`_of_weak` group (heads only: the accepted lane's shorter block parametrisation was ported instead),
   `SM.Link` (`PolyComp`, `Shadow`, `Generic`, `Diagram`, `single_*`), `Diagram.record` / `RecordIso.refl`.
2. Hand port on the source text (the file is a straight re-binding; the residue — the four `Generic` sites, the tier-2
   `consecutive_meet`, the `hn` drops, the two-tier binder layout — was done directly). Full explicit binder lists per
   declaration in §1–§4 (the U2b/U2c style); a `variable` block with `include hn hS in` for the two §5 lemmas whose
   statements do not mention `hn`/`hS`.
3. Two compile rounds: round 1 gave the two missing `include`s (unknown `hn`/`hS`) and one `funext` step needing `rw` instead
   of `exact`; round 1b placed `include … in` before the docstrings (parser requirement); round 2: exit 0, no output. Then
   `#print axioms` (64/64 standard), name grep (0 collisions), tier grep, `#check` of the agreement statements.

## Notes for the assembler and downstream units (U3, U6, U7c, U5a)

- **Import graph.** `SM.GeoPositiveLift` imports `SM.GeoCornerPolygon` (U2b), `SM.GeoCarrierSelfIntersections` (U2c),
  `SM.LinkPositiveLift` (accepted layer module, which itself imports the accepted rows `SM.CarriersLemma` and
  `SM.UniformDefinition` — the same dependency the accepted `positiveLift` already carries) and `SM.LinkDiagramRecord`
  (layer module). If the assembler prefers the tier-1 core to be free of `LinkPositiveLift`, §0–§5 (lines 1–753) compile
  with only the first two imports plus `SM.LinkDiagram`; §6 (755–856) is the only consumer of `LinkPositiveLift` /
  `LinkDiagramRecord` and could be split into `SM/GeoCarrierAgreement.lean` (U6's module) unchanged.
- **For U7c (142 def:piecediagram, 143 lem:piececurve, 146 def:X1):** `CV.pieceDiagram H := geoPositiveLift hn
  (CarrierGeometry.ofDiagrammatic hD) hK q_H` with `hK : GeoIndependent _ (S ∪ K_H)` from `CV.mem_Ind_iff_geoIndependent`
  (U0); the 142 bundle's four clauses are `geoPositiveLift_isPositive`, `geoPositiveLift_writhe` (`= (geoCarrierCrossings … q_H).card`,
  which is `(pieceLabels _ S H).card` after 143's `geoCarrierCrossings _ (S ∪ K) q = pieceLabels _ S H`),
  `⟨geoCarrierCrossingEquiv …⟩ : Nonempty (Crossing ≃ {c // c ∈ geoCarrierCrossings …})` (compose with the labels equality),
  `geoPositiveLift_componentCount`. The prototype's `carrierShadow_generic` sorry is `geoCarrierShadow_generic`.
- **For U6 / Bridge:B4 `pointwise`:** `geoPositiveLift_eq_generic hn hP S hG hS' hS q` with `hG := CarrierGeometry.ofGeneric hn hP`
  (or `.ofCV (generic_of_sm hn hP)`) turns `homfly (CV.pieceDiagram …)` on an SM-generic side into `homfly (positiveLift hn hP S
  (e q) hS)` by `congrArg`; `geoCarrierCrossings_eq_generic` gives the label sets; the corner-count/polygon agreement is
  `geoCarrierPolyComp_eq_generic` (PolyComp form) or `geoCornerPolygon_apply_eq_generic` (pointwise form).
- **For U3 (`GeoCarriersLemmaData`, `geoCarrierRotationInt`):** nothing here is needed beyond U2b; `geoCornerPolygon_injective hn hG hS q`
  and `geoCornerPolygon_tail_off` may serve as extra clause-(ii)/(iii) facts.
- **For U5a (path transport of positive lifts):** the lift is determined by its shadow (`eq_geoPositiveLift_of_isPositive`), so
  transporting `geoCornerPolygon` along a `GeoMarkTransport` transports the lift; `geoCarrierShadow_c/_comp` and
  `geoPositiveLift_comp` are the `rfl` access lemmas.
- **Call shapes:** every §1–§5 lemma takes `(hn : 3 ≤ n) {P} (hG : CarrierGeometry P) {S} (hS : GeoIndependent hG.cg S) (q)` in
  that order (tier-0 lemmas: `{P} (hP : CrossingGeometry P) (S) (q)` or `{S} (hS) (q)`, `hn` first where taken); a consumer with
  `hW : WeakGeneric P` passes `hW.carrierGeometry` (proof irrelevance identifies the `CrossingGeometry` proofs, as U2b/U2c note).
- **Time.** ≈ 1.6 h including reading the decision, the source, the U2b/U2c reports and interfaces, the accepted agreement
  layer and the two row modules' shapes, writing, two compile rounds, the checks and this report.
